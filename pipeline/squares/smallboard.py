"""Exact drawing policies for the boards below n = 5.

P1 cannot win there, but must not lose either; a reflex-only player
falls to a two-threat fork. The policy at every quiet node is the
lex-least move from which P1 still cannot be beaten, with wins and
single-threat blocks left to the reflexes (both are forced, so the
table stores only the quiet choices). The walk that extracts the table
visits every second-player reply sequence, so extraction doubles as
exhaustive verification that the policy never loses.

python3 -m squares.smallboard [path] regenerates the JSON consumed by
the site's bot, keyed by "p1,p2" stone bitmasks (row-major bits); the
default path is the site's small_tables.json.
"""

import json
import pathlib
import sys

from .paths import SITE_SMALL_TABLES
from .solver import Solver


def safe(solver, p1, p2, p1_to_move, memo):
    """True if P1 is not beaten from here, draws counting for P1."""
    key = (p1, p2, p1_to_move)
    cached = memo.get(key)
    if cached is not None:
        return cached
    mine, theirs = (p1, p2) if p1_to_move else (p2, p1)
    if solver.threat_bits(mine, theirs):
        memo[key] = p1_to_move
        return p1_to_move
    free = solver.full & ~p1 & ~p2
    if not free:
        memo[key] = True
        return True
    opp = solver.threat_bits(theirs, mine)
    if opp.bit_count() >= 2:
        memo[key] = not p1_to_move
        return not p1_to_move
    moves = [opp] if opp else _low_bits(free)
    if p1_to_move:
        out = any(safe(solver, p1 | low, p2, False, memo) for low in moves)
    else:
        out = all(safe(solver, p1, p2 | low, True, memo) for low in moves)
    memo[key] = out
    return out


def _low_bits(bits):
    out = []
    while bits:
        low = bits & -bits
        bits ^= low
        out.append(low)
    return out


def draw_policy(n):
    """The quiet-node policy table for the n x n board.

    Raises if any reachable position has no safe move, so a successful
    return is the proof that the policy never loses.
    """
    solver = Solver(n)
    memo = {}
    if not safe(solver, 0, 0, True, memo):
        raise ValueError(f"P1 can be beaten from the empty {n} x {n} board")
    table = {}
    seen = set()

    def visit(p1, p2):
        if (p1, p2) in seen or (p1 | p2) == solver.full:
            return
        seen.add((p1, p2))
        if solver.threat_bits(p1, p2):
            return  # the win reflex ends the game
        blocks = solver.threat_bits(p2, p1)
        if blocks:
            move = blocks  # forced, the block reflex plays it
        else:
            move = next(
                low
                for low in _low_bits(solver.full & ~p1 & ~p2)
                if safe(solver, p1 | low, p2, False, memo)
            )
            table[(p1, p2)] = move
        p1_after = p1 | move
        free = solver.full & ~p1_after & ~p2
        if not free:
            return
        for reply in _low_bits(free):
            visit(p1_after, p2 | reply)

    visit(0, 0)
    return table


def main():
    out = {}
    for n in (2, 3, 4):
        table = draw_policy(n)
        cells = {
            f"{p1},{p2}": divmod(move.bit_length() - 1, n) for (p1, p2), move in table.items()
        }
        out[str(n)] = cells
        print(f"n={n}: {len(cells)} quiet entries")
    path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else SITE_SMALL_TABLES
    path.write_text(json.dumps(out, separators=(",", ":")) + "\n")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
