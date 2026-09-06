"""Measure the plus rule's lines on each board.

For every reply pair on the n board the rule commits to a line: some
tempo moves, then the arms of a plus. Against an opponent who blocks,
each move is answered by its block until a move makes two threats; one
more block and the completion follow. If the double threat comes at the
j-th move of the line, the win is the (2j + 5)-th ply of the game. This
module reports, per board, the number of roots, the number of distinct
lines as played, the latest winning ply, and how the lines split by
tempo moves and plus side.

python3 -m squares.plus.measure [n_min [n_max]]   default 6 to 17.
"""

import sys
import time
from collections import Counter

from .rule import (
    DEPTH,
    OPENING,
    abstract_of,
    my_threats,
    second_move,
    tempo_moves,
    their_threats,
    winning_pluses,
)


def line_with_key(a):
    """The rule's line as best_line finds it, with the number of tempo
    moves in front of the plus and the plus key (arms left, side, centre)."""
    frontier = [(a, [])]
    for d in range(DEPTH + 1):
        best = None
        for b, pre in frontier:
            if their_threats(b.p2, b.p1 + b.p2):
                continue
            pl = winning_pluses(b)
            if pl:
                key, order = pl[0]
                if best is None or key < best[0]:
                    best = (key, pre + order)
        if best is not None:
            return best[1], d, best[0]
        if d == DEPTH:
            return None
        frontier = [(b2, pre + [m]) for b, pre in frontier for m, b2 in tempo_moves(b)]
        if not frontier:
            return None
    return None


def played(a, line):
    """The prefix of the line actually played against an opponent who
    blocks: the moves up to and including the one making two threats."""
    p1, p2 = list(a.p1), list(a.p2)
    for j, m in enumerate(line, start=1):
        p1 = [m] + p1
        mine = my_threats(p1, p1 + p2)
        if len(mine) >= 2:
            return line[:j]
        p2 = [mine[0]] + p2
    raise RuntimeError(f"line {line} never makes two threats")


def measure(n):
    """Statistics of the rule's lines over every reply pair on the n board."""
    cells = [(r, c) for r in range(n) for c in range(n)]
    roots, lines, tempo, sides, longest = 0, set(), Counter(), Counter(), None
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            roots += 1
            a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
            found = line_with_key(a)
            if found is None:
                raise RuntimeError(f"no line for {o1}, {o2} on the {n} board")
            line, d, key = found
            line = played(a, line)
            lines.add(tuple(line))
            tempo[d] += 1
            sides[key[1]] += 1
            if longest is None or len(line) > len(longest[2]):
                longest = (o1, o2, line)
    return {
        "n": n,
        "roots": roots,
        "lines": len(lines),
        "max_plies": 2 * len(longest[2]) + 5,
        "tempo": dict(sorted(tempo.items())),
        "sides": dict(sorted(sides.items())),
        "longest": longest,
    }


if __name__ == "__main__":
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 17
    for n in range(lo, hi + 1):
        t0 = time.time()
        m = measure(n)
        print(
            f"n={m['n']}: roots={m['roots']} lines={m['lines']} max_plies={m['max_plies']} "
            f"tempo={m['tempo']} sides={m['sides']} ({time.time() - t0:.0f}s)"
        )
        o1, o2, line = m["longest"]
        print(f"  longest: o1={o1} o2={o2} line={line}")
        sys.stdout.flush()
