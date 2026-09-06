"""Strategy-table extraction for the 5 x 5 board.

python3 -m squares.five.tables regenerates strategy5.py, a complete
lookup strategy for the 5x5 board verified exhaustively after
generation, and prints the number of positions the solver visited.
python3 -m squares.five.tables general generates the corner-box
table for every board from 6 up and verifies it with the reference
verifier at the given sizes (default 6, 7, 8); the exporters write the
shipped copies.

The extractor turns solved positions into table entries: a pure
forcing script where one exists, otherwise a solver-chosen move with a
fork over every reply.
"""

from ..solver import Solver, forcing_bits


def _merge_default(table):
    """Replace the most common entry with a None default."""
    if not table:
        return table
    counts = {}
    for entry in table.values():
        key = repr(entry)
        counts[key] = counts.get(key, 0) + 1
    common = max(counts, key=counts.get)
    if counts[common] < 2:
        return table
    out = {k: v for k, v in table.items() if repr(v) != common}
    out[None] = next(v for v in table.values() if repr(v) == common)
    return out


def _extract(solver, p1, p2, budget, memo=None):
    """A table entry winning the position under reflex semantics.

    Plan tuples may include cells the reflexes end up playing; resolve
    skips cells already held, so that is harmless.
    """
    if memo is None:
        memo = solver.extract_memo = getattr(solver, "extract_memo", {})
    key = (p1, p2)
    cached = memo.get(key)
    if cached is not None:
        return cached
    if solver.threat_bits(p1, p2):
        memo[key] = ()
        return ()
    blocks = solver.threat_bits(p2, p1)
    if blocks:
        if blocks.bit_count() > 1:
            raise ValueError("position is lost")
        move_bit = blocks  # the block reflex plays this
    else:
        script = forcing_bits(solver, p1, p2, budget)
        if script is not None:
            memo[key] = script
            return script
        move_bit = solver.winning_bit(p1, p2)
        if move_bit is None:
            raise ValueError("position is not a P1 win")
    move = solver.cell(move_bit)
    mine = solver.threat_bits(p1 | move_bit, p2)
    count = mine.bit_count()
    if count >= 2:
        entry = (move,)  # any reply, the win reflex finishes
    elif count == 1:
        cont = _extract(solver, p1 | move_bit, p2 | mine, budget, memo)
        if cont and cont[0] == "q":
            entry = ("q", move, {solver.cell(mine): cont, None: ()})
        else:
            entry = (move,) + cont
    else:
        table = {}
        free = solver.full & ~p1 & ~p2 & ~move_bit
        while free:
            low = free & -free
            free ^= low
            table[solver.cell(low)] = _extract(solver, p1 | move_bit, p2 | low, budget, memo)
        entry = ("q", move, _merge_default(table))
    memo[key] = entry
    return entry


def build_tables(
    n=5, opening=(2, 2), progress=None, exact=True, box=None, plan_box=None, solver=None
):
    """Generate (x2_map, scripts, gaps) for o1 inside the box.

    With exact=True, hard pairs go through the exact solver and gaps
    stays empty. With exact=False only the forcing search runs, and
    pairs it cannot win land in gaps as (o1, x2, o2). plan_box confines
    P1's plan region so scripts stay valid on every board that size up.
    A caller that passes its own solver can read its memo afterwards.
    """
    if solver is None:
        solver = Solver(n, box=plan_box)
    x2_candidates = [(3, 2), (2, 3), (1, 2), (2, 1), (3, 3), (1, 1), (3, 1), (1, 3)]
    o1_cells = [(r, c) for r in range(min(n, box or n)) for c in range(min(n, box or n))]
    o2_cells = [(r, c) for r in range(n) for c in range(n)]
    x2_map, scripts, gaps = {}, {}, []
    for o1 in o1_cells:
        if o1 == opening:
            continue
        options = [x2 for x2 in x2_candidates if x2 != o1]
        if exact:
            solver_bit = solver.winning_bit(solver.bit(opening), solver.bit(o1))
            if solver_bit is None:
                raise ValueError(f"o1 {o1} refutes the opening")
            fallback = solver.cell(solver_bit)
            if fallback not in options:
                options.append(fallback)
        best = None
        for x2 in options:
            base1 = solver.bit(opening) | solver.bit(x2)
            base2 = solver.bit(o1)
            table, pure, missing = {}, 0, []
            try:
                for o2 in o2_cells:
                    if o2 in (opening, o1, x2):
                        continue
                    p1b, p2b = base1, base2 | solver.bit(o2)
                    script = forcing_bits(solver, p1b, p2b, 8)
                    if script is not None:
                        table[o2] = script
                        pure += 1
                    elif exact:
                        table[o2] = _extract(solver, p1b, p2b, 8)
                    else:
                        missing.append(o2)
            except ValueError:
                continue  # this x2 loses somewhere
            if best is None or pure > best[0]:
                best = (pure, x2, table, missing)
            if not missing and pure == len(table):
                break
        if best is None:
            raise ValueError(f"no winning x2 found for o1 {o1}")
        pure, x2, table, missing = best
        x2_map[o1] = x2
        scripts[o1] = _merge_default(table)
        gaps.extend((o1, x2, o2) for o2 in missing)
        if progress:
            progress(f"o1 {o1}: x2 {x2}, {pure} pure, {len(missing)} gaps")
    return x2_map, scripts, gaps


def main():
    import pprint

    solver = Solver(5)
    x2_map, scripts, gaps = build_tables(progress=print, solver=solver)
    assert not gaps
    print(f"positions solved: {len(solver.memo)}")
    body = (
        '"""A complete P1 strategy for the 5x5 board.\n\n'
        "Generated by python3 -m squares.five.tables; regenerate rather\n"
        "than edit.\n"
        "x1 is (2,2); X2 picks the second move per o1; SCRIPTS maps (o1, o2)\n"
        "to the entry that follows, with None as the default key and\n"
        '("q", move, table) marking a move that forks on its reply.\n'
        '"""\n\n'
        "from .forcing import table_strategy\n\n"
        f"X2 = {pprint.pformat(x2_map, width=100)}\n\n"
        f"SCRIPTS = {pprint.pformat(scripts, width=100)}\n\n"
        "strategy5 = table_strategy(X2, SCRIPTS)\n"
    )
    import pathlib

    path = pathlib.Path(__file__).with_name("strategy5.py")
    path.write_text(body)
    print(f"wrote {path}")

    from ..verify import verify
    from . import strategy5

    result = verify(strategy5.strategy5, 5)
    print(result.report().splitlines()[0])


if __name__ == "__main__":
    main()
