"""Probe whether hot-cell pruning leaves the forcing search a way out.

The v2 table must avoid, per far branch, forced blocks that both land
on the branch's farm-aligned cells and create a counter-threat. This
probes the row-a representative branches on the generation board: with
the whole box row a marked hot (the strict union over refined
branches), does every (o1, o2) pair still get an all-forcing script?

python3 -m squares.threshold.probe_hot [gen_n], default 15.
"""

import sys

from ..solver import Solver, forcing_bits

OPENING = (2, 2)
X2_CANDIDATES = [(3, 2), (2, 3), (1, 2), (2, 1), (3, 3), (1, 1), (3, 1), (1, 3)]


def probe_branch(n, o1, hot_cells):
    solver = Solver(n, box=6)
    solver.hot_mask = sum(solver.bit(c) for c in hot_cells)
    o2_cells = [(r, c) for r in range(n) for c in range(n)]
    best = None
    for x2 in X2_CANDIDATES:
        if x2 == o1:
            continue
        base1 = solver.bit(OPENING) | solver.bit(x2)
        base2 = solver.bit(o1)
        pure, missing = 0, []
        for o2 in o2_cells:
            if o2 in (OPENING, o1, x2):
                continue
            script = forcing_bits(solver, base1, base2 | solver.bit(o2), 8)
            if script is not None:
                pure += 1
            else:
                missing.append(o2)
        if best is None or len(missing) < len(best[1]):
            best = (x2, missing, pure)
        if not missing:
            break
    x2, missing, pure = best
    return x2, pure, missing


def main(gen_n):
    for a in range(6):
        o1 = (a, gen_n - 1)
        hot = [(a, b) for b in range(6)]
        x2, pure, missing = probe_branch(gen_n, o1, hot)
        head = (
            f"row-{a} rep {o1} hot={hot[0]}..{hot[-1]}: x2={x2} pure={pure} gaps={len(missing)}"
        )
        if missing:
            head += f" first={missing[:4]}"
        print(head, flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 15)
