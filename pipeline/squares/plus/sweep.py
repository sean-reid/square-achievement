"""Sweep every opening on a board with the plus rule under forcing
semantics, and replay the anchored far-pair positions of the uniform
argument with the latent corner as a guard.

python3 -m squares.plus.sweep [n]   sweeps the n board, default 15.
"""

import sys
import time

from .rule import BASE, BOX, OPENING, Abs, abstract_of, best_line, second_move

ANCHOR_BOARD = 23


def sweep(n):
    """(openings, failures) of the rule over all reply pairs on the n board."""
    cells = [(r, c) for r in range(n) for c in range(n)]
    total, fails = 0, []
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            total += 1
            if best_line(abstract_of([OPENING, x2], [o1, o2], o1, o2)) is None:
                fails.append((o1, x2, o2))
    return total, fails


def anchors():
    """The anchored positions of the uniform argument: both replies far,
    a near aligned first reply, and a near aligned second reply."""
    out = []
    for h1 in range(BOX):
        for h2 in range(BOX):
            out.append(((h1 + 17, h2 + 17), (h1 + 17, h2), (h1, h2)))
    for a in range(BOX):
        for w in range(2 * BOX, BASE):
            for h in range(BOX):
                if 17 <= a + w - h:
                    out.append(((a, w), (a + w - h, w), (a, h)))
                    out.append(((w, a), (w, a + w - h), (h, a)))
                    out.append(((a + w - h, w), (a, w), (a, h)))
                    out.append(((w, a + w - h), (w, a), (h, a)))
    return out


def anchors_safe():
    """Anchored positions where the rule has no line respecting the guard."""
    fails = []
    for o1, o2, hot in anchors():
        x2 = second_move(o1)
        a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
        if a.hot != hot:
            fails.append(("key", o1, o2, hot, a.hot))
        elif best_line(Abs(a.p1, a.p2, hot)) is None:
            fails.append(("line", o1, o2, hot))
    return fails


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    t0 = time.time()
    total, fails = sweep(n)
    print(f"n={n}: {total} openings, {len(fails)} without a line ({time.time() - t0:.0f}s)")
    for f in fails[:20]:
        print("  ", f)
    bad = anchors_safe()
    print(f"anchored positions: {len(anchors())}, unsafe {len(bad)}")
