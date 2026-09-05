"""Measure the geometry the general strategy touches during verification.

The subsumption argument needs the frame every P1 decision fits in:
where P1's moves land by decision kind, how far the corners of the
squares justifying a reflex reach, and which table keys resolve
exactly rather than through an alignment class. This runs the
exhaustive verifier with a metering strategy and prints the maxima per
board size; a constant frame across growing n is the empirical footing
for choosing N0.

Usage: python3 -m squares.threshold.instrument [sizes...], default 6 7 8 9.
"""

import sys

from ..game import P1, P2, all_squares
from ..verify import verify
from .forcing import box_class, table_strategy
from .tables import build_general

BOX = 6


class Meter:
    def __init__(self):
        self.move_max = {}
        self.move_count = {}
        self.quiet_table_moves = 0
        self.reflex_corner_max = -1
        self.far_squares = 0
        self.exact_key_max = -1
        self.classes = set()
        self.default_keys = 0

    def move(self, g, kind, cell):
        self.move_max[kind] = max(self.move_max.get(kind, -1), max(cell))
        self.move_count[kind] = self.move_count.get(kind, 0) + 1
        if kind in ("opening", "x2", "plan") and not self._threatens(g, cell):
            self.quiet_table_moves += 1
        if kind in ("win", "block"):
            player = P1 if kind == "win" else P2
            stones = g.stones(player)
            for square in all_squares(g.n):
                if square - stones == {cell}:
                    reach = max(max(c) for c in square)
                    self.reflex_corner_max = max(self.reflex_corner_max, reach)
                    if all(max(c) >= BOX for c in square):
                        self.far_squares += 1

    def _threatens(self, g, cell):
        """Playing cell gives P1 three corners of a square, fourth empty."""
        stones = g.stones(P1) | {cell}
        for square in all_squares(g.n):
            if cell in square:
                missing = square - stones
                if len(missing) == 1 and not g.occupied(next(iter(missing))):
                    return True
        return False

    def key(self, cell, kind):
        if kind == "exact":
            self.exact_key_max = max(self.exact_key_max, max(cell))
        elif kind == "class":
            self.classes.add(box_class(cell))
        else:
            self.default_keys += 1

    def report(self):
        moves = " ".join(
            f"{k}={self.move_max.get(k, -1)}/{self.move_count.get(k, 0)}"
            for k in ("opening", "x2", "plan", "win", "block")
        )
        return (
            f"moves[max-coord/count]: {moves}  reflex-corner-max={self.reflex_corner_max}"
            f"  far-squares={self.far_squares}  exact-key-max={self.exact_key_max}"
            f"  classes={len(self.classes)}  default-keys={self.default_keys}"
            f"  quiet-table-moves={self.quiet_table_moves}"
        )


def main(sizes):
    print("building gen-15 tables...", flush=True)
    x2_map, scripts = build_general(gen_n=15)
    for n in sizes:
        meter = Meter()
        strategy = table_strategy(x2_map, scripts, classify=box_class, meter=meter)
        result = verify(strategy, n)
        print(f"n={n} proven={result.proven}  {meter.report()}", flush=True)
        if not result.proven:
            print(result.report())
            return


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [6, 7, 8, 9])
