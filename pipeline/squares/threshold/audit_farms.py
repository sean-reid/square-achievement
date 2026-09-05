"""Audit the table's verified lines for farm-vulnerable block sites.

A forced block by the opponent that creates a counter-threat is safe on
the board it was verified on, but a far pair (o1, o2) aligned with the
block cell would add a second, simultaneous threat on a large enough
board: a double threat the strategy cannot answer. This audit replays
the verification and reports every counter-threat block event with the
cell it happened at, grouped by (o1, o2) branch, plus the alignment
families a far pair would need to hit it.

python3 -m squares.threshold.audit_farms [sizes...], default 6 7; or
python3 -m squares.threshold.audit_farms <n> --o1 r,c to audit the single branch
entered through the first reply (r, c), which makes the class
representatives on the generation board affordable to replay.
"""

import pathlib
import sys
from collections import defaultdict

from ..game import P2, all_squares
from ..verify import verify
from .forcing import box_class, table_strategy
from .tables import build_general


class FarmAudit:
    """Observer for verify: fires at every P1 decision point."""

    def __init__(self, opening=(2, 2)):
        self.opening = opening
        self.events = defaultdict(set)
        self.samples = {}

    def __call__(self, g):
        if len(g.history) < 2:
            return
        reply = g.their_last
        if reply is None or not self._was_block(g, reply):
            return
        counters = g.threats(P2)
        if counters:
            o1 = g.history[1][1]
            o2 = g.history[3][1] if len(g.history) > 3 else None
            self.events[(o1, o2)].add((reply, tuple(counters)))
            self.samples.setdefault((o1, o2, reply), tuple(g.history))

    def _was_block(self, g, reply):
        """The reply completed an opponent square had P1 been allowed it."""
        mine = g.p1
        for square in all_squares(g.n):
            if reply in square:
                missing = square - mine
                if missing == {reply}:
                    return True
        return False


def alignment_families(t, n):
    """The corner pairs a far (o1, o2) must occupy to farm through t.

    A farm square through the box cell t = (a, b) has its other three
    corners determined by a side s and an orientation; the opponent
    needs the two corners that are not the eventual threat cell. Only
    orientations extending down or right leave the board for large s.
    """
    a, b = t
    out = []
    for s in range(7, n - max(a, b)):
        corners = [(a, b + s), (a + s, b), (a + s, b + s)]
        for i in range(3):
            pair = tuple(c for j, c in enumerate(corners) if j != i)
            out.append((s, pair, corners[i]))
    return out


def _tables():
    """The gen-15 tables, cached on disk across audit runs."""
    import pickle

    cache = pathlib.Path("/tmp/sag-gen15.pickle")
    if cache.exists():
        with cache.open("rb") as f:
            return pickle.load(f)
    print("building gen-15 tables...", flush=True)
    tables = build_general(gen_n=15)
    with cache.open("wb") as f:
        pickle.dump(tables, f)
    return tables


def main(sizes, o1=None):
    x2_map, scripts = _tables()
    strategy = table_strategy(x2_map, scripts, classify=box_class)
    for n in sizes:
        audit = FarmAudit()
        opening = ((2, 2), o1) if o1 else ()
        result = verify(strategy, n, opening=opening, observer=audit)
        branches = len(audit.events)
        events = sum(len(v) for v in audit.events.values())
        cells = {t for v in audit.events.values() for (t, _) in v}
        print(
            f"n={n} proven={result.proven}  counter-threat blocks: "
            f"{events} events over {branches} (o1,o2) branches, "
            f"{len(cells)} distinct cells: {sorted(cells)}",
            flush=True,
        )
        for (o1, o2, t), hist in sorted(audit.samples.items()):
            print(f"  sample o1={o1} o2={o2} t={t} plies={len(hist)}")
        if o1 is not None:
            import pickle

            out = pathlib.Path(f"/tmp/sag-samples-{n}-{o1[0]}-{o1[1]}.pickle")
            with out.open("wb") as f:
                pickle.dump(dict(audit.samples), f)
            print(f"  samples -> {out}")


if __name__ == "__main__":
    if "--o1" in sys.argv:
        i = sys.argv.index("--o1")
        cell = tuple(int(v) for v in sys.argv[i + 1].split(","))
        main([int(a) for a in sys.argv[1:i]], o1=cell)
    else:
        main([int(a) for a in sys.argv[1:]] or [6, 7])
