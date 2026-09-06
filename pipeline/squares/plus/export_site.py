"""Export the plus rule's lines as a fixture for the site's TypeScript rule.

The fixture lists, for every reply pair on the 6 board and for a set of
far pairs on larger boards, the second move, the latent corner, the
line as the rule commits to it, and how many of its moves are tempo
moves. The site's unit tests replay their own implementation of the
rule against it, so the three implementations, Lean, Python, and
TypeScript, are compared on the same positions.

python3 -m squares.plus.export_site   writes site/tests/fixtures/plus_lines.json
"""

import json

from ..paths import SITE_PLUS_FIXTURE
from .measure import line_with_key
from .rule import OPENING, abstract_of, second_move
from .sweep import anchors

FAR_PAIRS = [
    ((0, 0), (16, 16)),
    ((16, 16), (0, 0)),
    ((0, 16), (13, 3)),
    ((13, 3), (0, 16)),
    ((0, 17), (14, 3)),
    ((14, 3), (0, 17)),
    ((5, 12), (5, 20)),
    ((12, 5), (20, 5)),
    ((3, 1), (22, 22)),
    ((22, 22), (3, 1)),
    ((1, 3), (9, 9)),
    ((14, 14), (14, 13)),
]


def entry(n, o1, o2, hot=None):
    """One fixture entry: the pair, the second move, the latent corner,
    and the line with its tempo count."""
    x2 = second_move(o1)
    a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
    if hot is not None:
        assert a.hot == hot, (o1, o2, hot, a.hot)
    found = line_with_key(a)
    if found is None:
        raise RuntimeError(f"no line for {o1}, {o2} on the {n} board")
    line, tempo, key = found
    return {
        "n": n,
        "o1": list(o1),
        "o2": list(o2),
        "x2": list(x2),
        "hot": list(a.hot) if a.hot else None,
        "line": [list(c) for c in line],
        "tempo": tempo,
        "side": key[1],
        "centre": list(key[2]),
    }


def build_fixture():
    """Every pair on the 6 board, a sample of far pairs on the 23 board,
    and the anchored positions of the uniform argument."""
    out = []
    cells = [(r, c) for r in range(6) for c in range(6)]
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            out.append(entry(6, o1, o2))
    for o1, o2 in FAR_PAIRS:
        out.append(entry(23, o1, o2))
    for o1, o2, hot in anchors():
        out.append(entry(23, o1, o2, hot))
    return out


def main():
    SITE_PLUS_FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    SITE_PLUS_FIXTURE.write_text(json.dumps(build_fixture(), separators=(",", ":")) + "\n")
    print(f"wrote {SITE_PLUS_FIXTURE}")


if __name__ == "__main__":
    main()
