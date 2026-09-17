"""Cross-check the plus rule against the lines the Lean rule commits to.

`lake exe checker lines` prints, for every reply pair of the 6 x 6 board
and for every anchored position of the uniform argument, the line the
Lean rule commits to on its abstraction. This module computes the
Python rule's line for each printed position and reports every
position where the two disagree, including the second move and the
hidden corner.

python3 -m squares.plus.crosscheck [lines.txt] exits nonzero on any
mismatch; without a path it runs the Lean checker in the formalization.
"""

import pathlib
import subprocess
import sys

from ..paths import FORMALIZATION
from .rule import OPENING, abstract_of, best_line, second_move
from .sweep import anchors


def _cells(fields):
    return [(int(fields[i]), int(fields[i + 1])) for i in range(0, len(fields), 2)]


def parse_lines(text):
    """{(tag, o1, o2): (x2, hot, line)} from the checker's output; tag is
    "6" or "anchor", hot the hidden corner the Lean rule read."""
    out = {}
    for raw in text.splitlines():
        head, _, tail = raw.partition(" : ")
        fields = head.split()
        tag, fields = fields[0], fields[1:]
        hot = None
        if tag == "anchor":
            if fields[0] != "-":
                hot = (int(fields[0]), int(fields[1]))
            fields = fields[2:]
        o1, o2, x2 = _cells(fields)
        line = None if tail.strip() == "none" else _cells(tail.split())
        out[(tag, o1, o2)] = (x2, hot, line)
    return out


def python_line(o1, o2):
    """(x2, hot, line) of the Python rule after the reply pair."""
    x2 = second_move(o1)
    a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
    return x2, a.hot, best_line(a)


def expected_positions():
    """{(tag, o1, o2): hot} for the positions the checker prints."""
    cells = [(r, c) for r in range(6) for c in range(6)]
    out = {}
    for o1 in cells:
        if o1 == OPENING:
            continue
        for o2 in cells:
            if o2 not in (OPENING, o1, second_move(o1)):
                out[("6", o1, o2)] = None
    for o1, o2, hot in anchors():
        out[("anchor", o1, o2)] = hot
    return out


def mismatches(text):
    """Every disagreement between the checker's output and the Python rule."""
    lean = parse_lines(text)
    expected = expected_positions()
    out = [("missing", key) for key in expected if key not in lean]
    out += [("unexpected", key) for key in lean if key not in expected]
    for key, (x2, hot, line) in lean.items():
        if key not in expected:
            continue
        if key[0] == "anchor" and hot != expected[key]:
            out.append(("hidden corner", key, hot, expected[key]))
        ours = python_line(key[1], key[2])
        if ours != (x2, hot, line):
            out.append(("line", key, (x2, hot, line), ours))
    return out


def lean_lines():
    """The checker's output, from a build of the formalization."""
    run = subprocess.run(
        ["lake", "exe", "checker", "lines"],
        cwd=FORMALIZATION,
        check=True,
        capture_output=True,
        text=True,
    )
    return run.stdout


def main():
    text = pathlib.Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else lean_lines()
    bad = mismatches(text)
    for item in bad:
        print("mismatch:", *item)
    if bad:
        sys.exit(1)
    print(f"the Python rule agrees with the Lean rule on {len(parse_lines(text))} positions")


if __name__ == "__main__":
    main()
