"""Record the certificate run times in paper/data/timings.json.

Runs the compiled Lean checker once per board from 5 to 17, on the
anchor board 23, and on the anchored families, and stores the reported
milliseconds as seconds. Needs a built formalization (lake build
checker). Takes about a quarter of an hour, most of it the 23 board.

python3 -m squares.paper.timings
"""

import json
import re
import subprocess

from ..paths import REPO

FORMALIZATION = REPO / "formalization"
BOARDS = list(range(5, 18)) + [23]


def run(*args):
    """The checker's reported milliseconds for the given arguments."""
    out = subprocess.run(
        ["lake", "exe", "checker", *args], cwd=FORMALIZATION, capture_output=True, text=True
    ).stdout
    match = re.search(r"\((\d+)ms", out)
    if not match:
        raise RuntimeError(f"no time in checker output: {out!r}")
    return int(match.group(1)) / 1000


def main():
    timings = {str(n): run(str(n)) for n in BOARDS}
    timings["anchored"] = run("anchors")
    path = REPO / "paper" / "data" / "timings.json"
    path.write_text(json.dumps(timings, indent=2) + "\n")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
