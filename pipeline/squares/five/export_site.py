"""Export the 5 x 5 strategy table as the site's five.json.

The interactive page replays the same tables the checker verifies, so
the export must be bit-exact: cell keys as "r,c", alignment classes as
"row:r" and "col:c", farm keys as "farm:a,b", the default as "*", and
branch points as {"q": move, "b": branches}.

python3 -m squares.five.export_site [dir], default the site's game
directory. The two tables are separate files so the page loads only
the one a board size needs.
"""

import json
import pathlib
import sys

from ..paths import SITE_GAME
from . import strategy5


def key_str(k):
    if k is None:
        return "*"
    if isinstance(k[0], int):
        return f"{k[0]},{k[1]}"
    kind, v = k
    if kind == "farm":
        return f"farm:{v[0]},{v[1]}"
    return f"{kind}:{v}"


def entry_json(entry):
    if entry and entry[0] == "q":
        _, move, table = entry
        return {
            "q": list(move),
            "b": {key_str(k): entry_json(v) for k, v in table.items()},
        }
    return [list(c) for c in entry]


def table_json(opening, box, x2, scripts):
    return {
        "opening": list(opening),
        "box": box,
        "x2": {key_str(k): list(v) for k, v in x2.items()},
        "scripts": {
            key_str(k): {key_str(k2): entry_json(v2) for k2, v2 in tab.items()}
            for k, tab in scripts.items()
        },
    }


def main():
    out = {"five": table_json((2, 2), 5, strategy5.X2, strategy5.SCRIPTS)}
    directory = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else SITE_GAME
    for name, table in out.items():
        path = directory / f"{name}.json"
        path.write_text(json.dumps(table, separators=(",", ":")) + "\n")
        print(f"wrote {path}")


if __name__ == "__main__":
    main()
