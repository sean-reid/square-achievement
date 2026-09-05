"""Export the strategy tables as the site's tables.json.

The interactive page replays the same tables the checker verifies, so
the export must be bit-exact: cell keys as "r,c", alignment classes as
"row:r" and "col:c", farm keys as "farm:a,b", the default as "*", and
quiet forks as {"q": move, "b": branches}.

python3 -m squares.threshold.export_site [path], default the site's tables.json.
"""

import json
import pathlib
import sys

from ..paths import SITE_TABLES
from . import strategy5
from .tables import build_general


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
    x2_map, scripts = build_general()
    out = {
        "general": table_json((2, 2), 6, x2_map, scripts),
        "five": table_json((2, 2), 5, strategy5.X2, strategy5.SCRIPTS),
    }
    path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else SITE_TABLES
    path.write_text(json.dumps(out, separators=(",", ":")) + "\n")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
