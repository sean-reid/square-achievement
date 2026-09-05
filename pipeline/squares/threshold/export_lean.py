"""Export strategy tables as Lean data files.

python3 -m squares.threshold.export_lean [data-dir] writes Data/TableGen.lean
(the general table, regenerated) and Data/Table5.lean (the n=5 table
with quiet forks) into the Lean project's Data directory, by default
the formalization next to this pipeline in the repository.
"""

import pathlib
import sys

from ..paths import LEAN_DATA


def key_lean(k):
    if k is None:
        return "Key.dflt"
    if isinstance(k[0], int):
        return f"Key.cell ({k[0]}, {k[1]})"
    if k[0] == "row":
        return f"Key.row {k[1]}"
    if k[0] == "col":
        return f"Key.col {k[1]}"
    return f"Key.farm ({k[1][0]}, {k[1][1]})"


def entry_lean(e):
    if e and e[0] == "q":
        _, move, table = e
        branches = ", ".join(f"({key_lean(k)}, {entry_lean(v)})" for k, v in table.items())
        return f"Entry.quiet ({move[0]}, {move[1]}) [{branches}]"
    cells = ", ".join(f"({r}, {c})" for r, c in e)
    return f"Entry.plan [{cells}]"


def emit(name, defname, opening, box, x2_map, scripts, out_dir, chunk=4):
    lines = [
        "import SquareAchievement.Compute.Table",
        "",
        "/-! Machine-generated strategy table; regenerate with the table",
        "pipeline rather than edit. -/",
        "",
        "set_option maxHeartbeats 1000000",
        "set_option maxRecDepth 8192",
        "",
        "namespace SquareAchievement",
        "",
        f"def {defname}X2 : List (Key × Cell) := [",
    ]
    lines += [f"  ({key_lean(k)}, ({v[0]}, {v[1]}))," for k, v in x2_map.items()]
    lines += ["]", ""]
    entries = [
        f"  ({key_lean(k)}, ["
        + ", ".join(f"({key_lean(k2)}, {entry_lean(p)})" for k2, p in table.items())
        + "]),"
        for k, table in scripts.items()
    ]
    chunks = [entries[i : i + chunk] for i in range(0, len(entries), chunk)]
    for i, ch in enumerate(chunks):
        lines.append(f"def {defname}Scripts_{i} : List (Key × List (Key × Entry)) := [")
        lines += ch
        lines += ["]", ""]
    joined = " ++ ".join(f"{defname}Scripts_{i}" for i in range(len(chunks)))
    lines += [
        f"def {defname}Scripts : List (Key × List (Key × Entry)) := {joined}",
        "",
        f"def {defname}Table : Table :=",
        f"  ⟨({opening[0]}, {opening[1]}), {box}, {defname}X2, {defname}Scripts⟩",
        "",
        "end SquareAchievement",
    ]
    path = out_dir / name
    path.write_text("\n".join(lines) + "\n")
    print(f"wrote {path} ({len(chunks)} chunks)")


def as_entries(scripts):
    """Normalize plan tuples so every value is entry-shaped."""
    return {k: {k2: v2 for k2, v2 in table.items()} for k, table in scripts.items()}


def main():
    from . import strategy5
    from .tables import build_general

    out_dir = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else LEAN_DATA
    x2_map, scripts = build_general()
    emit("TableGen.lean", "gen", (2, 2), 6, x2_map, as_entries(scripts), out_dir)
    emit("Table5.lean", "five", (2, 2), 5, strategy5.X2, as_entries(strategy5.SCRIPTS), out_dir)


if __name__ == "__main__":
    main()
