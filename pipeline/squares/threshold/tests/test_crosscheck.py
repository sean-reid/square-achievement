"""The Lean data file, the site JSON, and the Python module agree."""

import json

from squares.paths import LEAN_DATA, SITE_FIVE_TABLE
from squares.threshold import strategy5
from squares.threshold.crosscheck import read_lean_table
from squares.threshold.export_site import table_json


def test_lean_five_table_matches_site_and_python():
    site = json.loads(SITE_FIVE_TABLE.read_text())
    lean = table_json(*read_lean_table(LEAN_DATA / "Table5.lean"))
    assert lean == site
    assert lean == table_json((2, 2), 5, strategy5.X2, strategy5.SCRIPTS)


def test_read_lean_table_shapes():
    opening, box, x2, scripts = read_lean_table(LEAN_DATA / "Table5.lean")
    assert (opening, box) == ((2, 2), 5)
    assert len(x2) == 24
    entries = [v for t in scripts.values() for v in t.values()]
    assert all(isinstance(v, tuple) or v[0] == "q" for v in entries)
