"""Repository paths shared by the exporters."""

import pathlib

REPO = pathlib.Path(__file__).resolve().parents[2]
SITE_GAME = REPO / "site/src/game"
SITE_FIVE_TABLE = SITE_GAME / "five.json"
SITE_SMALL_TABLES = SITE_GAME / "small_tables.json"
SITE_PLUS_FIXTURE = REPO / "site/tests/fixtures/plus_lines.json"
LEAN_DATA = REPO / "formalization/SquareAchievement/Five"
