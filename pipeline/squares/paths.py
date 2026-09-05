"""Repository paths shared by the exporters."""

import pathlib

REPO = pathlib.Path(__file__).resolve().parents[2]
SITE_GAME = REPO / "site/src/game"
SITE_FIVE_TABLE = SITE_GAME / "five.json"
SITE_GENERAL_TABLE = SITE_GAME / "general.json"
SITE_SMALL_TABLES = SITE_GAME / "small_tables.json"
LEAN_DATA = REPO / "formalization/Threshold/Data"
