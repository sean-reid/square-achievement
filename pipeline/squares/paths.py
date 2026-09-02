"""Repository paths shared by the exporters."""

import pathlib

REPO = pathlib.Path(__file__).resolve().parents[2]
SITE_TABLES = REPO / "site/src/game/tables.json"
SITE_SMALL_TABLES = REPO / "site/src/game/small_tables.json"
LEAN_DATA = REPO / "formalization/SquareAchievement/Data"
