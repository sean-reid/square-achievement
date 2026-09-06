"""The paper's generated numbers and figures are current."""

import pytest

from squares.paper.claims import PAPER, build_claims, render
from squares.paper.figures import build_figures


@pytest.mark.skipif(
    not (PAPER / "data" / "timings.json").exists(), reason="no recorded timings"
)
def test_claims_file_is_current():
    assert (PAPER / "claims.tex").read_text() == render(build_claims())


def test_figures_are_current():
    for name, text in build_figures().items():
        assert (PAPER / f"{name}.tex").read_text() == text, name
