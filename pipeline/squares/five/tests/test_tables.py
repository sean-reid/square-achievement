"""Claims the paper makes about the 5 x 5 table generation."""

from squares.five.tables import build_tables


def test_twenty_openings_on_five_have_no_forcing_win():
    # the paper: pure forcing fails for twenty of the (o1, o2) openings
    # that arise from the table's second moves, so the 5 x 5 table
    # needs quiet forks
    _, _, gaps = build_tables(n=5, exact=False)
    assert len(gaps) == 20
