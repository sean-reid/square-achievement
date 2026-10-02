"""Claims the paper makes about the 5 x 5 table."""

from squares.five import strategy5
from squares.five.forcing import forcing_script, quiet_pairs
from squares.five.tables import build_tables
from squares.game import P1, P2, Game


def test_quiet_moves_are_exactly_the_pairs_without_a_forcing_win():
    quiet = set(quiet_pairs(strategy5.X2, strategy5.SCRIPTS))
    cells = [(r, c) for r in range(5) for c in range(5)]
    no_forcing = set()
    for o1, x2 in strategy5.X2.items():
        for o2 in cells:
            if o2 in ((2, 2), o1, x2):
                continue
            g = Game(5)
            for player, move in ((P1, (2, 2)), (P2, o1), (P1, x2), (P2, o2)):
                g.play(player, move)
            if forcing_script(g, 8) is None:
                no_forcing.add((o1, o2))
    assert len(quiet) == 104
    assert quiet == no_forcing


def test_forcing_only_generation_leaves_twenty_gaps():
    _, _, gaps = build_tables(n=5, exact=False)
    assert len(gaps) == 20
