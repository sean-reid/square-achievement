"""The small-board policy generator proves itself by construction:
draw_policy raises unless every reachable line avoids a loss."""

from squares.smallboard import draw_policy, safe
from squares.solver import Solver


def test_empty_boards_are_safe():
    for n in (2, 3, 4):
        assert safe(Solver(n), 0, 0, True, {})


def test_policies_extract():
    assert len(draw_policy(2)) == 4
    assert len(draw_policy(3)) == 96


def test_policy_moves_are_free_cells():
    for (p1, p2), move in draw_policy(3).items():
        assert move & (p1 | p2) == 0
        assert move.bit_count() == 1
