import pytest

from squares import P1, P2, verify, verify_many
from squares.verify import DRAW, ILLEGAL_MOVE, P2_WIN, STRATEGY_ERROR


def take_win_else(cell):
    def strategy(g):
        if g.threats(P1):
            return g.threats(P1)[0]
        return cell

    return strategy


def test_triple_threat_proven():
    p1 = ((0, 0), (0, 2), (2, 4), (4, 2))
    p2 = ((1, 5), (3, 4), (5, 0), (5, 2))
    result = verify(take_win_else((2, 2)), 6, p1=p1, p2=p2)
    assert result.proven
    assert result.stats.lines == 27
    assert not result.counterexamples


def test_proven_on_larger_boards():
    p1 = ((0, 0), (0, 2), (2, 4), (4, 2))
    p2 = ((1, 5), (3, 4), (5, 0), (5, 2))
    results = verify_many(take_win_else((2, 2)), (6, 7, 8), p1=p1, p2=p2)
    assert [r.stats.lines for r in results] == [27, 40, 55]


def test_p2_win_counterexample():
    p1 = ((0, 0), (0, 2), (2, 4))
    p2 = ((3, 3), (3, 5), (5, 3))
    result = verify(take_win_else((2, 2)), 6, p1=p1, p2=p2)
    assert not result.proven
    ce = result.counterexamples[0]
    assert ce.kind == P2_WIN
    assert ce.line == ((P1, (2, 2)), (P2, (5, 5)))


def test_draw_counterexample():
    p1 = ((0, 0), (0, 1), (1, 1), (2, 0))
    p2 = ((0, 2), (1, 0), (1, 2), (2, 1))
    result = verify(lambda g: (2, 2), 3, p1=p1, p2=p2)
    assert not result.proven
    assert result.counterexamples[0].kind == DRAW


def test_illegal_move_occupied():
    result = verify(lambda g: (0, 0), 4)
    assert not result.proven
    ce = result.counterexamples[0]
    assert ce.kind == ILLEGAL_MOVE
    assert ce.line == ((P1, (0, 0)), (P2, (0, 1)))


def test_illegal_move_off_board():
    result = verify(lambda g: (9, 9), 4)
    assert result.counterexamples[0].kind == ILLEGAL_MOVE


def test_strategy_exception_is_reported():
    def strategy(g):
        raise RuntimeError("boom")

    result = verify(strategy, 4)
    assert result.counterexamples[0].kind == STRATEGY_ERROR


def test_strategy_bad_return_is_reported():
    result = verify(lambda g: "nonsense", 4)
    assert result.counterexamples[0].kind == STRATEGY_ERROR


def test_strategy_mutation_is_reported():
    def strategy(g):
        g.p1.add((3, 3))
        return (0, 0)

    result = verify(strategy, 4)
    assert result.counterexamples[0].kind == STRATEGY_ERROR
    assert "mutated" in result.counterexamples[0].note


def test_opening_presets_history():
    seen = {}

    def strategy(g):
        seen["history"] = tuple(g.history)
        return (5, 5)

    verify(strategy, 6, opening=((2, 2), (0, 0)), stop_after=1)
    assert seen["history"][:2] == ((P1, (2, 2)), (P2, (0, 0)))


def test_initial_p2_square_rejected():
    with pytest.raises(ValueError):
        verify(lambda g: (1, 1), 4, p2=[(0, 0), (0, 2), (2, 0), (2, 2)])


def test_initial_p1_square_is_trivially_proven():
    result = verify(lambda g: (1, 1), 4, p1=[(0, 0), (0, 2), (2, 0), (2, 2)])
    assert result.proven


def test_stop_after_collects_multiple():
    result = verify(lambda g: (0, 0), 4, stop_after=3)
    assert len(result.counterexamples) == 3
