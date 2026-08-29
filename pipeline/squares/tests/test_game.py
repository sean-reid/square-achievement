import pytest

from squares.game import P1, P2, Game, all_squares


def test_square_count():
    assert len(all_squares(3)) == 5
    assert len(all_squares(6)) == 55


def test_unit_square_wins():
    g = Game(4, p1=[(0, 0), (0, 1), (1, 0), (1, 1)])
    assert g.wins(P1)


def test_side_two_square_wins():
    g = Game(4, p1=[(0, 0), (0, 2), (2, 0), (2, 2)])
    assert g.wins(P1)


def test_threats():
    g = Game(4, p1=[(0, 0), (0, 2), (2, 0)])
    assert g.threats(P1) == [(2, 2)]
    assert g.threats(P2) == []


def test_threats_blocked_by_opponent():
    g = Game(4, p1=[(0, 0), (0, 2), (2, 0)], p2=[(2, 2)])
    assert g.threats(P1) == []


def test_completes():
    g = Game(4, p1=[(0, 0), (0, 2), (2, 0)])
    assert g.completes((2, 2), P1)
    assert not g.completes((3, 3), P1)
    assert not g.completes((2, 2), P2)


def test_play_undo_and_history():
    g = Game(4, p1=[(0, 0)])
    g.play(P1, (1, 1))
    g.play(P2, (2, 2))
    assert g.history == [(P1, (1, 1)), (P2, (2, 2))]
    assert g.my_moves == [(1, 1)]
    assert g.their_moves == [(2, 2)]
    assert g.my_last == (1, 1)
    assert g.their_last == (2, 2)
    assert g.move_count == 2
    g.undo()
    assert (2, 2) not in g.p2
    assert g.their_last is None


def test_reply_to():
    g = Game(6)
    g.play(P1, (2, 2))
    g.play(P2, (0, 0))
    g.play(P1, (3, 3))
    assert g.reply_to((2, 2)) == (0, 0)
    assert g.reply_to((3, 3)) is None
    assert g.reply_to((5, 5)) is None


def test_empties_and_full():
    g = Game(3, p1=[(0, 0)], p2=[(1, 1)])
    empties = g.empties()
    assert len(empties) == 7
    assert (0, 0) not in empties
    assert not g.is_full()


def test_occupied_cell_rejected():
    g = Game(4, p1=[(0, 0)])
    with pytest.raises(ValueError):
        g.play(P2, (0, 0))
    with pytest.raises(ValueError):
        g.play(P1, (9, 9))
