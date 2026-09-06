"""The plus rule: its lines, its sweep, and its exhaustive verification."""

from squares import verify
from squares.plus.rule import OPENING, abstract_of, best_line, second_move, strategy
from squares.plus.sweep import anchors_safe, sweep


def line(o1, o2):
    x2 = second_move(o1)
    return best_line(abstract_of([OPENING, x2], [o1, o2], o1, o2))


def test_lines_match_the_lean_rule():
    # the same openings evaluated in formalization/Plus/Rule.lean
    assert line((0, 0), (4, 4)) == [(2, 1), (1, 2), (2, 3)]
    assert line((0, 0), (2, 1)) == [(2, 3), (1, 2), (3, 0), (5, 2), (3, 4)]
    assert line((1, 3), (4, 3)) == [(1, 1), (3, 1), (2, 0)]
    assert line((3, 3), (2, 1)) == [(1, 1), (3, 1), (2, 0)]
    assert line((14, 14), (14, 13)) == [(2, 1), (1, 2), (2, 3)]


def test_second_move_diagram():
    exceptions = {o1 for r in range(6) for c in range(6) if second_move(o1 := (r, c)) != (3, 2)}
    assert exceptions == {(1, 3), (2, 3), (3, 3), (2, 1), (4, 3), (3, 1), (3, 2)}
    assert second_move((14, 14)) == (3, 2)


def test_every_opening_on_eight_has_a_line():
    total, fails = sweep(8)
    assert total == 3843
    assert fails == []


def test_anchored_positions_are_safe():
    assert anchors_safe() == []


def test_wins_every_game_on_six():
    result = verify(strategy, 6)
    assert result.proven
    assert result.stats.max_ply == 16


def test_measure_agrees_with_the_rule_on_six():
    from squares.plus.measure import line_with_key, measure

    cells = [(r, c) for r in range(6) for c in range(6)]
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
            assert line_with_key(a)[0] == best_line(a)
    m = measure(6)
    assert (m["roots"], m["lines"], m["max_plies"]) == (1155, 79, 17)
    assert m["tempo"] == {0: 985, 1: 91, 2: 54, 3: 25}
    assert m["sides"] == {1: 985, 2: 170}
