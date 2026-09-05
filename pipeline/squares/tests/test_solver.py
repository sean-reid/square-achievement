from squares.solver import Solver, forcing_bits


def test_small_boards_are_not_p1_wins():
    for n in (2, 3, 4):
        solver = Solver(n)
        assert not solver.p1_wins(0, 0, True)


def test_winning_bit_agrees_with_p1_wins():
    solver = Solver(4)
    assert solver.winning_bit(0, 0) is None


def test_plan_box_confines_candidates():
    solver = Solver(9, box=6)
    p1 = solver.bit((2, 2)) | solver.bit((3, 2))
    p2 = solver.bit((0, 3)) | solver.bit((2, 3))
    script = forcing_bits(solver, p1, p2, 8)
    assert script is not None
    assert all(r < 6 and c < 6 for r, c in script)
