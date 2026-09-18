"""The far-pair farm geometry and its generation-time constraints."""

from squares.hidden import farm_relation
from squares.solver import Solver, forcing_bits


def test_refutation_pair_is_the_p3_farm():
    # the pair that refuted the gen-15 table at n = 16
    assert farm_relation((0, 15), (12, 3)) == ("farm", (0, 3))
    assert farm_relation((12, 3), (0, 15)) == ("farm", (0, 3))


def test_column_and_row_pairs():
    # same column: (0,20) with (16,20) farms through (0,4)
    assert farm_relation((0, 20), (16, 20)) == ("farm", (0, 4))
    # same row, column-aligned member: transpose of the above
    assert farm_relation((20, 0), (20, 16)) == ("farm", (4, 0))


def test_near_pairs_do_not_farm():
    assert farm_relation((0, 11), (11, 11)) is None  # inside B_12
    assert farm_relation((0, 15), (12, 4)) is None  # relation off by one
    assert farm_relation((14, 13), (13, 14)) is None  # both generic
    assert farm_relation((0, 15), None) is None


def test_hot_pruning_blocks_the_hot_cell():
    solver = Solver(15, box=6)
    solver.hot_mask = solver.bit((0, 3))
    p1 = solver.bit((2, 2)) | solver.bit((3, 2))
    p2 = solver.bit((0, 14)) | solver.bit((14, 13))
    script = forcing_bits(solver, p1, p2, 8)
    assert script is not None
    # replay the script's forced blocks and confirm none lands on (0,3)
    hot = solver.bit((0, 3))
    stones1, stones2 = p1, p2
    for cell in script:
        stones1 |= solver.bit(cell)
        threats = solver.plan_threat_bits(stones1, stones2)
        if threats.bit_count() >= 2:
            break
        assert threats & hot == 0
        stones2 |= threats
