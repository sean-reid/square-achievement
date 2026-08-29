from squares import P1, P2, Game
from squares.forcing import forcing_script, resolve, table_strategy
from squares.solve import Solver, forcing_bits


def ladder_game():
    return Game(6, p1=[(2, 2), (2, 3)], p2=[(0, 5), (5, 0)])


def test_forcing_script_finds_the_ladder():
    g = ladder_game()
    script = forcing_script(g, 4)
    assert script is not None
    assert len(script) <= 4


def test_forcing_bits_matches_game_search():
    g = ladder_game()
    solver = Solver(6)
    script = forcing_bits(solver, solver.bits(g.p1), solver.bits(g.p2), 4)
    assert script is not None


def test_resolve_plan_skips_held_cells():
    g = Game(4, p1=[(0, 0)])
    assert resolve(g, ((0, 0), (1, 1))) == (1, 1)


def test_resolve_quiet_node_forks_on_reply():
    g = Game(4)
    g.play(P1, (1, 1))
    g.play(P2, (0, 0))
    entry = ("q", (1, 1), {(0, 0): ((2, 2),), None: ((3, 3),)})
    assert resolve(g, entry) == (2, 2)
    g.undo()
    g.play(P2, (0, 1))
    assert resolve(g, entry) == (3, 3)


def test_table_strategy_routes_through_tables():
    x2 = {(0, 0): (1, 1)}
    scripts = {(0, 0): {None: ((2, 2), (3, 3))}}
    strategy = table_strategy(x2, scripts, opening=(0, 1))
    g = Game(5)
    assert strategy(g) == (0, 1)
    g.play(P1, (0, 1))
    g.play(P2, (0, 0))
    assert strategy(g) == (1, 1)
    g.play(P1, (1, 1))
    g.play(P2, (4, 4))
    assert strategy(g) == (2, 2)
