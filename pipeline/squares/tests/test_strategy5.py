from squares import verify
from squares.strategy5 import strategy5


def test_strategy5_is_proven_on_n5():
    result = verify(strategy5, 5)
    assert result.proven
    assert not result.counterexamples
