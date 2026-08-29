"""Generate, verify, and diagnose strategies for the square achievement game."""

from .game import P1, P2, Game, other
from .verify import Counterexample, Result, Stats, verify, verify_many

__all__ = [
    "P1",
    "P2",
    "Counterexample",
    "Game",
    "Result",
    "Stats",
    "other",
    "verify",
    "verify_many",
]
