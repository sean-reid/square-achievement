"""Play a strategy against every P2 reply sequence.

A strategy is a plain function taking a Game and returning the cell P1
plays. The verifier does nothing on P1's behalf: if a win is available,
the strategy itself must return it. A line ends in a P1 win or a
counterexample: P2 completing a square, a draw, an illegal move, or the
strategy raising or mutating the game.
"""

import time
from dataclasses import dataclass

from .game import P1, P2, Game

P2_WIN = "p2_win"
DRAW = "draw"
ILLEGAL_MOVE = "illegal_move"
STRATEGY_ERROR = "strategy_error"


@dataclass
class Stats:
    states: int = 0
    lines: int = 0
    max_ply: int = 0
    elapsed: float = 0.0


@dataclass
class Counterexample:
    kind: str
    line: tuple
    board: str
    note: str = ""

    def render(self):
        moves = ", ".join(f"{'P1' if p == P1 else 'P2'} {cell}" for p, cell in self.line)
        head = f"{self.kind}: {moves or '(no moves)'}"
        if self.note:
            head += f"\n  {self.note}"
        return head + "\n" + self.board


@dataclass
class Result:
    n: int
    proven: bool
    stats: Stats
    counterexamples: list

    def report(self):
        s = self.stats
        head = (
            f"n={self.n}: {'PROVEN' if self.proven else 'REFUTED'}  "
            f"lines={s.lines} states={s.states} max_ply={s.max_ply} "
            f"elapsed={s.elapsed:.2f}s"
        )
        if self.counterexamples:
            head += "\n\n" + "\n\n".join(ce.render() for ce in self.counterexamples)
        return head


class _Search:
    def __init__(self, strategy, game, stop_after, observer=None):
        self.strategy = strategy
        self.game = game
        self.stop_after = stop_after
        self.observer = observer
        self.stats = Stats()
        self.found = []

    def aborted(self):
        return len(self.found) >= self.stop_after

    def fail(self, kind, note=""):
        self.found.append(
            Counterexample(kind, tuple(self.game.history), self.game.render(), note)
        )

    def ask_strategy(self):
        """The strategy's move, or None after recording what went wrong."""
        game = self.game
        sizes = (len(game.p1), len(game.p2), len(game.history))
        try:
            move = self.strategy(game)
        except Exception as exc:
            self.fail(STRATEGY_ERROR, note=f"strategy raised {exc!r}")
            return None
        if sizes != (len(game.p1), len(game.p2), len(game.history)):
            self.fail(STRATEGY_ERROR, note="strategy mutated the game")
            return None
        try:
            r, c = move
            move = (int(r), int(c))
        except Exception:
            self.fail(STRATEGY_ERROR, note=f"strategy returned {move!r}, not a cell")
            return None
        if not game.empty(move):
            self.fail(ILLEGAL_MOVE, note=f"strategy plays {move}, off the board or occupied")
            return None
        return move

    def explore(self):
        """P1 to move. True if P1 wins against every P2 continuation."""
        game = self.game
        self.stats.states += 1
        self.stats.max_ply = max(self.stats.max_ply, game.move_count)
        if self.observer is not None:
            self.observer(game)
        move = self.ask_strategy()
        if move is None:
            return False
        won = game.completes(move, P1)
        game.play(P1, move)
        try:
            if won:
                self.stats.lines += 1
                return True
            if game.is_full():
                self.fail(DRAW)
                return False
            ok = True
            for reply in game.empties():
                if self.aborted():
                    return False
                won = game.completes(reply, P2)
                game.play(P2, reply)
                try:
                    if won:
                        self.fail(P2_WIN)
                        sub = False
                    elif game.is_full():
                        self.fail(DRAW)
                        sub = False
                    else:
                        sub = self.explore()
                finally:
                    game.undo()
                ok = ok and sub
            return ok
        finally:
            game.undo()


def verify(strategy, n, *, p1=(), p2=(), opening=(), stop_after=1, observer=None):
    """Prove strategy wins for P1 on the n x n board, or return counterexamples.

    P1 is to move at the root. p1 and p2 preset stones without history;
    opening presets by replaying moves (P1 first, alternating), which is
    what a history-keyed strategy needs to pick up mid-line. Both allow
    verifying one stretch of the strategy at a time. observer, if given,
    is called with the game at every P1 decision point.
    """
    game = Game(n, p1, p2)
    for i, cell in enumerate(opening):
        game.play(P1 if i % 2 == 0 else P2, cell)
    if game.wins(P2):
        raise ValueError("initial position already contains a P2 square")
    search = _Search(strategy, game, stop_after, observer)
    start = time.perf_counter()
    if game.wins(P1):
        search.stats.lines = 1
        proven = True
    else:
        proven = search.explore()
    search.stats.elapsed = time.perf_counter() - start
    return Result(n, proven and not search.found, search.stats, search.found)


def verify_many(strategy, sizes, **kwargs):
    return [verify(strategy, n, **kwargs) for n in sizes]
