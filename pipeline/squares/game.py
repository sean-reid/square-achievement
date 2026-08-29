"""Game state and the queries a strategy uses.

Cells are (row, col), zero-based from the top-left. A player wins by
occupying all four corners of any axis-aligned square, from the 2x2
block (corners one apart) on up.
"""

from functools import cache

P1 = 1
P2 = 2


def other(player):
    return P2 if player == P1 else P1


@cache
def all_squares(n):
    """Corner sets of every winning square on the n x n board."""
    out = []
    for side in range(1, n):
        for r in range(n - side):
            for c in range(n - side):
                out.append(
                    frozenset(
                        {
                            (r, c),
                            (r, c + side),
                            (r + side, c),
                            (r + side, c + side),
                        }
                    )
                )
    return tuple(out)


class Game:
    """An n x n position. P1's stones are the set .p1, P2's the set .p2.

    A strategy receives a Game and may read anything on it (never write).
    .history holds the moves played since the preset position, oldest
    first, as (player, cell) pairs.
    """

    def __init__(self, n, p1=(), p2=()):
        self.n = n
        self.p1 = set()
        self.p2 = set()
        self.history = []
        for cell in p1:
            self._add(P1, tuple(cell))
        for cell in p2:
            self._add(P2, tuple(cell))

    def _add(self, player, cell):
        if not self.on_board(cell):
            raise ValueError(f"cell {cell} is off the {self.n}x{self.n} board")
        if self.occupied(cell):
            raise ValueError(f"cell {cell} is occupied")
        self.stones(player).add(cell)

    def stones(self, player):
        return self.p1 if player == P1 else self.p2

    @property
    def move_count(self):
        return len(self.history)

    @property
    def my_moves(self):
        """P1's moves since the preset, oldest first."""
        return [cell for player, cell in self.history if player == P1]

    @property
    def their_moves(self):
        """P2's moves since the preset, oldest first."""
        return [cell for player, cell in self.history if player == P2]

    @property
    def my_last(self):
        """P1's most recent move, or None."""
        return self.my_moves[-1] if self.my_moves else None

    @property
    def their_last(self):
        """P2's most recent move, or None."""
        return self.their_moves[-1] if self.their_moves else None

    def reply_to(self, cell):
        """P2's move immediately after P1 played cell, or None."""
        for i, (player, played) in enumerate(self.history):
            if player == P1 and played == cell:
                if i + 1 < len(self.history):
                    return self.history[i + 1][1]
                return None
        return None

    def on_board(self, cell):
        r, c = cell
        return 0 <= r < self.n and 0 <= c < self.n

    def occupied(self, cell):
        return cell in self.p1 or cell in self.p2

    def empty(self, cell):
        return self.on_board(cell) and not self.occupied(cell)

    def empties(self):
        """All empty cells, row-major."""
        return [
            (r, c) for r in range(self.n) for c in range(self.n) if not self.occupied((r, c))
        ]

    def is_full(self):
        return len(self.p1) + len(self.p2) == self.n * self.n

    def play(self, player, cell):
        self._add(player, cell)
        self.history.append((player, cell))

    def undo(self):
        player, cell = self.history.pop()
        self.stones(player).discard(cell)

    def wins(self, player):
        """True if player has completed a square."""
        mine = self.stones(player)
        return any(square <= mine for square in all_squares(self.n))

    def completes(self, cell, player):
        """True if playing the empty cell would finish a square for player."""
        mine = self.stones(player)
        return any(square - mine == {cell} for square in all_squares(self.n))

    def threats(self, player):
        """Empty cells where player would complete a square, sorted."""
        mine = self.stones(player)
        cells = set()
        for square in all_squares(self.n):
            missing = square - mine
            if len(missing) == 1:
                cell = next(iter(missing))
                if not self.occupied(cell):
                    cells.add(cell)
        return sorted(cells)

    def render(self):
        rows = ["   " + " ".join(str(c % 10) for c in range(self.n))]
        for r in range(self.n):
            marks = [
                "X" if (r, c) in self.p1 else "O" if (r, c) in self.p2 else "."
                for c in range(self.n)
            ]
            rows.append(f"{r:2} " + " ".join(marks))
        return "\n".join(rows)

    __str__ = render
