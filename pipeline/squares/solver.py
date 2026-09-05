"""Exact solver and forcing search over bitboards.

The solver is a three-valued negamax (P1 win / draw / P2 win, draws
count against P1) with forced blocks collapsed to a single move and
threat-making moves searched first. forcing_bits searches for an
all-forcing winning plan from a position, the building block of every
strategy table.
"""

from .game import all_squares


class Solver:
    def __init__(self, n, box=None):
        """box confines P1's plan: his candidate moves and the squares
        his threats run through must fit the box x box corner region, so
        generated scripts only rely on geometry every n >= box has.
        Opponent threats always use the whole board."""
        self.n = n
        self.full = (1 << n * n) - 1
        self.squares = [sum(1 << (r * n + c) for r, c in sq) for sq in all_squares(n)]
        self.hot_mask = 0
        if box is None:
            self.box_mask = self.full
            self.plan_squares = self.squares
        else:
            self.box_mask = sum(1 << (r * n + c) for r in range(box) for c in range(box))
            self.plan_squares = [m for m in self.squares if m & self.box_mask == m]
        self.memo = {}

    def plan_threat_bits(self, mine, theirs):
        out = 0
        for m in self.plan_squares:
            if not m & theirs:
                have = mine & m
                if have.bit_count() == 3:
                    out |= m ^ have
        return out & ~theirs

    def bit(self, cell):
        return 1 << (cell[0] * self.n + cell[1])

    def cell(self, bit):
        i = bit.bit_length() - 1
        return divmod(i, self.n)

    def bits(self, stones):
        return sum(self.bit(c) for c in stones)

    def threat_bits(self, mine, theirs):
        out = 0
        for m in self.squares:
            if not m & theirs:
                have = mine & m
                if have.bit_count() == 3:
                    out |= m ^ have
        return out & ~theirs

    def p1_wins(self, p1, p2, p1_to_move):
        """True if P1 forces a win; a draw counts as False.

        The memo stores (win, move): at winning P1 nodes, move is the
        winning move found, which doubles as the extraction policy.
        """
        key = (p1, p2, p1_to_move)
        cached = self.memo.get(key)
        if cached is not None:
            return cached[0]
        mine, theirs = (p1, p2) if p1_to_move else (p2, p1)
        if self.threat_bits(mine, theirs):
            self.memo[key] = (p1_to_move, None)
            return p1_to_move
        opp = self.threat_bits(theirs, mine)
        free = self.full & ~p1 & ~p2
        if not free:
            self.memo[key] = (False, None)
            return False
        if opp.bit_count() >= 2:
            self.memo[key] = (not p1_to_move, None)
            return not p1_to_move
        moves = [opp] if opp else self._ordered(free, mine, theirs)
        if p1_to_move:
            for low in moves:
                if self.p1_wins(p1 | low, p2, False):
                    self.memo[key] = (True, low)
                    return True
            self.memo[key] = (False, None)
            return False
        for low in moves:
            if not self.p1_wins(p1, p2 | low, True):
                self.memo[key] = (False, None)
                return False
        self.memo[key] = (True, None)
        return True

    def winning_bit(self, p1, p2):
        """The stored winning move for P1 in this position, or None."""
        if not self.p1_wins(p1, p2, True):
            return None
        return self.memo[(p1, p2, True)][1]

    def _ordered(self, free, mine, theirs):
        scored = []
        b = free
        while b:
            low = b & -b
            b ^= low
            made = self.threat_bits(mine | low, theirs).bit_count()
            scored.append((-made, low))
        scored.sort()
        return [low for _, low in scored]


def forcing_bits(solver, p1, p2, budget):
    """A winning all-forcing plan as a tuple of cells, or None.

    P1's threats and candidate moves go through the solver's plan
    region; the opponent's threats always use the whole board, so a
    boxed solver only accepts lines that survive its own board size.
    """
    if solver.plan_threat_bits(p1, p2):
        return ()
    opp = solver.threat_bits(p2, p1)
    if opp:
        if opp.bit_count() > 1:
            return None
        return _forcing_after(solver, p1 | opp, p2, budget)
    if budget == 0:
        return None
    scored = []
    b = solver.box_mask & ~p1 & ~p2
    while b:
        low = b & -b
        b ^= low
        made = solver.plan_threat_bits(p1 | low, p2).bit_count()
        if made:
            scored.append((-made, low))
    scored.sort()
    for _, low in scored:
        tail = _forcing_after(solver, p1 | low, p2, budget - 1)
        if tail is not None:
            return (solver.cell(low),) + tail
    return None


def _forcing_after(solver, p1, p2, budget):
    if solver.threat_bits(p2, p1):
        return None
    mine = solver.plan_threat_bits(p1, p2)
    count = mine.bit_count()
    if count >= 2:
        return ()
    if count == 1:
        if mine & solver.hot_mask:
            return None  # the forced block would hand P2 the farm corner
        return forcing_bits(solver, p1, p2 | mine, budget)
    return None
