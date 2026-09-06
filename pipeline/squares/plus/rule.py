"""The plus rule, mirroring formalization/Plus/Rule.lean move for move.

A plus is a stone we hold with the four cells at distance s along the
axes; each arm played makes three corners of a side-s square with the
centre and a neighbouring arm, so the opponent must block the diagonal
cell, and the last arm threatens two squares at once. A tempo move is a
single forcing move.

The rule: open at (2, 2); reply below it at (3, 2), except against seven
first replies touching the opening pair, where a fixed diagram gives the
second move; take a win or a block by reflex; otherwise follow the line
chosen at the second reply, the shortest sequence of at most three
tempo moves followed by a plus of side 1 or 2, preferring fewer tempo
moves, then the smaller plus, then cell order, and never making a
threat whose only block is the latent corner of the opponent's two free
stones.

The rule reads an abstraction of the position: our stones (in the 6 x 6
corner), the opponent's stones inside the 17 x 17 base board, and the
latent corner of the free pair.
"""

from itertools import permutations

from ..game import P1, P2
from ..threshold.forcing import farm_relation

BOX = 6
BASE = 17
OPENING = (2, 2)
DEPTH = 3


def second_move(o1):
    """The second move: (3, 2) unless the first reply touches the pair."""
    if o1 in ((1, 3), (2, 3), (3, 3)):
        return (2, 1)
    if o1 in ((2, 1), (4, 3)):
        return (2, 3)
    if o1 in ((3, 1), (3, 2)):
        return (1, 2)
    return (3, 2)


def squares_through(k, a, b):
    """Squares inside board k with corners a and b, as corner lists."""
    if a == b:
        return []
    if a[0] == b[0]:
        d = abs(a[1] - b[1])
        c, r = min(a[1], b[1]), a[0]
        out = []
        if r + d < k:
            out.append([(r, c), (r, c + d), (r + d, c), (r + d, c + d)])
        if d <= r:
            out.append([(r - d, c), (r - d, c + d), (r, c), (r, c + d)])
        return out
    if a[1] == b[1]:
        d = abs(a[0] - b[0])
        r, c = min(a[0], b[0]), a[1]
        out = []
        if c + d < k:
            out.append([(r, c), (r, c + d), (r + d, c), (r + d, c + d)])
        if d <= c:
            out.append([(r, c - d), (r, c), (r + d, c - d), (r + d, c)])
        return out
    dr, dc = abs(a[0] - b[0]), abs(a[1] - b[1])
    if dr == dc:
        r, c = min(a[0], b[0]), min(a[1], b[1])
        return [[(r, c), (r, c + dr), (r + dr, c), (r + dr, c + dr)]]
    return []


def threats_in(k, mine, occ):
    """Cells where mine is one stone short of a square inside board k,
    unblocked; sorted by cell."""
    mine_set, occ_set = set(mine), set(occ)
    out = set()
    for a in mine:
        for b in mine:
            if a < b:
                for sq in squares_through(k, a, b):
                    missing = [x for x in sq if x not in mine_set]
                    if len(missing) == 1 and missing[0] not in occ_set:
                        out.add(missing[0])
    return sorted(out)


def my_threats(p1, occ):
    return threats_in(BOX, p1, occ)


def their_threats(p2, occ):
    return threats_in(BASE, p2, occ)


class Abs:
    """The abstract position the rule reads."""

    __slots__ = ("p1", "p2", "hot")

    def __init__(self, p1, p2, hot):
        self.p1, self.p2, self.hot = p1, p2, hot


def force_line(a, moves):
    """Play moves under forcing semantics, as the checker judges them."""
    p1, p2 = list(a.p1), list(a.p2)
    for m in moves:
        if m in p1 or m in p2:
            return False
        p1 = [m] + p1
        if their_threats(p2, p1 + p2):
            return False
        mine = my_threats(p1, p1 + p2)
        if len(mine) >= 2:
            return True
        if not mine or mine[0] == a.hot:
            return False
        p2 = [mine[0]] + p2
    return False


def arms(c, s):
    return [(c[0] - s, c[1]), (c[0] + s, c[1]), (c[0], c[1] - s), (c[0], c[1] + s)]


def arms_ok(c, s):
    return s <= c[0] and s <= c[1] and c[0] + s < BOX and c[1] + s < BOX


def winning_pluses(a):
    """Every plus we can complete by force, as ((todo, side, centre), order),
    sorted by key then order."""
    out = []
    for c in a.p1:
        for s in (1, 2):
            if not arms_ok(c, s):
                continue
            todo = [x for x in arms(c, s) if x not in a.p1]
            if not todo or any(x in a.p2 for x in todo):
                continue
            for order in permutations(todo):
                if force_line(a, order):
                    out.append(((len(todo), s, c), list(order)))
                    break
    out.sort()
    return out


def tempo_moves(a):
    """Single forcing moves with the block forced and not on the latent
    corner, in cell order."""
    out = []
    for r in range(BOX):
        for c in range(BOX):
            m = (r, c)
            if m in a.p1 or m in a.p2:
                continue
            p1 = [m] + a.p1
            if their_threats(a.p2, p1 + a.p2):
                continue
            mine = my_threats(p1, p1 + a.p2)
            if len(mine) == 1 and mine[0] != a.hot:
                out.append((m, Abs(p1, [mine[0]] + a.p2, a.hot)))
    return out


def best_line(a):
    """The best line within DEPTH tempo moves, or None."""
    frontier = [(a, [])]
    for d in range(DEPTH + 1):
        best = None
        for b, pre in frontier:
            if their_threats(b.p2, b.p1 + b.p2):
                continue
            pl = winning_pluses(b)
            if pl:
                key, order = pl[0]
                if best is None or key < best[0]:
                    best = (key, pre + order)
        if best is not None:
            return best[1]
        if d == DEPTH:
            return None
        frontier = [(b2, pre + [m]) for b, pre in frontier for m, b2 in tempo_moves(b)]
        if not frontier:
            return None
    return None


def abstract_of(p1, p2, o1, o2):
    """The abstraction of a position given the two free replies."""
    near = [x for x in p2 if x[0] < BASE and x[1] < BASE]
    fk = farm_relation(o1, o2) if o1 is not None and o2 is not None else None
    hot = fk[1] if fk else None
    return Abs(list(p1), near, hot)


def strategy(g):
    """The rule as a move function for the exhaustive verifier."""
    wins = g.threats(P1)
    if wins:
        return wins[0]
    blocks = g.threats(P2)
    if blocks:
        return blocks[0]
    if not g.my_moves:
        return OPENING
    o1 = g.reply_to(OPENING)
    x2 = second_move(o1)
    if x2 not in g.p1:
        return x2
    o2 = g.reply_to(x2)
    root = abstract_of([OPENING, x2], [o1, o2], o1, o2)
    line = best_line(root)
    if line is None:
        raise NotImplementedError(f"no line for {o1}, {o2}")
    for cell in line:
        if cell not in g.p1:
            return cell
    raise NotImplementedError("line exhausted")
