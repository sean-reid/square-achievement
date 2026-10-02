"""Search for forcing win scripts.

A forcing script is a list of P1 moves that each create at least one
threat, so every P2 reply is a forced block, until a move creates two
threats at once. The search mirrors the reflex semantics exactly:
completions are taken, a lone opposing threat is blocked even when the
block is quiet, two opposing threats lose. Scripts list only P1's free
moves; forced blocks are the block reflex's job at replay.
"""

from ..game import P1, P2
from ..hidden import farm_relation


def _candidates(g):
    """Empty cells that would create a P1 threat, most threats first."""
    out = []
    for cell in g.empties():
        g.play(P1, cell)
        made = len(g.threats(P1))
        g.undo()
        if made:
            out.append((-made, cell))
    out.sort()
    return [cell for _, cell in out]


def forcing_script(g, budget):
    """A winning all-forcing plan of at most budget free moves, or None.

    P1 is to move in g.
    """
    if g.threats(P1):
        return ()
    blocks = g.threats(P2)
    if blocks:
        if len(blocks) > 1:
            return None
        g.play(P1, blocks[0])
        try:
            return _after_p1(g, budget)
        finally:
            g.undo()
    if budget == 0:
        return None
    for move in _candidates(g):
        g.play(P1, move)
        try:
            tail = _after_p1(g, budget - 1)
        finally:
            g.undo()
        if tail is not None:
            return (move,) + tail
    return None


def _after_p1(g, budget):
    """P1 just moved; P2 answers by force or loses."""
    if g.threats(P2):
        return None
    mine = g.threats(P1)
    if len(mine) >= 2:
        return ()
    if len(mine) == 1:
        g.play(P2, mine[0])
        try:
            return forcing_script(g, budget)
        finally:
            g.undo()
    return None


def quiet_extension(g, budget):
    """One quiet move, then a forcing script for every reply.

    Returns (move, {reply: script}) or None. Used where pure forcing has
    no win: the quiet move rebuilds shape at the cost of one free P2
    reply, and each reply gets its own forcing script.
    """
    threatening = set(_candidates(g))
    quiet = [c for c in g.empties() if c not in threatening]
    quiet.sort(key=lambda c: abs(c[0] - 2) + abs(c[1] - 2))
    for move in quiet:
        g.play(P1, move)
        table = {}
        for reply in list(g.empties()):
            g.play(P2, reply)
            script = forcing_script(g, budget)
            g.undo()
            if script is None:
                table = None
                break
            table[reply] = script
        g.undo()
        if table is not None:
            return move, table
    return None


def resolve(g, entry):
    """The move an entry prescribes in the current position.

    An entry is a tuple of cells (a forcing plan: play the first cell
    not already P1's) or ("q", move, table): play move, then fork on
    the reply to it, with None as the table's default key.
    """
    while True:
        if entry and entry[0] == "q":
            _, move, table = entry
            if move not in g.p1:
                return move
            reply = g.reply_to(move)
            entry = table.get(reply, table.get(None))
            if entry is None:
                raise NotImplementedError(f"no branch for reply {reply} to {move}")
            continue
        for cell in entry:
            if cell not in g.p1:
                return cell
        raise NotImplementedError("plan exhausted")


def box_class(cell, box=6):
    """The alignment class of a far cell relative to the corner box.

    A far stone sharing a row or column with the box can join squares
    through the box at any distance, so those cells form per-line
    classes; everything else far is generic (None).
    """
    r, c = cell
    if r < box and c >= box:
        return ("row", r)
    if c < box and r >= box:
        return ("col", c)
    return None


def quiet_pairs(x2, scripts, n=5, opening=(2, 2)):
    """The reply pairs (o1, o2) whose table entry opens with a quiet move."""
    cells = [(r, c) for r in range(n) for c in range(n)]
    out = []
    for o1, second in x2.items():
        table = scripts[o1]
        for o2 in cells:
            if o2 in (opening, o1, second):
                continue
            entry = table.get(o2, table.get(None))
            if entry and entry[0] == "q":
                out.append((o1, o2))
    return out


def table_strategy(x2, scripts, opening=(2, 2), classify=None, meter=None):
    """The lookup strategy over a generated (x2, scripts) table.

    x2 maps o1 to P1's second move; scripts maps o1 to a table mapping
    o2 (or None as the default) to the entry that follows. classify, if
    given, maps a cell with no exact key to a class key tried before
    the None default. meter, if given, hears every decision: .key(cell,
    kind) for lookups (exact/class/default) and .move(g, kind, cell)
    for the chosen move (win/block/opening/x2/plan).
    """

    def lookup(table, cell):
        entry = table.get(cell)
        if entry is not None:
            if meter is not None:
                meter.key(cell, "exact")
            return entry
        if classify is not None:
            cls = classify(cell)
            if cls is not None:
                entry = table.get(cls)
                if entry is not None:
                    if meter is not None:
                        meter.key(cell, "class")
                    return entry
        entry = table.get(None)
        if meter is not None and entry is not None:
            meter.key(cell, "default")
        return entry

    def strategy(g):
        wins = g.threats(P1)
        if wins:
            if meter is not None:
                meter.move(g, "win", wins[0])
            return wins[0]
        blocks = g.threats(P2)
        if blocks:
            if meter is not None:
                meter.move(g, "block", blocks[0])
            return blocks[0]
        if not g.my_moves:
            if meter is not None:
                meter.move(g, "opening", opening)
            return opening
        o1 = g.reply_to(opening)
        second = lookup(x2, o1)
        if second is None:
            raise NotImplementedError(f"no x2 entry for o1 {o1}")
        if second not in g.p1:
            if meter is not None:
                meter.move(g, "x2", second)
            return second
        o2 = g.reply_to(second)
        table = lookup(scripts, o1)
        entry = None
        # an exact o2 entry is only pair-safe when o1 is exact too:
        # shifting an abstract o1 moves the pair's farm cell away from
        # the one the exact entry was generated against
        fk = None if o1 in scripts else farm_relation(o1, o2)
        if fk is not None:
            entry = table.get(fk)
            if entry is not None and meter is not None:
                meter.key(o2, "farm")
        if entry is None:
            entry = table.get(o2)
            if entry is not None:
                if meter is not None:
                    meter.key(o2, "exact")
            else:
                fk2 = farm_relation(o1, o2)
                if fk2 is not None:
                    entry = table.get(fk2)
                    if entry is not None and meter is not None:
                        meter.key(o2, "farm")
                if entry is None:
                    entry = lookup(table, o2)
        if entry is None:
            raise NotImplementedError(f"no plan for o1 {o1}, o2 {o2}")
        move = resolve(g, entry)
        if meter is not None:
            meter.move(g, "plan", move)
        return move

    return strategy
