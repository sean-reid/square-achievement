"""Exact solver and strategy-table extraction for small boards.

python3 -m squares.solve regenerates strategy5.py: a complete lookup
strategy for the 5x5 board, verified exhaustively after generation.

The solver is a three-valued negamax (P1 win / draw / P2 win, draws
count against P1) over bitboards, with forced blocks collapsed to a
single move and threat-making moves searched first. The extractor turns
solved positions into table entries: a pure forcing script where one
exists, otherwise a solver-chosen move with a fork over every reply.
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


def _merge_default(table):
    """Replace the most common entry with a None default."""
    if not table:
        return table
    counts = {}
    for entry in table.values():
        key = repr(entry)
        counts[key] = counts.get(key, 0) + 1
    common = max(counts, key=counts.get)
    if counts[common] < 2:
        return table
    out = {k: v for k, v in table.items() if repr(v) != common}
    out[None] = next(v for v in table.values() if repr(v) == common)
    return out


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


def _extract(solver, p1, p2, budget, memo=None):
    """A table entry winning the position under reflex semantics.

    Plan tuples may include cells the reflexes end up playing; resolve
    skips cells already held, so that is harmless.
    """
    if memo is None:
        memo = solver.extract_memo = getattr(solver, "extract_memo", {})
    key = (p1, p2)
    cached = memo.get(key)
    if cached is not None:
        return cached
    if solver.threat_bits(p1, p2):
        memo[key] = ()
        return ()
    blocks = solver.threat_bits(p2, p1)
    if blocks:
        if blocks.bit_count() > 1:
            raise ValueError("position is lost")
        move_bit = blocks  # the block reflex plays this
    else:
        script = forcing_bits(solver, p1, p2, budget)
        if script is not None:
            memo[key] = script
            return script
        move_bit = solver.winning_bit(p1, p2)
        if move_bit is None:
            raise ValueError("position is not a P1 win")
    move = solver.cell(move_bit)
    mine = solver.threat_bits(p1 | move_bit, p2)
    count = mine.bit_count()
    if count >= 2:
        entry = (move,)  # any reply, the win reflex finishes
    elif count == 1:
        cont = _extract(solver, p1 | move_bit, p2 | mine, budget, memo)
        if cont and cont[0] == "q":
            entry = ("q", move, {solver.cell(mine): cont, None: ()})
        else:
            entry = (move,) + cont
    else:
        table = {}
        free = solver.full & ~p1 & ~p2 & ~move_bit
        while free:
            low = free & -free
            free ^= low
            table[solver.cell(low)] = _extract(solver, p1 | move_bit, p2 | low, budget, memo)
        entry = ("q", move, _merge_default(table))
    memo[key] = entry
    return entry


def build_tables(n=5, opening=(2, 2), progress=None, exact=True, box=None, plan_box=None):
    """Generate (x2_map, scripts, gaps) for o1 inside the box.

    With exact=True, hard pairs go through the exact solver and gaps
    stays empty. With exact=False only the forcing search runs, and
    pairs it cannot win land in gaps as (o1, x2, o2). plan_box confines
    P1's plan region so scripts stay valid on every board that size up.
    """
    solver = Solver(n, box=plan_box)
    x2_candidates = [(3, 2), (2, 3), (1, 2), (2, 1), (3, 3), (1, 1), (3, 1), (1, 3)]
    o1_cells = [(r, c) for r in range(min(n, box or n)) for c in range(min(n, box or n))]
    o2_cells = [(r, c) for r in range(n) for c in range(n)]
    x2_map, scripts, gaps = {}, {}, []
    for o1 in o1_cells:
        if o1 == opening:
            continue
        options = [x2 for x2 in x2_candidates if x2 != o1]
        if exact:
            solver_bit = solver.winning_bit(solver.bit(opening), solver.bit(o1))
            if solver_bit is None:
                raise ValueError(f"o1 {o1} refutes the opening")
            fallback = solver.cell(solver_bit)
            if fallback not in options:
                options.append(fallback)
        best = None
        for x2 in options:
            base1 = solver.bit(opening) | solver.bit(x2)
            base2 = solver.bit(o1)
            table, pure, missing = {}, 0, []
            try:
                for o2 in o2_cells:
                    if o2 in (opening, o1, x2):
                        continue
                    p1b, p2b = base1, base2 | solver.bit(o2)
                    script = forcing_bits(solver, p1b, p2b, 8)
                    if script is not None:
                        table[o2] = script
                        pure += 1
                    elif exact:
                        table[o2] = _extract(solver, p1b, p2b, 8)
                    else:
                        missing.append(o2)
            except ValueError:
                continue  # this x2 loses somewhere
            if best is None or pure > best[0]:
                best = (pure, x2, table, missing)
            if not missing and pure == len(table):
                break
        if best is None:
            raise ValueError(f"no winning x2 found for o1 {o1}")
        pure, x2, table, missing = best
        x2_map[o1] = x2
        scripts[o1] = _merge_default(table)
        gaps.extend((o1, x2, o2) for o2 in missing)
        if progress:
            progress(f"o1 {o1}: x2 {x2}, {pure} pure, {len(missing)} gaps")
    return x2_map, scripts, gaps


def _farm_hot_cells(o1_key, box, far_edge):
    """Box cells a beyond-board far pair can farm through, per branch.

    Class branches face the full row, column, or box; an exact aligned
    key at distance c faces only the cells whose partner falls off the
    generation board (nearer partners were verified concretely).
    """
    if o1_key is None:
        return [(a, b) for a in range(box) for b in range(box)]
    if isinstance(o1_key[0], str):
        kind, i = o1_key
        if kind == "row":
            return [(i, b) for b in range(box)]
        return [(a, i) for a in range(box)]
    r, c = o1_key
    out = []
    if r < box and c >= 2 * box:
        out += [(r, b) for b in range(max(0, r + c - far_edge))]
    if c < box and r >= 2 * box:
        out += [(a, c) for a in range(max(0, r + c - far_edge))]
    return out


def build_general(gen_n=12, plan_box=6, progress=None):
    """Tables for every board size: exact keys from the gen_n board,
    alignment-class keys taken from the farthest representatives, and
    per-branch farm entries whose plans never hand the opponent the
    box corner of a beyond-board farm square."""
    x2_map, scripts, gaps = build_tables(
        gen_n, exact=False, box=gen_n, plan_box=plan_box, progress=progress
    )
    if gaps:
        raise ValueError(f"{len(gaps)} forcing gaps, first: {gaps[:3]}")
    far = gen_n - 1
    reps = [(("row", r), (r, far)) for r in range(plan_box)]
    reps += [(("col", c), (far, c)) for c in range(plan_box)]
    rep_of = dict(reps)
    rep_of[None] = (far, far)
    for key, rep in reps:
        x2_map[key] = x2_map[rep]
        scripts[key] = scripts[rep]
    x2_map[None] = x2_map[(far, far)]
    scripts[None] = scripts[(far, far)]
    for table in scripts.values():
        for key, rep in reps:
            if rep in table:
                table[key] = table[rep]
    solver = Solver(gen_n, box=plan_box)
    opening = (2, 2)
    o2rep = (far, far - 1)
    farms = 0
    for key in list(scripts):
        for t in _farm_hot_cells(key, plan_box, far):
            table = scripts[key]
            if ("farm", t) in table:
                continue
            o1rep = rep_of.get(key, key)
            x2 = x2_map[key]
            p1 = solver.bit(opening) | solver.bit(x2)
            p2 = solver.bit(o1rep) | solver.bit(o2rep)
            solver.hot_mask = solver.bit(t)
            script = forcing_bits(solver, p1, p2, 8)
            solver.hot_mask = 0
            if script is None:
                raise ValueError(f"no farm-safe script for {key} hot {t}")
            table[("farm", t)] = script
            farms += 1
    if progress:
        progress(f"farm entries: {farms}")
    return x2_map, scripts


def general_main():
    import pathlib
    import pprint

    from .forcing import box_class, table_strategy
    from .verify import verify

    x2_map, scripts = build_general(progress=print)
    strategy = table_strategy(x2_map, scripts, classify=box_class)
    print("full-board verification from the empty board:")
    for n in range(6, 14):
        result = verify(strategy, n)
        print(result.report().splitlines()[0], flush=True)
        if not result.proven:
            print(result.report())
            return
    body = (
        '"""A P1 strategy for every board size six and up.\n\n'
        "Generated by python3 -m squares.solve general; regenerate rather\n"
        "than edit. P1's plan is confined to the 6x6 corner box; far replies\n"
        "resolve through exact keys from the n=12 board, then alignment\n"
        "classes (box_class), then the generic default. Verified\n"
        "exhaustively from the empty board at n = 6 through 13.\n"
        '"""\n\n'
        "from .forcing import box_class, table_strategy\n\n"
        f"X2 = {pprint.pformat(x2_map, width=100)}\n\n"
        f"SCRIPTS = {pprint.pformat(scripts, width=100)}\n\n"
        "strategy_box = table_strategy(X2, SCRIPTS, classify=box_class)\n"
    )
    path = pathlib.Path(__file__).with_name("strategy_box.py")
    path.write_text(body)
    print(f"wrote {path}")


def main():
    import pprint

    x2_map, scripts, gaps = build_tables(progress=print)
    assert not gaps
    body = (
        '"""A complete P1 strategy for the 5x5 board.\n\n'
        "Generated by python3 -m squares.solve; regenerate rather than edit.\n"
        "x1 is (2,2); X2 picks the second move per o1; SCRIPTS maps (o1, o2)\n"
        "to the entry that follows, with None as the default key and\n"
        '("q", move, table) marking a move that forks on its reply.\n'
        '"""\n\n'
        "from .forcing import table_strategy\n\n"
        f"X2 = {pprint.pformat(x2_map, width=100)}\n\n"
        f"SCRIPTS = {pprint.pformat(scripts, width=100)}\n\n"
        "strategy5 = table_strategy(X2, SCRIPTS)\n"
    )
    import pathlib

    path = pathlib.Path(__file__).with_name("strategy5.py")
    path.write_text(body)
    print(f"wrote {path}")

    from .verify import verify

    result = verify(__import__("squares.strategy5", fromlist=["strategy5"]).strategy5, 5)
    print(result.report().splitlines()[0])


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "general":
        general_main()
    else:
        main()
