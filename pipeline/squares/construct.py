"""Construct a double-threat refutation from an audited event.

Given a verified line in which the opponent's forced block at t
created a counter-threat, substitute a far pair aligned with t for
(o1, o2) and replay on a board large enough to hold the farm square.
If the strategy's moves track the original line (same class, so same
plan), the block at t now completes the farm square as well: two
simultaneous threats, and the position is lost. A successful
construction proves the fatal pattern is realizable against the table,
not merely possible in principle.
"""

from .game import P1, P2, Game


def replay(strategy, n, history, subs):
    """Drive strategy for P1, the recorded moves (substituted) for P2.

    Returns ("double", game) when the opponent holds two threats with
    P1 to move, ("diverged", game) when the strategy departs from the
    recorded line, or ("end", game).
    """
    g = Game(n)
    recorded = iter([subs.get(cell, cell) for player, cell in history if player == P2])
    for player, _cell in history:
        if player != P1:
            continue
        move = strategy(g)
        g.play(P1, move)
        if g.wins(P1):
            return "p1_win", g
        if len(g.threats(P2)) >= 2:
            return "double", g
        reply = next(recorded, None)
        if reply is None:
            return "end", g
        if not g.empty(reply):
            return "diverged", g
        g.play(P2, reply)
        if g.wins(P2):
            return "p2_win", g
        if len(g.threats(P2)) >= 2 and not g.threats(P1):
            return "double", g
    return "end", g


def try_event(strategy, history, t, n):
    """Try every alignment family for t against the recorded line."""
    o1 = history[1][1]
    o2 = history[3][1] if len(history) > 3 else None
    a, b = t
    outcomes = []
    for s in range(7, n - max(a, b)):
        corners = [(a, b + s), (a + s, b), (a + s, b + s)]
        for i in range(3):
            pair = [c for j, c in enumerate(corners) if j != i]
            for far1, far2 in (pair, pair[::-1]):
                subs = {o1: far1, o2: far2}
                if len(subs) < 2 or o1 is None or o2 is None:
                    continue
                verdict, g = replay(strategy, n, history, subs)
                outcomes.append((verdict, s, i, (far1, far2)))
                if verdict == "double":
                    return outcomes, g
    return outcomes, None


def adaptive(strategy, n, free_moves):
    """Drive strategy for P1 against a blocking P2 with scripted
    free moves. Returns the verdict and the final game."""
    g = Game(n)
    free = list(free_moves)
    while True:
        move = strategy(g)
        g.play(P1, move)
        if g.wins(P1):
            return "p1_win", g
        if len(g.threats(P1)) >= 2:
            return "p1_double", g
        if g.is_full():
            return "draw", g
        threats = g.threats(P1)
        if threats:
            reply = threats[0]
        elif free:
            reply = free.pop(0)
            if not g.empty(reply):
                return "clash", g
        else:
            return "p2_out_of_script", g
        g.play(P2, reply)
        if g.wins(P2):
            return "p2_win", g
        if len(g.threats(P2)) >= 2:
            return "DOUBLE", g


def main():
    import sys

    from .audit_farms import _tables
    from .forcing import box_class, table_strategy

    n = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    x2_map, scripts = _tables()
    strategy = table_strategy(x2_map, scripts, classify=box_class)
    # abstract o1 with an exact o2: the pair class that hid behind the
    # exact key until the v2 refutation at n = 16
    for o1, o2 in [
        ((14, 15), (14, 3)),
        ((15, 15), (14, 3)),
        ((14, 15), (14, 1)),
        ((16, 16), (13, 2)),
        ((3, 15), (14, 3)),
    ]:
        verdict, g = adaptive(strategy, n, [o1, o2])
        print(f"mixed pair o1={o1} o2={o2}: {verdict}", flush=True)
        if verdict == "DOUBLE":
            print(g.render())
            return
    for a, b in [(0, 4), (0, 3), (0, 2)]:
        for s in range(11, n - 5):
            for pair in ([(a, b + s), (a + s, b + s)], [(a, b + s), (a + s, b)]):
                if max(c for cell in pair for c in cell) >= n:
                    continue
                if all(max(cell) < 15 for cell in pair):
                    continue
                verdict, g = adaptive(strategy, n, pair)
                print(f"t=({a},{b}) s={s} pair={pair}: {verdict}", flush=True)
                if verdict == "DOUBLE":
                    print(g.render())
                    print(f"P2 threats: {g.threats(P2)}")
                    return


if __name__ == "__main__":
    main()
