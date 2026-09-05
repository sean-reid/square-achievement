"""Replay a failing line against the general table and narrate it.

python3 -m squares.threshold.diagnose n r,c r,c ...   (the move list, P1 first)
"""

import sys

from .. import P1, P2, Game
from .forcing import box_class


def narrate(moves, n):
    from .audit_farms import _tables

    x2_map, scripts = _tables()
    g = Game(n)
    opening = (2, 2)

    def describe(cell, table):
        if cell in table:
            return f"exact {cell}"
        cls = box_class(cell)
        if cls is not None and cls in table:
            return f"class {cls}"
        return "default"

    for i, cell in enumerate(moves):
        player = P1 if i % 2 == 0 else P2
        if player == P1:
            note = ""
            if g.threats(P1):
                note = f"win reflex, threats {g.threats(P1)}"
            elif g.threats(P2):
                note = f"block reflex, P2 threats {g.threats(P2)}"
            elif not g.my_moves:
                note = "opening"
            else:
                o1 = g.reply_to(opening)
                x2 = x2_map.get(o1) or x2_map.get(box_class(o1)) or x2_map.get(None)
                if x2 not in g.p1:
                    note = f"x2 via {describe(o1, x2_map)}"
                else:
                    o2 = g.reply_to(x2)
                    table = scripts.get(o1) or scripts.get(box_class(o1)) or scripts.get(None)
                    entry = table.get(o2) or table.get(box_class(o2)) or table.get(None)
                    note = (
                        f"entry: o1 {describe(o1, scripts)}, "
                        f"o2 {describe(o2, table)} -> {entry}"
                    )
            print(f"{i:2} P1 {cell}  [{note}]")
        else:
            comp = g.completes(cell, P2)
            print(f"{i:2} P2 {cell}{'  COMPLETES A SQUARE' if comp else ''}")
        g.play(player, cell)
        if g.wins(player):
            print(f"   -> {'P1' if player == P1 else 'P2'} wins here")
            break
    print()
    print(g.render())
    print()
    print(f"final threats: P1 {g.threats(P1)}  P2 {g.threats(P2)}")


def main():
    n = int(sys.argv[1])
    moves = [tuple(int(v) for v in arg.split(",")) for arg in sys.argv[2:]]
    narrate(moves, n)


if __name__ == "__main__":
    main()
