"""Write paper/claims.tex, every number the paper quotes, as LaTeX macros.

Counts come from the pipeline itself: the rule's lines per board from
squares.plus.measure, the lines on the anchor board and in the anchored
positions from the same rule, the anchored positions from squares.plus.sweep,
the 5 x 5 table's branches from its module, and the line count of the
Lean rule. Values that come from long runs are read from
paper/data/recorded.json and paper/data/timings.json, the latter
written by squares.paper.timings.

python3 -m squares.paper.claims   writes paper/claims.tex
"""

import json

from ..five import strategy5
from ..paths import REPO
from ..plus.measure import line_with_key, measure, played
from ..plus.rule import OPENING, abstract_of, my_threats, second_move, their_threats
from ..plus.sweep import anchors

PAPER = REPO / "paper"
LEAN = REPO / "formalization" / "SquareAchievement"
WORDS = {
    5: "Five",
    6: "Six",
    7: "Seven",
    8: "Eight",
    9: "Nine",
    10: "Ten",
    11: "Eleven",
    12: "Twelve",
    13: "Thirteen",
    14: "Fourteen",
    15: "Fifteen",
    16: "Sixteen",
    17: "Seventeen",
    23: "Anchor",
}


def group(n):
    """1234567 -> 1{,}234{,}567, the paper's thousands separator."""
    return "{,}".join(f"{n:,}".split(","))


def seconds(x):
    """A wall-clock time in seconds, one decimal below ten."""
    return f"{x:.1f}" if x < 10 else f"{round(x)}"


def line_played(a):
    """The line the rule plays from the abstraction a against blocks."""
    line, _, _ = line_with_key(a)
    return tuple(played(a, line))


def lines_by_abstraction(n):
    """Every distinct abstraction of a reply pair on the n board, with its line."""
    cells = [(r, c) for r in range(n) for c in range(n)]
    out = {}
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
            key = (tuple(sorted(a.p1)), tuple(sorted(a.p2)), a.hot)
            if key not in out:
                out[key] = line_played(a)
    return out


def anchored_lines():
    """The line the rule plays from each anchored position."""
    out = []
    for o1, o2, hot in anchors():
        a = abstract_of([OPENING, second_move(o1)], [o1, o2], o1, o2)
        assert a.hot == hot
        out.append(line_played(a))
    return out


def blocks_that_threaten(n):
    """Reply pairs on the n board whose line has a block that gives the
    second player a threat, which the next tempo move must then take."""
    cells = [(r, c) for r in range(n) for c in range(n)]
    count = 0
    for o1 in cells:
        if o1 == OPENING:
            continue
        x2 = second_move(o1)
        for o2 in cells:
            if o2 in (OPENING, o1, x2):
                continue
            a = abstract_of([OPENING, x2], [o1, o2], o1, o2)
            line, tempo, _ = line_with_key(a)
            p1, p2 = list(a.p1), list(a.p2)
            hit = False
            for j, m in enumerate(line):
                p1 = [m] + p1
                mine = my_threats(p1, p1 + p2)
                if len(mine) >= 2:
                    break
                p2 = mine + p2
                threats = their_threats(p2, p1 + p2)
                if threats:
                    assert j < tempo and threats == [line[j + 1]]
                    hit = True
            count += hit
            if hit:
                assert tempo == 3
    return count


def latest_ply(lines):
    """The ply of the win when the double threat ends the longest line."""
    return max(2 * len(line) + 5 for line in lines)


def build_claims():
    """The macro table, name to LaTeX value."""
    recorded = json.loads((PAPER / "data" / "recorded.json").read_text())
    timings = json.loads((PAPER / "data" / "timings.json").read_text())
    out = {}
    six = measure(6)
    for n in range(6, 18):
        m = six if n == 6 else measure(n)
        out[f"pairs{WORDS[n]}"] = group(m["roots"])
        if n == 17:
            out["tempoZeroSeventeen"] = group(m["tempo"][0])
            out["tempoOneSeventeen"] = group(m["tempo"][1])
        assert m["lines"] == six["lines"] and m["max_plies"] == six["max_plies"]
        assert m["tempo"][2] == six["tempo"][2] and m["tempo"][3] == six["tempo"][3]
        # the paper says side-1 lines are exactly the lines with no tempo move
        assert m["sides"][1] == m["tempo"][0]
    out["pairsAnchor"] = group((23 * 23 - 1) * (23 * 23 - 3))
    six_lines = set(lines_by_abstraction(6).values())
    anchor = lines_by_abstraction(23)
    assert len(six_lines) == six["lines"] and latest_ply(six_lines) == six["max_plies"]
    assert set(anchor.values()) == six_lines and set(anchored_lines()) <= six_lines
    out["anchorAbstractions"] = group(len(anchor))
    out["blocksThatThreaten"] = str(blocks_that_threaten(6))
    out["distinctLines"] = str(six["lines"])
    for d in range(4):
        out[f"tempo{['Zero', 'One', 'Two', 'Three'][d]}"] = group(six["tempo"][d])
    out["longestLineMoves"] = str(len(six["longest"][2]))
    out["latestPly"] = str(six["max_plies"])
    out["anchoredPositions"] = str(len(anchors()))
    out["fiveTablePositions"] = recorded["five_positions_solved"]
    out["fiveTableBranches"] = str(len(strategy5.X2))
    out["fiveNoForcing"] = str(recorded["five_no_forcing"])
    rule_lines = len((LEAN / "Plus" / "Rule.lean").read_text().splitlines())
    out["ruleLeanLines"] = str(round(rule_lines, -1))
    for key, secs in timings.items():
        if key == "anchored":
            out["timeAnchored"] = f"{secs:.2f}"
        else:
            out[f"time{WORDS[int(key)]}"] = seconds(secs)
    out["buildMinutes"] = str(recorded["build_minutes"])
    return out


def render(claims):
    head = "% Generated by python3 -m squares.paper.claims; do not edit.\n"
    return head + "".join(f"\\newcommand{{\\{k}}}{{{v}}}\n" for k, v in claims.items())


def main():
    path = PAPER / "claims.tex"
    path.write_text(render(build_claims()))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
