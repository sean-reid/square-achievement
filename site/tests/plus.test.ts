/** The plus rule against the pipeline's fixture and by exhaustive replay:
 * the TypeScript rule must choose the same lines as the Python twin and
 * the Lean definition, and win every game on the 6 board. */

import { describe, expect, it } from "vitest";

import { botMove } from "../src/game/bot";
import { lineOf, plusDecision, secondMove } from "../src/game/plus";
import { Position, winningSquare } from "../src/game/rules";
import fixture from "./fixtures/plus_lines.json";

interface Entry {
  n: number;
  o1: [number, number];
  o2: [number, number];
  x2: [number, number];
  hot: [number, number] | null;
  line: [number, number][];
  tempo: number;
  side: number;
  centre: [number, number];
}

const entries = fixture as Entry[];

function rootOf(e: Entry): Position {
  const pos = new Position(e.n);
  pos.play([2, 2]);
  pos.play(e.o1);
  pos.play(e.x2);
  pos.play(e.o2);
  return pos;
}

/** True if the rule wins against every reply sequence from pos. */
function verifyAll(pos: Position): boolean {
  const move = botMove(pos);
  const won = winningSquare(pos, new Set([...pos.p1, pos.idx(move)]), move);
  pos.play(move);
  try {
    if (won) return true;
    if (pos.full()) return false;
    for (let i = 0; i < pos.n * pos.n; i++) {
      if (pos.occupied(i)) continue;
      const reply = pos.cell(i);
      const replyWins = winningSquare(pos, new Set([...pos.p2, i]), reply);
      pos.play(reply);
      try {
        if (replyWins) return false;
        if (pos.full()) return false;
        if (!verifyAll(pos)) return false;
      } finally {
        pos.undo();
      }
    }
    return true;
  } finally {
    pos.undo();
  }
}

describe("the plus rule", () => {
  it("has the pipeline's second-move diagram", () => {
    for (const e of entries) expect(secondMove(e.o1)).toEqual(e.x2);
    expect(secondMove([14, 14])).toEqual([3, 2]);
  });

  it("commits to the pipeline's line on every fixture position", () => {
    expect(entries.length).toBeGreaterThan(1300);
    for (const e of entries) {
      const line = lineOf(rootOf(e));
      expect(line, `${e.o1} ${e.o2}`).not.toBeNull();
      expect(line!.cells).toEqual(e.line);
      expect(line!.tempo).toBe(e.tempo);
      expect(line!.side).toBe(e.side);
      expect(line!.centre).toEqual(e.centre);
      expect(plusDecision(rootOf(e)).hot).toEqual(e.hot);
    }
  });

  it("explains its moves", () => {
    const pos = rootOf({
      n: 6,
      o1: [0, 0],
      o2: [4, 4],
      x2: [3, 2],
      hot: null,
      line: [],
      tempo: 0,
      side: 1,
      centre: [2, 2],
    });
    const d = plusDecision(pos);
    expect(d.move).toEqual([2, 1]);
    expect(d.source).toBe("arm");
    expect(d.reason).toContain("side-1 plus at (2,2)");
    expect(d.reason).toContain("(3,1)");
  });

  it("wins every line at n = 6", () => {
    expect(verifyAll(new Position(6))).toBe(true);
  }, 240_000);
});
