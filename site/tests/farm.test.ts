/** The farm branch that refuted the earlier table at n = 16: the far
 * pair (0,15), (12,3) selects a farm entry, and the bot must win every
 * continuation of that branch. */

import { describe, expect, it } from "vitest";

import { botMove } from "../src/game/bot";
import { Position, winningSquare } from "../src/game/rules";

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

describe("farm branches at n = 16", () => {
  for (const o2 of [
    [12, 3],
    [12, 15],
    [15, 15],
  ] as [number, number][]) {
    it(`wins the branch o1=(0,15) o2=(${o2})`, () => {
      const pos = new Position(16);
      expect(botMove(pos)).toEqual([2, 2]);
      pos.play([2, 2]);
      pos.play([0, 15]);
      expect(botMove(pos)).toEqual([3, 2]);
      pos.play([3, 2]);
      pos.play(o2);
      expect(verifyAll(pos)).toBe(true);
    }, 60_000);
  }
});
