/** Exhaustive replay: the TypeScript engine must win every line, making
 * the site a third independent verifier of the strategy tables. */

import { beforeAll, describe, expect, it } from "vitest";

import { botMove, loadAllTables } from "../src/game/bot";
import { Position, threats, winningSquare } from "../src/game/rules";

/** True if the bot wins against every reply sequence from pos. */
function verifyAll(pos: Position): boolean {
  const move = botMove(pos, "table");
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

beforeAll(loadAllTables);

describe("exhaustive replay", () => {
  it("wins every line at n = 5", () => {
    expect(verifyAll(new Position(5))).toBe(true);
  }, 120_000);

  it("wins every line at n = 6", () => {
    expect(verifyAll(new Position(6))).toBe(true);
  }, 240_000);

  it("threat computation matches the reflex convention", () => {
    const pos = new Position(6);
    for (const cell of [
      [2, 2],
      [0, 0],
      [3, 2],
      [0, 1],
    ] as [number, number][]) {
      pos.play(cell);
    }
    expect(threats(pos, pos.p1)).toEqual(
      threats(pos, pos.p1)
        .slice()
        .sort((a, b) => a - b),
    );
  });
});
