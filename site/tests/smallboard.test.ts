/** Exhaustive replay of the small-board drawing policy: the bot must
 * never lose on the boards below n = 5, where no win exists. */

import { describe, expect, it } from "vitest";

import { botMove } from "../src/game/bot";
import { Position, winningSquare } from "../src/game/rules";

/** True if the bot never loses against any reply sequence from pos. */
function neverLoses(pos: Position): boolean {
  const move = botMove(pos);
  const won = winningSquare(pos, new Set([...pos.p1, pos.idx(move)]), move);
  pos.play(move);
  try {
    if (won || pos.full()) return true;
    for (let i = 0; i < pos.n * pos.n; i++) {
      if (pos.occupied(i)) continue;
      const reply = pos.cell(i);
      const replyWins = winningSquare(pos, new Set([...pos.p2, i]), reply);
      pos.play(reply);
      try {
        if (replyWins) return false;
        if (!pos.full() && !neverLoses(pos)) return false;
      } finally {
        pos.undo();
      }
    }
    return true;
  } finally {
    pos.undo();
  }
}

describe("small boards", () => {
  it("never loses at n = 2", () => {
    expect(neverLoses(new Position(2))).toBe(true);
  });

  it("never loses at n = 3", () => {
    expect(neverLoses(new Position(3))).toBe(true);
  });

  it("never loses at n = 4", () => {
    expect(neverLoses(new Position(4))).toBe(true);
  }, 120_000);

  it("blocks the fork the filler bot fell to", () => {
    // X fills the top row while O builds (1,1),(1,2),(2,0),(2,1); the
    // old filler bot then faced threats at both (1,0) and (2,2).
    const pos = new Position(4);
    const oMoves: [number, number][] = [
      [1, 1],
      [1, 2],
      [2, 0],
      [2, 1],
    ];
    for (const oMove of oMoves) {
      pos.play(botMove(pos));
      if (pos.occupied(pos.idx(oMove))) break;
      pos.play(oMove);
    }
    expect(neverLoses(pos)).toBe(true);
  });
});
