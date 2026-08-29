import { describe, expect, it } from "vitest";

import { Position, threats, winningSquare } from "../src/game/rules";
import { botMove } from "../src/game/bot";

function place(pos: Position, moves: [number, number][]): void {
  for (const m of moves) pos.play(m);
}

describe("rules", () => {
  it("detects a 2x2 block win", () => {
    const pos = new Position(4);
    place(pos, [
      [0, 0],
      [3, 3],
      [0, 1],
      [3, 2],
      [1, 0],
      [2, 3],
      [1, 1],
    ]);
    expect(winningSquare(pos, pos.p1, [1, 1])).not.toBeNull();
  });

  it("detects a side-2 square win", () => {
    const pos = new Position(5);
    place(pos, [
      [0, 0],
      [4, 4],
      [0, 2],
      [4, 3],
      [2, 0],
      [3, 4],
      [2, 2],
    ]);
    expect(winningSquare(pos, pos.p1, [2, 2])).not.toBeNull();
  });

  it("finds the threat cell", () => {
    const pos = new Position(5);
    place(pos, [
      [0, 0],
      [4, 4],
      [0, 2],
      [4, 3],
      [2, 0],
    ]);
    expect(threats(pos, pos.p1)).toEqual([pos.idx([2, 2])]);
  });

  it("threats exclude occupied completion cells", () => {
    const pos = new Position(5);
    place(pos, [
      [0, 0],
      [2, 2],
      [0, 2],
      [4, 4],
      [2, 0],
    ]);
    expect(threats(pos, pos.p1)).toEqual([]);
  });
});

describe("bot reflexes", () => {
  it("completes a square when it can", () => {
    const pos = new Position(5);
    place(pos, [
      [0, 0],
      [4, 4],
      [0, 2],
      [4, 3],
      [2, 0],
      [3, 3],
    ]);
    expect(botMove(pos)).toEqual([2, 2]);
  });

  it("blocks the opponent's completion", () => {
    const pos = new Position(6);
    place(pos, [
      [2, 2],
      [0, 0],
      [5, 5],
      [0, 1],
      [4, 5],
      [1, 0],
    ]);
    expect(botMove(pos)).toEqual([1, 1]);
  });
});
