import { describe, expect, it } from "vitest";

import { decodeGame, encodeGame } from "../src/game/url";

describe("game url codec", () => {
  it("round-trips a game", () => {
    const encoded = encodeGame(7, [24, 0, 31]);
    expect(decodeGame(encoded)).toEqual({ n: 7, history: [24, 0, 31] });
  });

  it("round-trips an empty game", () => {
    expect(decodeGame(encodeGame(5, []))).toEqual({ n: 5, history: [] });
  });

  it("rejects malformed values", () => {
    expect(decodeGame("abc")).toBeNull();
    expect(decodeGame("5:99")).toBeNull();
    expect(decodeGame("5:1.1")).toBeNull();
    expect(decodeGame("1")).toBeNull();
  });
});
