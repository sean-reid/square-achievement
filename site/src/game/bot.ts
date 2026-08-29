/** The first-player bot.
 *
 * On boards of size 5 and up it replays the strategy tables from the
 * proof pipeline bit-for-bit (see table.ts): the n=5 table with its
 * quiet forks, the general corner-box table for n >= 6. Below 5 the
 * game is a draw under best play; the bot plays reflexes plus the
 * first free cell until the exact small-board player lands.
 */

import { Position, threats } from "./rules";
import { strategyDecision, type Decision, type StrategyTable } from "./table";
import tablesJson from "./tables.json";

const tables = tablesJson as unknown as {
  general: StrategyTable;
  five: StrategyTable;
};

/** True once the tables' verification status is final. */
export const VERIFIED = false;

export function botDecision(pos: Position): Decision {
  if (pos.n === 5) return strategyDecision(tables.five, pos);
  if (pos.n >= 6) return strategyDecision(tables.general, pos);
  const mine = threats(pos, pos.p1);
  if (mine.length > 0) {
    const [r, c] = pos.cell(mine[0]!);
    return { move: [r, c], source: "win" };
  }
  const theirs = threats(pos, pos.p2);
  if (theirs.length > 0) {
    const [r, c] = pos.cell(theirs[0]!);
    return { move: [r, c], source: "block" };
  }
  for (let i = 0; i < pos.n * pos.n; i++) {
    if (!pos.occupied(i)) {
      const [r, c] = pos.cell(i);
      return { move: [r, c], source: "plan" };
    }
  }
  return { move: null, source: "exhausted" };
}

export function botMove(pos: Position): [number, number] {
  const d = botDecision(pos);
  if (d.move === null) throw new Error("strategy exhausted");
  return d.move;
}
