/** The first-player bot.
 *
 * On boards of size 5 and up it replays the strategy tables from the
 * proof pipeline bit-for-bit (see table.ts): the n=5 table with its
 * quiet forks, the general corner-box table for n >= 6. Below 5 the
 * game is a draw under best play, and the bot replays an exact
 * never-losing policy (see smallbot.ts).
 */

import { Position } from "./rules";
import { smallBotDecision } from "./smallbot";
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
  return smallBotDecision(pos);
}

export function botMove(pos: Position): [number, number] {
  const d = botDecision(pos);
  if (d.move === null) throw new Error("strategy exhausted");
  return d.move;
}
