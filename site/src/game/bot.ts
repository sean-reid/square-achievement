/** The first-player bot.
 *
 * Two strategies are available from 6 x 6 up: the plus rule (plus.ts),
 * a strategy stated without a table, and the general corner-box table
 * of the threshold paper (table.ts), replayed bit-for-bit. On 5 x 5 the
 * n=5 table with its quiet forks plays. Below 5 the game is a draw
 * under best play, and the bot replays an exact never-losing policy
 * (smallbot.ts). Each table is loaded on demand, so the page ships
 * only what a board size and strategy need; the rule needs no data.
 */

import { plusDecision } from "./plus";
import { Position } from "./rules";
import { loadSmallTables, smallBotDecision } from "./smallbot";
import { strategyDecision, type Decision, type StrategyTable } from "./table";

export type Strategy = "plus" | "table";

/** The strategy that actually plays on the n board: the rule applies
 * from 6 x 6 up, the tables below. */
export function effectiveStrategy(n: number, wanted: Strategy): Strategy {
  return n >= 6 ? wanted : "table";
}

let five: StrategyTable | null = null;
let general: StrategyTable | null = null;
const loads = new Map<string, Promise<void>>();

function once(key: string, load: () => Promise<void>): Promise<void> {
  let p = loads.get(key);
  if (!p) {
    p = load();
    loads.set(key, p);
  }
  return p;
}

/** Load what the n board needs under the strategy; botDecision answers
 * once it resolves. The rule needs nothing. */
export function loadTables(
  n: number,
  strategy: Strategy = "table",
): Promise<void> {
  if (n >= 6 && strategy === "plus") return Promise.resolve();
  if (n === 5) {
    return once("five", async () => {
      five = (await import("./five.json")).default as unknown as StrategyTable;
    });
  }
  if (n >= 6) {
    return once("general", async () => {
      general = (await import("./general.json"))
        .default as unknown as StrategyTable;
    });
  }
  return once("small", loadSmallTables);
}

/** Every table at once, for tests that replay many board sizes. */
export async function loadAllTables(): Promise<void> {
  await Promise.all([loadTables(2), loadTables(5), loadTables(6)]);
}

function loaded<T>(table: T | null, name: string): T {
  if (table === null) throw new Error(`${name} table not loaded`);
  return table;
}

export function botDecision(
  pos: Position,
  strategy: Strategy = "table",
): Decision {
  if (pos.n >= 6 && strategy === "plus") return plusDecision(pos);
  if (pos.n === 5) return strategyDecision(loaded(five, "five"), pos);
  if (pos.n >= 6) return strategyDecision(loaded(general, "general"), pos);
  return smallBotDecision(pos);
}

export function botMove(
  pos: Position,
  strategy: Strategy = "table",
): [number, number] {
  const d = botDecision(pos, strategy);
  if (d.move === null) throw new Error("strategy exhausted");
  return d.move;
}
