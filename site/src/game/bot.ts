/** The first-player bot.
 *
 * From 6 x 6 up the plus rule plays (plus.ts), a strategy stated without
 * a table. On 5 x 5 the n=5 table with its branch points plays, replayed
 * bit-for-bit by table.ts. Below 5 the game is a draw under best play,
 * and the bot replays an exact never-losing policy (smallbot.ts). The
 * tables are loaded on demand, so a page ships only what a board size
 * needs; the rule needs no data.
 */

import { plusDecision } from "./plus";
import { Position } from "./rules";
import { loadSmallTables, smallBotDecision } from "./smallbot";
import { strategyDecision, type Decision, type StrategyTable } from "./table";

let five: StrategyTable | null = null;
const loads = new Map<string, Promise<void>>();

function once(key: string, load: () => Promise<void>): Promise<void> {
  let p = loads.get(key);
  if (!p) {
    p = load();
    loads.set(key, p);
  }
  return p;
}

/** Load what the n board needs; botDecision answers once it resolves. */
export function loadTables(n: number): Promise<void> {
  if (n >= 6) return Promise.resolve();
  if (n === 5) {
    return once("five", async () => {
      five = (await import("./five.json")).default as unknown as StrategyTable;
    });
  }
  return once("small", loadSmallTables);
}

/** Every table at once, for tests that replay many board sizes. */
export async function loadAllTables(): Promise<void> {
  await Promise.all([loadTables(2), loadTables(5)]);
}

function loaded<T>(table: T | null, name: string): T {
  if (table === null) throw new Error(`${name} table not loaded`);
  return table;
}

export function botDecision(pos: Position): Decision {
  if (pos.n >= 6) return plusDecision(pos);
  if (pos.n === 5) return strategyDecision(loaded(five, "five"), pos);
  return smallBotDecision(pos);
}

export function botMove(pos: Position): [number, number] {
  const d = botDecision(pos);
  if (d.move === null) throw new Error("strategy exhausted");
  return d.move;
}
