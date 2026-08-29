/** Exact drawing policy for the boards below n = 5.
 *
 * No first-player win exists there, so the bot's job is to never
 * lose. The tables hold the quiet-node moves of a policy solved
 * offline; wins and single-threat blocks stay with the reflexes,
 * mirroring the big tables' replay. The offline extraction walks
 * every reply sequence, so the shipped table is verified to never
 * lose from the empty board.
 */

import { Position, threats } from "./rules";
import type { Decision } from "./table";
import smallJson from "./small_tables.json";

const tables = smallJson as unknown as Record<
  string,
  Record<string, [number, number]>
>;

function mask(stones: Set<number>): number {
  let m = 0;
  for (const i of stones) m |= 1 << i;
  return m;
}

export function smallBotDecision(pos: Position): Decision {
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
  const key = `${mask(pos.p1)},${mask(pos.p2)}`;
  const entry = tables[String(pos.n)]?.[key];
  if (entry !== undefined) {
    return {
      move: entry,
      source: pos.history.length === 0 ? "opening" : "plan",
    };
  }
  // off-policy positions (shared or hand-built) fall back to filler
  for (let i = 0; i < pos.n * pos.n; i++) {
    if (!pos.occupied(i)) {
      const [r, c] = pos.cell(i);
      return { move: [r, c], source: "plan" };
    }
  }
  return { move: null, source: "exhausted" };
}
