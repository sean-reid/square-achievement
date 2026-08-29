/** The first-player bot.
 *
 * Reflexes first, exactly as in the verified strategy: complete a
 * square when possible, block the opponent's completion otherwise,
 * both at the lexicographically least cell. The plan below the
 * reflexes is a placeholder until the verified strategy table is
 * exported from the proof pipeline; until then VERIFIED stays false
 * and the UI says so.
 */

import { Position, threats } from "./rules";

export const VERIFIED = false;

export function botMove(pos: Position): [number, number] {
  const mine = threats(pos, pos.p1);
  if (mine.length > 0) return pos.cell(mine[0]!);
  const theirs = threats(pos, pos.p2);
  if (theirs.length > 0) return pos.cell(theirs[0]!);
  // placeholder plan: the corner-box scaffold the real table also uses
  const plan: [number, number][] = [
    [2, 2],
    [3, 2],
    [2, 1],
    [1, 1],
    [2, 3],
    [4, 3],
    [2, 5],
  ];
  for (const cell of plan) {
    if (pos.onBoard(cell) && !pos.occupied(pos.idx(cell))) return cell;
  }
  for (let i = 0; i < pos.n * pos.n; i++) {
    if (!pos.occupied(i)) return pos.cell(i);
  }
  throw new Error("board is full");
}
