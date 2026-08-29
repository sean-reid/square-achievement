/** Bit-exact replay of the strategy tables.
 *
 * Mirrors the certificate checker's semantics move for move: reflexes
 * at the lexicographically least cell, then the lookup chain (exact
 * key, alignment class, default), then the first unplayed plan cell,
 * with quiet forks resolved against the reply to their own move. Every
 * move reports its decision source, which also drives annotations.
 */

import { Position, threats } from "./rules";

export type Entry =
  [number, number][] | { q: [number, number]; b: Record<string, Entry> };

export interface StrategyTable {
  opening: [number, number];
  box: number;
  x2: Record<string, [number, number]>;
  scripts: Record<string, Record<string, Entry>>;
}

export type Source =
  "win" | "block" | "opening" | "second" | "plan" | "exhausted";

export interface Decision {
  move: [number, number] | null;
  source: Source;
}

function cellKey(cell: [number, number]): string {
  return `${cell[0]},${cell[1]}`;
}

function classKey(box: number, cell: [number, number]): string | null {
  const [r, c] = cell;
  if (r < box && c >= box) return `row:${r}`;
  if (c < box && r >= box) return `col:${c}`;
  return null;
}

function lookup<T>(
  box: number,
  rec: Record<string, T>,
  cell: [number, number],
): T | undefined {
  const exact = rec[cellKey(cell)];
  if (exact !== undefined) return exact;
  const cls = classKey(box, cell);
  if (cls !== null && rec[cls] !== undefined) return rec[cls];
  return rec["*"];
}

function replyTo(
  pos: Position,
  cell: [number, number],
): [number, number] | null {
  const i = pos.history.indexOf(pos.idx(cell));
  if (i < 0 || i + 1 >= pos.history.length) return null;
  const [r, c] = pos.cell(pos.history[i + 1]!);
  return [r, c];
}

function resolveEntry(
  table: StrategyTable,
  pos: Position,
  entry: Entry,
): [number, number] | null {
  let current: Entry | undefined = entry;
  for (let fuel = pos.history.length + 1; fuel > 0 && current; fuel--) {
    if (Array.isArray(current)) {
      for (const cell of current) {
        if (!pos.p1.has(pos.idx(cell))) return cell;
      }
      return null;
    }
    const move: [number, number] = current.q;
    if (!pos.p1.has(pos.idx(move))) return move;
    const reply = replyTo(pos, move);
    if (reply === null) return null;
    current = lookup(table.box, current.b, reply);
  }
  return null;
}

/** The strategy's move for the position (P1 to move). */
export function strategyDecision(
  table: StrategyTable,
  pos: Position,
): Decision {
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
  if (pos.history.length === 0) {
    return { move: table.opening, source: "opening" };
  }
  const o1raw = pos.cell(pos.history[1]!);
  const o1: [number, number] = [o1raw[0], o1raw[1]];
  const second = lookup(table.box, table.x2, o1);
  if (second === undefined) return { move: null, source: "exhausted" };
  if (!pos.p1.has(pos.idx(second))) return { move: second, source: "second" };
  const o2 = replyTo(pos, second);
  if (o2 === null) return { move: null, source: "exhausted" };
  const entries = lookup(table.box, table.scripts, o1);
  if (entries === undefined) return { move: null, source: "exhausted" };
  const entry = lookup(table.box, entries, o2);
  if (entry === undefined) return { move: null, source: "exhausted" };
  const move = resolveEntry(table, pos, entry);
  return move ? { move, source: "plan" } : { move: null, source: "exhausted" };
}
