/** The plus rule, mirroring formalization/Plus/Rule.lean move for move.
 *
 * A plus is a stone we hold with the four cells at distance s along the
 * axes; each arm played makes three corners of a side-s square with the
 * centre and a neighbouring arm, so the opponent must block the
 * diagonal cell, and the last arm threatens two squares at once. A
 * tempo move is a single forcing move.
 *
 * The rule: open at (2, 2); reply below it at (3, 2), except against
 * seven first replies touching the opening pair; take a win or a block
 * by reflex; otherwise follow the line chosen at the second reply, the
 * shortest sequence of at most three tempo moves followed by a plus of
 * side 1 or 2, preferring fewer tempo moves, then fewer arms to play,
 * then the smaller plus, then cell order, and never making a threat
 * whose only block is the hidden corner of the opponent's two free
 * stones. The rule reads an abstraction of the position: our stones,
 * the opponent's stones inside the 17 x 17 base board, and the hidden
 * corner. The Python twin in pipeline/squares/plus and the fixture in
 * tests/fixtures/plus_lines.json pin this file to the Lean definition.
 */

import { Position } from "./rules";
import { farmCell, type Decision } from "./table";

export type Cell = [number, number];

export const BOX = 6;
export const BASE = 17;
export const OPENING: Cell = [2, 2];
const DEPTH = 3;

/** The abstract position the rule reads. */
export interface Abs {
  p1: Cell[];
  p2: Cell[];
  hot: Cell | null;
}

/** The line the rule commits to after the second reply. */
export interface Line {
  /** Tempo moves first, then the arms of the plus in the order played. */
  cells: Cell[];
  tempo: number;
  side: number;
  centre: Cell;
}

function same(a: Cell, b: Cell): boolean {
  return a[0] === b[0] && a[1] === b[1];
}

function has(list: readonly Cell[], c: Cell): boolean {
  return list.some((x) => same(x, c));
}

function cellLt(a: Cell, b: Cell): boolean {
  return a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
}

function cmpCell(a: Cell, b: Cell): number {
  return a[0] - b[0] || a[1] - b[1];
}

export function fmt(c: Cell): string {
  return `(${c[0]},${c[1]})`;
}

/** The second move: (3, 2) unless the first reply touches the pair. */
export function secondMove(o1: Cell): Cell {
  if (
    has(
      [
        [1, 3],
        [2, 3],
        [3, 3],
      ],
      o1,
    )
  )
    return [2, 1];
  if (
    has(
      [
        [2, 1],
        [4, 3],
      ],
      o1,
    )
  )
    return [2, 3];
  if (
    has(
      [
        [3, 1],
        [3, 2],
      ],
      o1,
    )
  )
    return [1, 2];
  return [3, 2];
}

/** Squares inside board k with corners a and b, as corner lists. */
function squaresThrough(k: number, a: Cell, b: Cell): Cell[][] {
  if (same(a, b)) return [];
  const out: Cell[][] = [];
  if (a[0] === b[0]) {
    const d = Math.abs(a[1] - b[1]);
    const c = Math.min(a[1], b[1]);
    const r = a[0];
    if (r + d < k)
      out.push([
        [r, c],
        [r, c + d],
        [r + d, c],
        [r + d, c + d],
      ]);
    if (d <= r)
      out.push([
        [r - d, c],
        [r - d, c + d],
        [r, c],
        [r, c + d],
      ]);
    return out;
  }
  if (a[1] === b[1]) {
    const d = Math.abs(a[0] - b[0]);
    const r = Math.min(a[0], b[0]);
    const c = a[1];
    if (c + d < k)
      out.push([
        [r, c],
        [r, c + d],
        [r + d, c],
        [r + d, c + d],
      ]);
    if (d <= c)
      out.push([
        [r, c - d],
        [r, c],
        [r + d, c - d],
        [r + d, c],
      ]);
    return out;
  }
  const dr = Math.abs(a[0] - b[0]);
  const dc = Math.abs(a[1] - b[1]);
  if (dr === dc) {
    const r = Math.min(a[0], b[0]);
    const c = Math.min(a[1], b[1]);
    return [
      [
        [r, c],
        [r, c + dr],
        [r + dr, c],
        [r + dr, c + dr],
      ],
    ];
  }
  return [];
}

/** Cells where mine is one stone short of a square inside board k and
 * the cell is free, in cell order. */
export function threatsIn(k: number, mine: Cell[], occ: Cell[]): Cell[] {
  const out: Cell[] = [];
  for (const a of mine) {
    for (const b of mine) {
      if (!cellLt(a, b)) continue;
      for (const sq of squaresThrough(k, a, b)) {
        const missing = sq.filter((x) => !has(mine, x));
        if (missing.length === 1) {
          const m = missing[0]!;
          if (!has(occ, m) && !has(out, m)) out.push(m);
        }
      }
    }
  }
  return out.sort(cmpCell);
}

function myThreats(p1: Cell[], occ: Cell[]): Cell[] {
  return threatsIn(BOX, p1, occ);
}

function theirThreats(p2: Cell[], occ: Cell[]): Cell[] {
  return threatsIn(BASE, p2, occ);
}

/** Play moves under forcing semantics, as the checker judges them. */
function forceLine(a: Abs, moves: Cell[]): boolean {
  let p1 = a.p1;
  let p2 = a.p2;
  for (const m of moves) {
    if (has(p1, m) || has(p2, m)) return false;
    p1 = [m, ...p1];
    if (theirThreats(p2, [...p1, ...p2]).length > 0) return false;
    const mine = myThreats(p1, [...p1, ...p2]);
    if (mine.length >= 2) return true;
    if (mine.length === 0) return false;
    const b = mine[0]!;
    if (a.hot && same(a.hot, b)) return false;
    p2 = [b, ...p2];
  }
  return false;
}

function arms(c: Cell, s: number): Cell[] {
  return [
    [c[0] - s, c[1]],
    [c[0] + s, c[1]],
    [c[0], c[1] - s],
    [c[0], c[1] + s],
  ];
}

function armsOk(c: Cell, s: number): boolean {
  return s <= c[0] && s <= c[1] && c[0] + s < BOX && c[1] + s < BOX;
}

/** All orderings, in the order of the generating pipeline. */
function permutations(xs: Cell[]): Cell[][] {
  if (xs.length === 0) return [[]];
  const out: Cell[][] = [];
  xs.forEach((x, i) => {
    const rest = xs.filter((_, j) => j !== i);
    for (const tail of permutations(rest)) out.push([x, ...tail]);
  });
  return out;
}

type PlusKey = [number, number, Cell];

interface Candidate {
  key: PlusKey;
  order: Cell[];
}

function cmpKey(a: PlusKey, b: PlusKey): number {
  return a[0] - b[0] || a[1] - b[1] || cmpCell(a[2], b[2]);
}

function cmpOrder(a: Cell[], b: Cell[]): number {
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const d = cmpCell(a[i]!, b[i]!);
    if (d !== 0) return d;
  }
  return a.length - b.length;
}

/** Every plus we can complete by force, keyed by (arms to play, side,
 * centre), sorted by key then arm order. */
function winningPluses(a: Abs): Candidate[] {
  const out: Candidate[] = [];
  for (const c of a.p1) {
    for (const s of [1, 2]) {
      if (!armsOk(c, s)) continue;
      const todo = arms(c, s).filter((x) => !has(a.p1, x));
      if (todo.length === 0 || todo.some((x) => has(a.p2, x))) continue;
      for (const order of permutations(todo)) {
        if (forceLine(a, order)) {
          out.push({ key: [todo.length, s, c], order });
          break;
        }
      }
    }
  }
  return out.sort((x, y) => cmpKey(x.key, y.key) || cmpOrder(x.order, y.order));
}

/** Single forcing moves with the block forced and not on the hidden
 * corner, in cell order, with the position after the block. */
function tempoMoves(a: Abs): [Cell, Abs][] {
  const out: [Cell, Abs][] = [];
  for (let r = 0; r < BOX; r++) {
    for (let c = 0; c < BOX; c++) {
      const m: Cell = [r, c];
      if (has(a.p1, m) || has(a.p2, m)) continue;
      const p1 = [m, ...a.p1];
      if (theirThreats(a.p2, [...p1, ...a.p2]).length > 0) continue;
      const mine = myThreats(p1, [...p1, ...a.p2]);
      if (mine.length === 1 && !(a.hot && same(a.hot, mine[0]!))) {
        out.push([m, { p1, p2: [mine[0]!, ...a.p2], hot: a.hot }]);
      }
    }
  }
  return out;
}

/** The best line within DEPTH tempo moves, or null. */
export function bestLine(a: Abs): Line | null {
  let frontier: [Abs, Cell[]][] = [[a, []]];
  for (let d = 0; d <= DEPTH; d++) {
    let best: { key: PlusKey; cells: Cell[] } | null = null;
    for (const [b, pre] of frontier) {
      if (theirThreats(b.p2, [...b.p1, ...b.p2]).length > 0) continue;
      const pl = winningPluses(b);
      if (pl.length > 0) {
        const { key, order } = pl[0]!;
        if (best === null || cmpKey(key, best.key) < 0) {
          best = { key, cells: [...pre, ...order] };
        }
      }
    }
    if (best !== null) {
      return {
        cells: best.cells,
        tempo: d,
        side: best.key[1],
        centre: best.key[2],
      };
    }
    if (d === DEPTH) return null;
    const next: [Abs, Cell[]][] = [];
    for (const [b, pre] of frontier) {
      for (const [m, b2] of tempoMoves(b)) next.push([b2, [...pre, m]]);
    }
    if (next.length === 0) return null;
    frontier = next;
  }
  return null;
}

function cells(pos: Position, stones: Set<number>): Cell[] {
  return [...stones]
    .sort((a, b) => a - b)
    .map((i) => {
      const [r, c] = pos.cell(i);
      return [r, c];
    });
}

/** The abstraction of the position: our stones, the opponent's stones
 * inside the base board, and the hidden corner of the free pair. */
export function abstractOf(pos: Position): Abs {
  const p2 = cells(pos, pos.p2).filter((x) => x[0] < BASE && x[1] < BASE);
  let hot: Cell | null = null;
  if (pos.history.length >= 4) {
    const o1 = pos.cell(pos.history[1]!);
    const o2 = pos.cell(pos.history[3]!);
    hot = farmCell(BOX, [o1[0], o1[1]], [o2[0], o2[1]]);
  }
  return { p1: cells(pos, pos.p1), p2, hot };
}

const lines = new Map<string, Line | null>();

/** The line committed to at the second reply, from the two free
 * replies; memoized, since the abstraction at that point is a function
 * of the pair alone. */
export function lineOf(pos: Position): Line | null {
  if (pos.history.length < 4) return null;
  const o1 = pos.cell(pos.history[1]!);
  const o2 = pos.cell(pos.history[3]!);
  const x2 = secondMove([o1[0], o1[1]]);
  if (!same(pos.cell(pos.history[2]!) as Cell, x2)) return null;
  if (!same(pos.cell(pos.history[0]!) as Cell, OPENING)) return null;
  const k = `${o1[0]},${o1[1]}|${o2[0]},${o2[1]}`;
  let line = lines.get(k);
  if (line === undefined) {
    const root = new Position(
      Math.max(pos.n, BASE + 1, o1[0] + 1, o1[1] + 1, o2[0] + 1, o2[1] + 1),
    );
    root.play(OPENING);
    root.play([o1[0], o1[1]]);
    root.play(x2);
    root.play([o2[0], o2[1]]);
    line = bestLine(abstractOf(root));
    lines.set(k, line);
  }
  return line;
}

export interface PlusDecision extends Decision {
  reason: string;
  /** The committed line, once there is one. */
  line: Line | null;
  /** How many of the line's cells we already hold. */
  played: number;
  hot: Cell | null;
}

function list(cs: Cell[]): string {
  return cs.map(fmt).join(" and ");
}

/** The rule's move for the position (P1 to move), with its reason. */
export function plusDecision(pos: Position): PlusDecision {
  const a = abstractOf(pos);
  const occ = [...a.p1, ...a.p2];
  const base = { line: null as Line | null, played: 0, hot: a.hot };
  const mine = myThreats(a.p1, occ);
  if (mine.length > 0) {
    return {
      ...base,
      move: mine[0]!,
      source: "win",
      reason: "completes a square",
    };
  }
  const theirs = theirThreats(a.p2, occ);
  if (theirs.length > 0) {
    return {
      ...base,
      move: theirs[0]!,
      source: "block",
      reason: `blocks your threat at ${fmt(theirs[0]!)}`,
    };
  }
  if (pos.history.length === 0) {
    return { ...base, move: OPENING, source: "opening", reason: "the opening" };
  }
  const o1r = pos.cell(pos.history[1]!);
  const o1: Cell = [o1r[0], o1r[1]];
  const x2 = secondMove(o1);
  if (!has(a.p1, x2)) {
    const reason = same(x2, [3, 2])
      ? "the second move, below the opening"
      : `the second move; ${fmt(o1)} is one of the seven exceptions`;
    return { ...base, move: x2, source: "second", reason };
  }
  const line = lineOf(pos);
  if (line === null) {
    return { ...base, move: null, source: "exhausted", reason: "no line" };
  }
  const played = line.cells.filter((c) => has(a.p1, c)).length;
  const idx = line.cells.findIndex((c) => !has(a.p1, c));
  if (idx < 0) {
    return {
      ...base,
      line,
      played,
      move: null,
      source: "exhausted",
      reason: "line exhausted",
    };
  }
  const move = line.cells[idx]!;
  const after = myThreats([move, ...a.p1], [move, ...occ]);
  const armCount = line.cells.length - line.tempo;
  let reason: string;
  let source: Decision["source"];
  if (idx < line.tempo) {
    source = "tempo";
    reason = `tempo move ${idx + 1} of ${line.tempo}: threatens ${list(after)}, so the reply is forced`;
  } else {
    source = "arm";
    const j = idx - line.tempo + 1;
    const plus = `the side-${line.side} plus at ${fmt(line.centre)}`;
    reason =
      after.length >= 2
        ? `last arm of ${plus}: threatens ${list(after)}, and no single block answers both`
        : `arm ${j} of ${armCount} of ${plus}: threatens ${list(after)}`;
  }
  return { ...base, line, played, move, source, reason };
}
