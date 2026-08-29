/** Rules of the square achievement game.
 *
 * Cells are [row, col] on an n x n board. A player wins by holding all
 * four corners of an axis-aligned square of any side length, 2x2 blocks
 * included. Cells are encoded as r * n + c inside a game for speed.
 */

export type Cell = readonly [number, number];

export class Position {
  readonly n: number;
  readonly p1: Set<number> = new Set();
  readonly p2: Set<number> = new Set();
  readonly history: number[] = [];

  constructor(n: number) {
    this.n = n;
  }

  idx(cell: Cell): number {
    return cell[0] * this.n + cell[1];
  }

  cell(idx: number): Cell {
    return [Math.floor(idx / this.n), idx % this.n];
  }

  onBoard(cell: Cell): boolean {
    const [r, c] = cell;
    return r >= 0 && c >= 0 && r < this.n && c < this.n;
  }

  occupied(idx: number): boolean {
    return this.p1.has(idx) || this.p2.has(idx);
  }

  /** Play for the side whose turn it is (P1 on even plies). */
  play(cell: Cell): void {
    const i = this.idx(cell);
    if (!this.onBoard(cell) || this.occupied(i)) {
      throw new Error(`illegal move ${cell}`);
    }
    (this.history.length % 2 === 0 ? this.p1 : this.p2).add(i);
    this.history.push(i);
  }

  undo(): void {
    const i = this.history.pop();
    if (i === undefined) return;
    (this.history.length % 2 === 0 ? this.p1 : this.p2).delete(i);
  }

  p1ToMove(): boolean {
    return this.history.length % 2 === 0;
  }

  full(): boolean {
    return this.history.length === this.n * this.n;
  }
}

/** The four corners of the square anchored at (r, c) with side s. */
export function corners(n: number, r: number, c: number, s: number): number[] {
  return [r * n + c, r * n + c + s, (r + s) * n + c, (r + s) * n + c + s];
}

/** The completed square through the last-placed cell, if any. */
export function winningSquare(
  pos: Position,
  stones: Set<number>,
  last: Cell,
): number[] | null {
  const n = pos.n;
  const [lr, lc] = last;
  for (let s = 1; s < n; s++) {
    for (const [r, c] of [
      [lr, lc],
      [lr, lc - s],
      [lr - s, lc],
      [lr - s, lc - s],
    ]) {
      if (r < 0 || c < 0 || r + s >= n || c + s >= n) continue;
      const sq = corners(n, r, c, s);
      if (sq.every((i) => stones.has(i))) return sq;
    }
  }
  return null;
}

/** Empty cells completing a square for `stones`, ascending. */
export function threats(pos: Position, stones: Set<number>): number[] {
  const n = pos.n;
  const out = new Set<number>();
  for (let s = 1; s < n; s++) {
    for (let r = 0; r + s < n; r++) {
      for (let c = 0; c + s < n; c++) {
        const sq = corners(n, r, c, s);
        const missing = sq.filter((i) => !stones.has(i));
        if (missing.length === 1 && !pos.occupied(missing[0]!)) {
          out.add(missing[0]!);
        }
      }
    }
  }
  return [...out].sort((a, b) => a - b);
}
