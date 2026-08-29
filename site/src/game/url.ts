/** Shareable game state in the URL query: g=<n>:<i1>.<i2>...., the
 * board size and the move history as cell indices. */

export function encodeGame(n: number, history: number[]): string {
  return history.length === 0 ? `${n}` : `${n}:${history.join(".")}`;
}

export function decodeGame(
  value: string,
): { n: number; history: number[] } | null {
  const [nPart, movesPart] = value.split(":");
  const n = Number(nPart);
  if (!Number.isInteger(n) || n < 2 || n > 999) return null;
  if (!movesPart) return { n, history: [] };
  const history: number[] = [];
  for (const piece of movesPart.split(".")) {
    const i = Number(piece);
    if (!Number.isInteger(i) || i < 0 || i >= n * n) return null;
    if (history.includes(i)) return null;
    history.push(i);
  }
  return { n, history };
}
