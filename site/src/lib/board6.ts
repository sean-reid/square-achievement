/** A board diagram as inline SVG, in the paper's idiom: black stones
 * the first player's, white the second player's, dashed circles the
 * threat cells, hollow squares the quiet moves, letters for labels,
 * dashed squares for the squares of a plus. The caller wraps the markup
 * in an <svg> whose <defs> declare the grid pattern `grid6p`. */

export type Cell = [number, number];

/** Cell side in SVG units; a board of size n spans n * UNIT. */
export const UNIT = 24;

export function board6(opts: {
  size?: number;
  black?: Cell[];
  white?: Cell[];
  threats?: Cell[];
  quiet?: Cell[];
  labels?: [number, number, string][];
  squares?: [number, number, number][];
}): string {
  const U = UNIT;
  const size = (opts.size ?? 6) * U;
  const parts: string[] = [];
  parts.push(
    `<rect width="${size}" height="${size}" fill="url(#grid6p)"></rect>`,
    `<rect width="${size}" height="${size}" fill="none" stroke="var(--rule)" stroke-width="0.8" opacity="0.5"></rect>`,
  );
  for (const [r, c, s] of opts.squares ?? []) {
    parts.push(
      `<rect x="${c * U + 3}" y="${r * U + 3}" width="${(s + 1) * U - 6}" height="${(s + 1) * U - 6}" fill="none" stroke="var(--accent)" stroke-width="1.4" stroke-dasharray="4 3"></rect>`,
    );
  }
  for (const [r, c] of opts.black ?? []) {
    parts.push(
      `<circle cx="${c * U + 12}" cy="${r * U + 12}" r="6.5" fill="var(--ink)"></circle>`,
    );
  }
  for (const [r, c] of opts.white ?? []) {
    parts.push(
      `<circle cx="${c * U + 12}" cy="${r * U + 12}" r="6.5" fill="var(--paper)" stroke="var(--ink)" stroke-width="1.3"></circle>`,
    );
  }
  for (const [r, c] of opts.threats ?? []) {
    parts.push(
      `<circle cx="${c * U + 12}" cy="${r * U + 12}" r="7" fill="none" stroke="var(--accent)" stroke-width="1.4" stroke-dasharray="3 2.5"></circle>`,
    );
  }
  for (const [r, c] of opts.quiet ?? []) {
    parts.push(
      `<rect x="${c * U + 6}" y="${r * U + 6}" width="12" height="12" fill="none" stroke="var(--ink)" stroke-width="1.4"></rect>`,
    );
  }
  for (const [r, c, text] of opts.labels ?? []) {
    parts.push(
      `<text x="${c * U + 12}" y="${r * U + 17}" text-anchor="middle" font-size="13" font-style="italic" fill="var(--ink)">${text}</text>`,
    );
  }
  return parts.join("");
}
