/** The results the site presents, one entry per paper. Each has a
 * landing page at /<slug>/, a proof guide at /<slug>/proof/, a PDF at
 * downloads/<slug>.pdf, and a Lean library named after it. */

export interface Result {
  slug: string;
  title: string;
  statement: string;
  lean: string;
}

export const results: Result[] = [
  {
    slug: "threshold",
    title: "The winning threshold",
    statement:
      "The first player has a winning strategy if and only if n ≥ 5, and every smaller board is drawn under optimal play. One explicit strategy wins every board from 6 × 6 up, and the proof is machine-checked for all n at once.",
    lean: "Threshold library, theorem outcome",
  },
];
