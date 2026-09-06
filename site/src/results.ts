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
  {
    slug: "plus",
    title: "A short winning rule",
    statement:
      "A strategy for every board from 6 × 6 up stated as a rule with no lookup table: open at (2,2), take completions and blocks, and otherwise follow the shortest line of at most three forcing moves ending in the arms of a plus. It wins by the seventeenth ply, and the Lean theorem says the rule's own play wins.",
    lean: "Plus library, theorem plus_wins_with",
  },
];
