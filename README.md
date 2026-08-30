# The Square Achievement Game on n x n Boards

Landing page, playable strategy, paper, formalization, and generation
pipeline for the square achievement game: two players alternate
claiming cells of an n x n grid, and the first to hold all four
corners of an axis-aligned square wins. The first player wins exactly
when n >= 5, by a machine-checked strategy.

## Layout

- `site/` the landing page: a long-form article with the playable game
  (the bot plays the verified first-player strategy), the history, the
  strategy, and downloads. Astro, statically built; the deploy also
  packages the paper PDF and the formalization tarball.
- `paper/` the LaTeX source of the methods paper; CI builds the PDF.
- `formalization/` the Lean 4 development: game semantics, checkers
  with machine-checked soundness, and the strategy tables as data.
- `pipeline/` the Python side: table generation, the exhaustive
  reference verifier, exporters for the site and the formalization,
  and the analysis tools.

## Develop

Site: `cd site && npm install && npm run dev` (Node 22, from
[nodejs.org](https://nodejs.org) or a version manager); `npm test`
for unit tests, `npm run e2e` for Playwright, after a one-time
`npx playwright install`. Paper: `cd paper &&
latexmk -pdf main.tex` (any TeX Live with amsart, tikz, algorithm).
Formalization: `cd formalization && lake exe cache get && lake build`;
see `formalization/README.md` for the Linux environment note, the
expected build time, and the commands reproducing the paper's Table 1.
Pipeline: Python 3.11+, no third-party dependencies at runtime;
`cd pipeline && uv run --with pytest python -m pytest squares/tests`.
Commands assume a POSIX shell; on Windows, work inside WSL.

Licensing: code MIT; paper text and figures CC BY 4.0.
