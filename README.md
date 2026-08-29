# The Square Achievement Game on n x n Boards

Landing page, playable strategy, paper, and formalization for the square
achievement game: two players alternate claiming cells of an n x n grid,
and the first to hold all four corners of an axis-aligned square wins.
The first player wins exactly when n >= 5, by a machine-checked strategy.

## Layout

- `site/` the landing page: a long-form article with the playable game
  (you are O, the bot plays the verified first-player strategy),
  history, and the proof outline. Astro, statically built.
- `paper/` the LaTeX source of the methods paper; CI builds the PDF.
- `formalization/` the Lean 4 development proving the threshold theorem,
  packaged as downloadable supplemental material.

## Develop

Site: `cd site && npm install && npm run dev`. Tests: `npm test` for
unit, `npm run e2e` for Playwright. Paper: `cd paper && latexmk -pdf
main.tex`.

Licensing: code MIT; paper text and figures CC BY 4.0.
