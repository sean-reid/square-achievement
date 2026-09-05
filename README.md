# The Square Achievement Game on n x n Boards

Landing page, playable strategy, paper, formalization, and generation
pipeline for the square achievement game: two players alternate
claiming cells of an n x n grid, and the first to hold all four
corners of an axis-aligned square wins. The first player wins exactly
when n >= 5, by a machine-checked strategy.

## Layout

- `site/` the landing page: the theorem, the playable game, and the
  routes to the paper, the Lean development, and an illustrated proof
  guide at `/proof/`. Astro, statically built; the deploy also
  packages the paper PDF and the formalization tarball.
- `paper/` the LaTeX source of the paper; CI builds the PDF.
- `formalization/` the Lean 4 development: game semantics, checkers
  with machine-checked soundness, the simulation theorem covering
  every board size, and the strategy tables as data. See
  [formalization/README.md](formalization/README.md).
- `pipeline/` the Python side: table generation, the exhaustive
  reference verifier, exporters, and analysis tools. See
  [pipeline/README.md](pipeline/README.md).

## Getting started

The components are independent; none is needed to build the others.
Commands assume a POSIX shell; on Windows, work inside WSL.

### Site

Requires Node 22, from [nodejs.org](https://nodejs.org) or a version
manager.

```sh
cd site
npm install
npm run dev
```

`npm test` runs the unit tests. `npm run e2e` runs the Playwright
suite after a one-time `npx playwright install`.

### Paper

Requires a TeX Live installation with `amsart`, `tikz`, and
`algorithm`.

```sh
cd paper
latexmk -pdf main.tex
```

### Formalization

Requires [elan](https://github.com/leanprover/elan), which supplies
the pinned Lean toolchain.

```sh
cd formalization
lake exe cache get
lake build
```

A successful build verifies every theorem, all board sizes included.
[formalization/README.md](formalization/README.md) covers the
expected build time, the Linux environment note, and the commands
reproducing the paper's Table 1.

### Pipeline

Requires Python 3.11 or later; no third-party dependencies at
runtime.

```sh
cd pipeline
uv run --with pytest python -m pytest squares
```

## License

Code is MIT. The paper's text and figures are CC BY 4.0.
