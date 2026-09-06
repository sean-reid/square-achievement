# The Square Achievement Game on n x n Boards

Landing page, playable strategy, paper, formalization, and generation
pipeline for the square achievement game: two players alternate
claiming cells of an n x n grid, and the first to hold all four
corners of an axis-aligned square wins. The first player wins exactly
when n >= 5, by a machine-checked strategy.

## Layout

- `site/` the site: a hub with the playable game and one card per
  result, and for each result an overview page at `/<slug>/` and an
  illustrated proof guide at `/<slug>/proof/`. Astro, statically
  built; the deploy also packages every paper's PDF and the
  formalization tarball.
- `papers/` the LaTeX sources, one directory per paper, with the
  shared bibliography and macros in `papers/shared/`; CI builds every
  PDF. `papers/threshold/` is the paper on the winning threshold and
  `papers/plus/` the paper on the plus rule, a winning strategy with
  no lookup table.
- `formalization/` the Lean 4 development: a core library with the
  game semantics and the checkers with machine-checked soundness, and
  a library per result, the first holding the strategy tables as
  data and the simulation theorem covering every board size. See
  [formalization/README.md](formalization/README.md).
- `pipeline/` the Python side: table generation, the exhaustive
  reference verifier, exporters, and analysis tools. See
  [pipeline/README.md](pipeline/README.md).

## Getting started

The components are independent; none is needed to build the others.
Commands assume a POSIX shell; on Windows, work inside WSL.

While the repository is private, the checks below run on the author's
machine before a change merges; the `ci` and `lean` workflows repeat
them weekly and on demand rather than on every pull request.

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
cd papers/threshold   # or papers/plus
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

## Adding a result

Each result is one slug used everywhere, `threshold` being the first.
A new one needs:

- `papers/<slug>/main.tex`, citing from `papers/shared/refs.bib`, and
  the slug added to the paper matrix in `.github/workflows/ci.yml`.
- A Lean library `formalization/<Slug>/` with a root `<Slug>.lean`,
  importing the `SquareAchievement` core, listed as a `lean_lib` in
  `formalization/lakefile.toml` and among its default targets.
- A pipeline subpackage `pipeline/squares/<slug>/` with its tests
  beside it, if the result has generated data.
- An entry in `site/src/results.ts`, with `site/src/pages/<slug>/index.astro`
  and `site/src/pages/<slug>/proof.astro`.

## License

Code is MIT. The paper's text and figures are CC BY 4.0.
