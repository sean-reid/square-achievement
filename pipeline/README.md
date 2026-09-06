# Pipeline

The Python side of the project: it generates the strategy tables that
the formalization certifies, and independently cross-checks them. The
verification of record is the Lean checker in `../formalization`; this
code is where tables come from and where failures get diagnosed.
Requires Python 3.11 or later, with no third-party dependencies at
runtime.

## Modules

The package root holds the game, the verifier, the solver, and the
shared geometry; `squares/five/` the generation and export of the
5 x 5 table; `squares/plus/` the Python twin of the plus rule; and
`squares/paper/` the scripts that produce the paper's numbers and
figures.

- `squares/game.py`: the game, played over sets of cells.
- `squares/verify.py`: exhaustive verifier; plays a strategy against
  every second-player reply sequence and returns a proof of win or a
  counterexample line.
- `squares/solver.py`: exact solver over bitboards and the search for
  all-forcing winning plans.
- `squares/smallboard.py`: exact never-losing policies for the boards
  below 5, exported for the site's bot.
- `squares/paths.py`: repository paths the exporters write to.
- `squares/latent.py`: the latent corner of a far reply pair, the one
  geometric fact the rule and the 5 x 5 machinery share.
- `squares/five/tables.py`: extraction of the 5 x 5 table from solved
  positions; generates `strategy5.py`.
- `squares/five/forcing.py`: forcing-script search and the
  table-driven strategy the 5 x 5 table replays through.
- `squares/five/strategy5.py`: the generated 5 x 5 table.
- `squares/five/export_lean.py`: writes the table as a Lean data file
  into the formalization.
- `squares/five/export_site.py`: writes the same table as the site's
  `five.json`.
- `squares/five/crosscheck.py`: reads the Lean data file back and
  checks that the Lean, site, and Python copies agree.
- `squares/plus/rule.py`: the plus rule, a strategy with no lookup
  table, stated to mirror `formalization/SquareAchievement/Plus/Rule.lean`
  move for move; `sweep.py` runs it over every opening of a board and
  over the anchored far-pair positions; `measure.py` reports its lines
  per board; `export_site.py` writes the site's test fixture.
- `squares/paper/`: the paper's generated inputs: `claims.py` writes
  `paper/claims.tex` with every number the paper quotes, `figures.py`
  writes `paper/fig-*.tex` from the rule's own play, and `timings.py`
  records the certificate run times in `paper/data/timings.json`.

## Usage

```
python3 -m squares.five.tables                # regenerate the 5 x 5 table; prints the positions solved
python3 -m squares.five.export_lean           # write the Lean data file
python3 -m squares.five.export_site           # write the site's five.json
python3 -m squares.smallboard                 # write the site's small_tables.json
python3 -m squares.five.crosscheck            # the three copies of the table agree
python3 -m squares.plus.sweep 15              # the plus rule over every opening of the 15 board
python3 -m squares.plus.measure               # the rule's lines per board: count, longest, tempo split
python3 -m squares.plus.export_site           # write the site's plus_lines.json fixture
python3 -m squares.paper.timings              # record certificate times (needs lake build checker)
python3 -m squares.paper.claims               # write paper/claims.tex
python3 -m squares.paper.figures              # write paper/fig-*.tex
```

The exporters write exactly the committed files, and CI regenerates
them on every change and fails on any difference. The exported JSON is
excluded from the site's formatter so that the exporter's output is the
committed byte sequence. The 5 x 5 solve takes about twenty minutes and
several gigabytes of memory, reports 179,173,935 positions solved, and
writes `strategy5.py` unformatted: run `ruff format` on it afterwards
to reproduce the committed file byte for byte.

## Tests

```sh
uv run --with pytest python -m pytest squares
```
