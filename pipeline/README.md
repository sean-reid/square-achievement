# Pipeline

The Python side of the project: it generates the strategy tables that
the formalization certifies, and independently cross-checks them. The
verification of record is the Lean checker in `../formalization`; this
code is where tables come from and where failures get diagnosed.
Requires Python 3.11 or later, with no third-party dependencies at
runtime.

## Modules

The package root holds what every result shares; `squares/threshold/`
holds the generation and export code of the threshold paper. A later
result gets its own subpackage beside it.

- `squares/game.py`: the game, played over sets of cells.
- `squares/verify.py`: exhaustive verifier; plays a strategy against
  every second-player reply sequence and returns a proof of win or a
  counterexample line.
- `squares/solver.py`: exact solver over bitboards and the search for
  all-forcing winning plans.
- `squares/smallboard.py`: exact never-losing policies for the boards
  below 5, exported for the site's bot.
- `squares/paths.py`: repository paths the exporters write to.
- `squares/threshold/tables.py`: extraction of table entries from
  solved positions; generates the 5 x 5 table and the corner-box table.
- `squares/threshold/forcing.py`: forcing-script search and the
  table-driven strategy the tables replay through.
- `squares/threshold/strategy5.py`: the generated 5 x 5 table.
- `squares/threshold/export_lean.py`: writes the tables as Lean data
  files into the formalization.
- `squares/threshold/export_site.py`: writes the same tables as the
  site's `tables.json`.
- `squares/threshold/crosscheck.py`: reads the Lean data files back and
  checks that the Lean, site, and Python copies of the tables agree.
- `squares/threshold/diagnose.py`: replays a failing line and narrates
  every decision the strategy made.
- `squares/threshold/instrument.py`: runs the verifier with a metering
  strategy and reports the geometric frame the strategy touches.

## Usage

```
python3 -m squares.threshold.tables           # regenerate the 5 x 5 table; prints the positions solved
python3 -m squares.threshold.tables general   # general table + reference verification at 6, 7, 8
python3 -m squares.threshold.export_lean      # write the Lean data files
python3 -m squares.threshold.export_site      # write the site's tables.json
python3 -m squares.smallboard                 # write the site's small_tables.json
python3 -m squares.threshold.crosscheck       # the three copies of the tables agree
python3 -m squares.threshold.instrument 6 7   # measure the strategy's frame
```

The general table is generated on the 15 x 15 board (`GEN_N` in
`tables.py`), which takes about five minutes; the exporters write
exactly the committed files, and CI regenerates them on every change
and fails on any difference. The exported JSON is excluded from the
site's formatter so that the exporter's output is the committed
byte sequence. The 5 x 5 solve takes about twenty minutes and
several gigabytes of memory, reports 179,173,935 positions solved,
and writes `strategy5.py` unformatted: run `ruff format` on it
afterwards to reproduce the committed file byte for byte.

## Tests

```sh
uv run --with pytest python -m pytest squares
```
