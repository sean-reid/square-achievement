# Pipeline

The Python side of the project: it generates the strategy tables that
the formalization certifies, and independently cross-checks them. The
verification of record is the Lean checker in `../formalization`; this
code is where tables come from and where failures get diagnosed.
Requires Python 3.11 or later, with no third-party dependencies at
runtime.

## Modules

- `squares/game.py`: the game, played over sets of cells.
- `squares/verify.py`: exhaustive verifier; plays a strategy against
  every second-player reply sequence and returns a proof of win or a
  counterexample line.
- `squares/solve.py`: exact solver over bitboards and the extraction
  of table entries from solved positions.
- `squares/forcing.py`: forcing-script search and the table-driven
  strategy the tables replay through.
- `squares/strategy5.py`: the generated 5 x 5 table (regenerate with
  `python3 -m squares.solve`).
- `squares/export_lean.py`: writes the tables as Lean data files into
  the formalization.
- `squares/export_site.py`: writes the same tables as the site's
  `tables.json`.
- `squares/crosscheck.py`: reads the Lean data files back and checks
  that the Lean, site, and Python copies of the tables agree.
- `squares/smallboard.py`: exact never-losing policies for the boards
  below 5, exported for the site's bot.
- `squares/diagnose.py`: replays a failing line and narrates every
  decision the strategy made.
- `squares/instrument.py`: runs the verifier with a metering strategy
  and reports the geometric frame the strategy actually touches.

## Usage

```
python3 -m squares.solve            # regenerate the 5 x 5 table; prints the positions solved
python3 -m squares.solve general    # general table + reference verification at 6, 7, 8
python3 -m squares.export_lean      # write the Lean data files
python3 -m squares.export_site      # write the site's tables.json
python3 -m squares.smallboard       # write the site's small_tables.json
python3 -m squares.crosscheck       # the three copies of the tables agree
python3 -m squares.instrument 6 7   # measure the strategy's frame
```

The general table is generated on the 15 x 15 board (`GEN_N` in
`solve.py`), which takes about five minutes; the exporters write
exactly the committed files, and CI regenerates them on every change
and fails on any difference. The exported JSON is excluded from the
site's formatter so that the exporter's output is the committed
byte sequence. The 5 x 5 solve takes about twenty minutes and
several gigabytes of memory, reports 179,173,935 positions solved,
and writes `strategy5.py` unformatted: run `ruff format` on it
afterwards to reproduce the committed file byte for byte.

## Tests

```sh
uv run --with pytest python -m pytest squares/tests
```
