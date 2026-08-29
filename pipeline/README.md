# Pipeline

The Python side of the project: it generates the strategy tables that
the formalization certifies, and independently cross-checks them. The
verification of record is the Lean checker in `../formalization`; this
code is where tables come from and where failures get diagnosed.

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
- `squares/smallboard.py`: exact never-losing policies for the boards
  below 5, exported for the site's bot.
- `squares/diagnose.py`: replays a failing line and narrates every
  decision the strategy made.
- `squares/instrument.py`: runs the verifier with a metering strategy
  and reports the geometric frame the strategy actually touches.

## Usage

```
python3 -m squares.solve            # regenerate the 5 x 5 table
python3 -m squares.solve general    # general table + verification sweep
python3 -m squares.export_lean      # write Lean data files
python3 -m squares.instrument 6 7   # measure the strategy's frame
```

Tests: `uv run --with pytest python -m pytest squares/tests`.
