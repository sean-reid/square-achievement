# Formalization

Lean 4 formalization of the square achievement game: two players
alternately claim cells of an n x n board, and the first to hold all
four corners of an axis-aligned square (2 x 2 blocks included) wins.
`P1CanWin` is an inductive whose proofs are literally strategy trees;
everything below builds or refutes such trees. The development has no
unproved declarations: every certificate evaluates during the build,
and the axiom footprint is Lean's kernel plus the compiler-evaluation
axiom that `native_decide` uses.

## Results

| Theorem | Statement |
| --- | --- |
| `small_board_no_win` | no first-player win on boards up to 4 x 4 |
| `p1_wins_five` | the first player wins on 5 x 5 |
| `p1_wins_of_five_le` | the first player wins on every board from 5 x 5 up |
| `check_sound` | a successful checker run yields a `P1CanWin` tree |
| `checkForced_sound` | the same for the forced-tree checker |
| `refute_sound` | a successful refuter run yields a drawing strategy |
| `escape_farm` | a square escaping the base board is latent: box corner plus the reply pair |
| `simulate` | a forced base run replays on every larger board |
| `check_sound_uniform` | the checked run at 17, with the anchored certificates, wins every board from 17 up |

## Layout

- `Core/`: cells, squares, positions; the quarter-plane model makes
  cross-board-size statements direct.
- `Game/`: the rules and `P1CanWin`.
- `Compute/`: the strategy table format; the enumerating checker, the
  forced-tree checker, and the refuter with their soundness proofs;
  the anchored farm-safety certificates; and a byte-board checker
  used only by the executable (never cited in proofs).
- `Data/`: machine-generated strategy tables, the n = 5 table and the
  general corner-box table.
- `General/`: the uniform proof: span and invariance geometry
  (`Invariance`), the latency dichotomy (`Coverage`), the simulation
  (`Simulation`), and the wrapper assembling `check_sound_uniform`
  (`Wrapper`).
- `Results/`: the evaluated certificates and the threshold theorems.

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain is
pinned by `lean-toolchain`, and mathlib arrives prebuilt through the
cache. From this directory:

```
lake exe cache get
lake build
```

On Linux, export `LD_LIBRARY_PATH="$(lean --print-libdir)"` first:
the library precompiles its modules, and the loader needs the Lean
runtime on that path (see `.github/workflows/lean.yml`, which is the
recipe CI runs). The first build also compiles mathlib's native code
and then evaluates every certificate; expect roughly half an hour on
a laptop, dominated by the batched runs at sizes 6 through 16 and
the base run at 17. Later builds only re-evaluate what changed.
Verified on macOS (Apple silicon) and Linux x86-64; on Windows, use
WSL, which is the Linux path above. The native Windows toolchain is
untested here.

## Checking the theorem

The build is the proof. `lake build` elaborates every file and the
kernel checks every theorem, evaluating the certificates along the
way, so a successful build verifies everything in the results table,
the boards from 17 up included through `check_sound_uniform`. The
checker executable below demonstrates the same runs interactively
but is not the proof; the runs the theorems cite happen inside the
build. To display the headline theorem and the axioms behind it, after building:

```
echo 'import SquareAchievement
#check @SquareAchievement.p1_wins_of_five_le
#print axioms SquareAchievement.p1_wins_of_five_le' | lake env lean --stdin
```

The axioms are `propext`, `Classical.choice`, `Quot.sound`, and
`Lean.ofReduceBool`, the standard base plus the compiler-evaluation
axiom behind `native_decide`.

## Running the checker

```
lake exe checker <n> [five] [slow] [forced] [trace] [refute] [farmsafe] [exactfarm]
```

Verifies the general table on the n x n board with the byte-board
checker. `five` selects the n = 5 table (and the certified checker,
which alone handles its quiet forks), `slow` forces the certified
checker, `forced` runs the certified forced-tree checker, `trace`
prints the first failing line instead of a verdict, `refute` searches
for a drawing strategy for the second player, `farmsafe` and
`exactfarm` run the anchored farm-safety certificates.

To reproduce the runs reported in the paper's Table 1:

```
lake exe checker 5 five slow
for n in $(seq 6 17); do lake exe checker "$n" forced; done
```
