# Formalization

Lean 4 formalization of the square achievement game: two players
alternately claim cells of an n x n board, and the first to hold all
four corners of an axis-aligned square (2 x 2 blocks included) wins.
`P1CanWin` is an inductive whose proofs are literally strategy trees;
everything below builds or refutes such trees. The development has no
unproved declarations, and its axiom footprint is Lean's kernel plus
the compiler-evaluation axiom that `native_decide` uses.

## Results

| Theorem | Statement |
| --- | --- |
| `p1_wins_iff` | the first player forces a win exactly on the boards from 5 x 5 up |
| `outcome` | the same, plus: every board up to 4 x 4 is drawn, each player able to secure at least a draw |
| `small_board_no_win` | no first-player win on boards up to 4 x 4 |
| `small_board_drawn` | drawing strategies for both players on boards up to 4 x 4 |
| `second_player_no_win` | strategy stealing: the second player never forces a win |
| `P1CanWin.or_p2CanDraw` | determinacy: the player to move forces a win or the opponent can draw |
| `p1_wins_five` | the first player wins on 5 x 5 |
| `p1_wins_of_five_le` | the first player wins on every board from 5 x 5 up |
| `check_sound` | a successful checker run yields a `P1CanWin` tree |
| `checkForced_sound` | the same for the forced-tree checker |
| `refute_sound` | a successful refuter run refutes a first-player win |
| `escape_farm` | a square escaping the base board is latent: box corner plus the reply pair |
| `simulate` | a forced base run replays on every larger board |
| `check_sound_uniform` | the checked run at 17, with the anchored certificates, wins every board from 17 up |

## Building

Prerequisites:

- [elan](https://github.com/leanprover/elan); the exact Lean
  toolchain is pinned by `lean-toolchain`.
- A few gigabytes of disk for the mathlib cache.
- A POSIX shell. On Linux, export
  `LD_LIBRARY_PATH="$(lean --print-libdir)"` before building: the
  library precompiles its modules and the loader needs the Lean
  runtime on that path (`.github/workflows/lean.yml` is the recipe CI
  runs). On Windows, use WSL; the native toolchain is untested here.

```sh
lake exe cache get
lake build
```

The first build compiles mathlib's native code and then evaluates
every certificate; expect roughly half an hour on a laptop, dominated
by the batched runs at sizes 6 through 16 and the base run at 17.
Later builds re-evaluate only what changed. Verified on macOS (Apple
silicon) and Linux x86-64.

## Checking the theorem

The build is the proof. `lake build` elaborates every file and the
kernel checks every theorem, evaluating the certificates along the
way, so a successful build verifies everything in the results table,
the boards from 17 up included through `check_sound_uniform`. The
checker executable below demonstrates the same runs interactively but
is not the proof; the runs the theorems cite happen inside the build.
To display the headline theorem and the axioms behind it, after
building:

```sh
echo 'import SquareAchievement
#check @SquareAchievement.outcome
#print axioms SquareAchievement.outcome' | lake env lean --stdin
```

The axioms are `propext`, `Classical.choice`, `Quot.sound`, and one
`..._native.native_decide.ax...` entry per evaluated certificate:
the standard base plus the compiler-evaluation trust behind
`native_decide`. That last item means trusting the Lean compiler and
runtime to evaluate the checkers correctly; the kernel checks the
soundness theorems but not the evaluations themselves. Kernel
reduction (`decide`) of the same runs is out of reach by orders of
magnitude, so this is the trust base of every large computer-assisted
proof in Lean.

## Running the checker

```sh
lake exe checker <n> [flags]
```

Without flags, verifies the general table on the n x n board with the
byte-board checker.

| Flag | Effect |
| --- | --- |
| `five` | select the n = 5 table and the certified checker, which alone handles its quiet forks |
| `slow` | force the certified enumerating checker |
| `forced` | run the certified forced-tree checker |
| `trace` | print the first failing line instead of a verdict |
| `refute` | search for a second-player drawing strategy |
| `exactfarm` | run the three coordinate-anchored farm-safety certificates |

To reproduce the runs reported in the paper's Table 1:

```sh
lake exe checker 5 five slow
for n in $(seq 6 17); do lake exe checker "$n" forced; done
```

## Layout

- `Core/` cells, squares, positions; the quarter-plane model makes
  cross-board-size statements direct.
- `Game/` the rules and `P1CanWin`; `Outcome` adds the draw
  predicates, strategy stealing, and determinacy.
- `Compute/` the strategy table format; the enumerating checker, the
  forced-tree checker, and the refuter with their soundness proofs;
  the anchored farm-safety certificates; and a byte-board checker
  used only by the executable, never cited in proofs.
- `Data/` machine-generated strategy tables: the n = 5 table and the
  general corner-box table.
- `General/` the uniform proof: span and invariance geometry
  (`Invariance`), the latency dichotomy (`Coverage`), the simulation
  (`Simulation`), and the wrapper assembling `check_sound_uniform`
  (`Wrapper`).
- `Results/` the evaluated certificates and the threshold theorems.
