# Formalization

Lean 4 formalization of the square achievement game: two players
alternately claim cells of an n x n board, and the first to hold all
four corners of an axis-aligned square (2 x 2 blocks included) wins.
`P1CanWin` is an inductive whose proofs are literally strategy trees;
everything below builds or refutes such trees. The development has no
unproved declarations, and its axiom footprint is Lean's kernel plus
the compiler-evaluation axiom that `native_decide` uses.

The package holds three libraries. `SquareAchievement` is the shared
core: the game, its outcomes, the strategy-table format, the checkers,
and their soundness theorems. `Threshold` is the first result built on
it: the tables, the uniform argument, the certificates, and the
threshold theorems below. `Plus` is the second: a strategy stated as a
rule rather than a table, certified directly for every board from 6 up
with no data file anywhere. Further results get
libraries of their own beside them.

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
| `simulate` | a forced base run of any strategy replays on every larger board |
| `check_sound_uniform` | the checked run at 17, with the anchored certificates, wins every board from 17 up |
| `checkForcedS_winsWith` | a successful forced run of a strategy that takes its wins yields the strategy's own winning tree, `WinsWith` |
| `Plus.plus_wins_with` | following the plus rule, a strategy stated without a lookup table, wins every board from 6 up: the winning tree is the rule's own play |
| `Plus.plus_wins` | the same with the moves forgotten, a `P1CanWin` tree |
| `Plus.plus_wins_with_of_le_seventeen` | the rule's direct certificates for the boards from 6 to 17 |

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

The build is the proof, and it runs on the author's machine before a
change to the formalization merges; the `lean` workflow rebuilds it
weekly and on demand rather than per pull request, since a full build
costs most of an hour of runner time. `lake build` builds all three
libraries: it elaborates every file and the kernel checks every
theorem, evaluating the certificates along the
way, so a successful build verifies everything in the results table,
the boards from 17 up included through `check_sound_uniform`. The
checker executable below demonstrates the same runs interactively but
is not the proof; the runs the theorems cite happen inside the build.
To display the headline theorem and the axioms behind it, after
building:

```sh
echo 'import Threshold
import Plus
#check @SquareAchievement.outcome
#print axioms SquareAchievement.outcome
#check @SquareAchievement.Plus.plus_wins_with
#print axioms SquareAchievement.Plus.plus_wins_with' | lake env lean --stdin
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
| `plus` | run the certified forced-tree checker on the plus rule instead of the table |
| `plus anchors` | run the plus rule's three anchored far-pair families |

To reproduce the runs reported in the paper's Table 1:

```sh
lake exe checker 5 five slow
for n in $(seq 6 17); do lake exe checker "$n" forced; done
```

To reproduce the plus rule's runs, Table 1 of the plus paper:

```sh
for n in $(seq 6 17) 23; do lake exe checker "$n" plus; done
lake exe checker plus anchors
```

## Layout

`SquareAchievement/`, the core library:

- `Core/` cells, squares, positions; the quarter-plane model makes
  cross-board-size statements direct.
- `Game/` the rules and `P1CanWin`; `Outcome` adds the draw
  predicates, strategy stealing, and determinacy.
- `Compute/` the strategy table format; the enumerating checker, the
  forced-tree checker (generic over strategies, the table strategy
  being one instance), and the refuter with their soundness proofs;
  `WinsWith`, the predicate that a strategy's own play wins, which the
  forced checker's soundness theorem concludes; and a byte-board
  checker used only by the executable, never cited in proofs.
- `General/` the simulation argument any forced strategy can use:
  span and invariance geometry (`Invariance`), the latency dichotomy
  (`Coverage`), the replay of a forced base run on every larger board
  (`Simulation`), and the small facts every wrapper of it needs
  (`Dispatch`).

`Threshold/`, the threshold result:

- `ExactFarm.lean` the anchored farm-safety certificates.
- `Data/` machine-generated strategy tables: the n = 5 table and the
  general corner-box table.
- `General/Wrapper.lean` the dispatch assembling `check_sound_uniform`
  from the table's lookups and the simulation.
- `Results/` the evaluated certificates and the threshold theorems.

`Plus/`, the plus rule:

- `Rule.lean` the strategy as executable code: the opening, the
  second-move diagram, tempo moves, pluses of side one and two, and the
  shortest line within three tempo moves, read off an abstraction of
  the position.
- `Anchors.lean` the rule's anchored runs on the board of size 23: the
  base run for the uniform argument and the three far-pair families,
  with the latent corner as a guard.
- `Threats.lean` the rule's pair-based threat scan agrees with the
  checker's square scan, so the rule takes every completion the board
  offers.
- `Agreement.lean` the rule reads the same move from a real history and
  from its base view: stand-ins and anchors beyond the base board leave
  its abstraction unchanged.
- `Uniform.lean` the wrapper dispatching every real reply pair to the
  simulation, using the rule's own second move and stand-ins beyond the
  base board, and concluding that the rule's own play wins.
- `Results.lean` the certificates, evaluated: the runs at sizes 6 to 17,
  the anchor-board run, and the anchored families, and the theorems
  `plus_wins_with` and `plus_wins`.

`Checker.lean` is the executable, built from the core and `Threshold`.
