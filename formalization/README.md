# Formalization

A Lean 4 development, on mathlib, of the square achievement game on
`n x n` boards: the rules, the winning predicate, the draw predicates,
executable checkers with machine-checked soundness theorems, the plus
rule as a Lean definition with its certificates, the `5 x 5` strategy
table as data, the simulation theorem that carries a checked run on
one board to every larger board, and the outcome theorems. The
development builds with no unproved declarations, and its axiom
footprint is Lean's kernel plus the compiler-evaluation trust behind
`native_decide`.

## Results

| Theorem | Statement |
| --- | --- |
| `outcome` | the first player forces a win exactly on the boards from 5 x 5 up, and every board up to 4 x 4 is drawn, each player able to secure at least a draw |
| `p1_wins_iff` | the first half of `outcome` |
| `Plus.plus_wins_with` | following the plus rule, a strategy stated without a lookup table, wins every board from 6 x 6 up: the winning tree is the rule's own play |
| `Plus.plus_wins` | the same with the moves forgotten, a `P1CanWin` tree |
| `p1_wins_five` | the first player wins on 5 x 5, by the exact-solver table with quiet forks |
| `small_board_no_win` | no first-player win on boards up to 4 x 4 |
| `small_board_drawn` | drawing strategies for both players on boards up to 4 x 4 |
| `second_player_no_win` | strategy stealing: the second player never forces a win |
| `P1CanWin.or_p2CanDraw` | determinacy: the player to move forces a win or the other player can draw |
| `check_sound` | a successful run of the enumerating checker yields a `P1CanWin` tree |
| `checkForcedS_winsWith` | a successful forced run of a strategy that takes its wins yields the strategy's own winning tree, `WinsWith` |
| `refute_sound` | a successful refuter run refutes a first-player win |
| `escape_farm` | a square escaping the base board through a box cell and the reply pair has that cell as the pair's hidden corner, the one `farmKey` returns |
| `farmKey_corners` | the hidden corner lies in the box and is a corner of a square through both replies |
| `simulate` | a forced base run of any strategy replays on every larger board as the strategy's own play |

## Building

Requires [elan](https://github.com/leanprover/elan), which supplies the
pinned toolchain.

```sh
lake exe cache get
lake build
```

`lake build` elaborates every file and the kernel checks every theorem,
evaluating the certificates along the way: the refutations up to 4 x 4,
the exhaustive check of the 5 x 5 table, the forced-tree runs of the
plus rule at sizes 6 to 17 and on the anchor board 23, and the three
anchored far-pair families. Expect about 17 minutes on a laptop,
almost all of it the evaluations. On Linux the precompiled
modules load the toolchain's shared libraries through
`LD_LIBRARY_PATH`; set it to `$(lean --print-libdir)` if the checker
executable fails to start.

The build is the proof, and it runs locally before a formalization
change merges; the `lean` workflow rebuilds it weekly and on demand
rather than per pull request.

## Checking the theorem

To display the headline theorems and the axioms behind them, after
building:

```sh
echo 'import SquareAchievement
#check @SquareAchievement.outcome
#print axioms SquareAchievement.outcome
#check @SquareAchievement.Plus.plus_wins_with
#print axioms SquareAchievement.Plus.plus_wins_with' | lake env lean --stdin
```

The axioms are `propext`, `Classical.choice`, `Quot.sound`, and one
`..._native.native_decide.ax...` entry per evaluated certificate: the
standard base plus the compiler-evaluation trust behind
`native_decide`. That last item means trusting the Lean compiler and
runtime to evaluate the checkers correctly; the kernel checks the
soundness theorems but not the evaluations themselves. Kernel reduction
(`decide`) of the same runs is out of reach by orders of magnitude, so
this is the trust base of every large computer-assisted proof in Lean.

## Running the checker

```sh
lake exe checker <n>        # the certificate for the n board, with its time
lake exe checker anchors    # the plus rule's three anchored far-pair families
lake exe checker lines      # the line the plus rule commits to after every reply pair
lake exe checker 5 trace    # the first failing line of the 5 x 5 table, if any
```

Below 5 the checker runs the refuter, at 5 the exhaustive check of the
5 x 5 table, and from 6 up the forced-tree checker on the plus rule.
The executable demonstrates the same runs interactively but is not the
proof; the runs the theorems cite happen inside the build.

`lines` prints one position per line, machine-readable:
`6 o1r o1c o2r o2c x2r x2c : r c r c ...` for each of the 1,155 reply
pairs of the 6 x 6 board, where `o1` and `o2` are the second player's
replies and `x2` the first player's second move, and
`anchor h1 h2 o1r o1c o2r o2c x2r x2c : ...` for each of the 176
anchored positions, where `(h1, h2)` is the hidden corner the rule
reads. After the colon come the cells of the rule's line in play order,
or `none`. The pipeline's `squares.plus.crosscheck` compares this
output with the Python rule, and its tests keep a saved copy at
`pipeline/squares/plus/tests/fixtures/lean_lines.txt`.

## Layout

One library, `SquareAchievement/`, every declaration in the
`SquareAchievement` namespace, with a root `SquareAchievement.lean`
importing every module:

- `Core/` cells, squares, positions; the quarter-plane model makes
  cross-board-size statements direct.
- `Game/` the rules and `P1CanWin`; `Outcome` adds the draw predicates,
  strategy stealing, and determinacy.
- `Compute/` the strategy table format used by the 5 x 5 table; the
  enumerating checker and the refuter with their soundness proofs; the
  forced-tree checker, generic over strategies; `WinsWith`, the
  predicate that a strategy's own play wins, which the forced checker's
  soundness theorem concludes.
- `General/` the simulation argument any forced strategy can use: the
  hidden corner of a reply pair (`FarmKey`), the dichotomy for squares
  escaping the base board (`Coverage`), the replay of a forced base run
  on every larger board (`Simulation`), and the small facts every
  wrapper of it needs (`Dispatch`).
- `Plus/` the plus rule: `Rule` defines it as executable code;
  `Threats` proves its pair-based threat scan agrees with the
  checker's; `Agreement` proves it reads the same move from a real
  history and its base view; `Anchors` defines the anchored runs on the
  board of size 23; `Uniform` dispatches every real reply pair to the
  simulation; `Results` evaluates the certificates and states
  `plus_wins_with` and `plus_wins`.
- `Five/` the machine-generated 5 x 5 table, exported by the pipeline.
- `Results/` the outcome theorems assembled from the refutations, the
  5 x 5 certificate, and the plus rule.

`Main.lean` is the executable, `lake exe checker`.
