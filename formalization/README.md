# Formalization

Lean 4 formalization of the square achievement game: two players
alternately claim cells of an n x n board, and the first to hold all
four corners of an axis-aligned square (2 x 2 blocks included) wins.
`P1CanWin` is an inductive whose proofs are literally strategy trees;
everything below builds or refutes such trees.

## Results

Proven, no axioms beyond Lean's kernel plus the compiler-evaluation
axiom that `native_decide` uses:

| Theorem | Statement |
| --- | --- |
| `small_board_no_win` | no first-player win on boards up to 4 x 4 |
| `p1_wins_five` | the first player wins on 5 x 5 |
| `check_sound` | a successful checker run yields a `P1CanWin` tree |
| `refute_sound` | a successful refuter run yields a drawing strategy |

Open, stated with named `sorry` obligations in `Results/`:

- `check_below_bound`, `check_at_bound`: one heavy checker evaluation
  per concrete size, deferred to the final build where each is a
  single `native_decide`.
- `subsumption`: lifting the checker run at the saturation bound to
  every larger board. This is the remaining mathematics.

## Layout

- `Core/`: cells, squares, positions; the quarter-plane model makes
  cross-board-size statements direct.
- `Game/`: the rules and `P1CanWin`.
- `Compute/`: the strategy table format, the executable checker and
  refuter, their soundness proofs, and a byte-board checker used only
  by the executable (never cited in proofs).
- `Data/`: machine-generated strategy tables, the n = 5 table and the
  general corner-box table.
- `General/`: board-size invariance lemmas.
- `Results/`: the threshold theorems and the subsumption statement.

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain is
pinned by `lean-toolchain`.

```
lake exe cache get
lake build
```

## Running the checker

```
lake exe checker <n> [five] [slow] [trace] [refute]
```

Verifies the general table on the n x n board with the byte-board
checker. `five` selects the n = 5 table (and the certified checker,
which alone handles its quiet forks), `slow` forces the certified
checker, `trace` prints the first failing line instead of a verdict,
`refute` searches for a drawing strategy for the second player.
