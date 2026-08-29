import SquareAchievement.Compute.Refute
import SquareAchievement.Results.Subsumption
import SquareAchievement.Data.Table5

/-!
# The threshold theorems

The headline results. `small_board_no_win` needs a refutation
certificate (P2's drawing strategy, exportable from the exact solver's
memo). `p1_wins_of_five_le` assembles from three ingredients:

* `n = 5`: its own certificate (the exact-solver table with quiet
  forks, awaiting the checker's fork-entry extension);
* `6 ≤ n < N₀`: one checker run per size via `check_sound`;
* `N₀ ≤ n`: the one run at `N₀`, lifted by `subsumption`.

The per-size `check` facts are heavy evaluations (the compiled checker
takes minutes at the largest sizes), so they stay `sorry` until the
final build, where each becomes a single `native_decide`.
-/

set_option linter.style.nativeDecide false

namespace SquareAchievement

theorem refute_one : refute 1 = true := by native_decide
theorem refute_two : refute 2 = true := by native_decide
theorem refute_three : refute 3 = true := by native_decide
theorem refute_four : refute 4 = true := by native_decide

theorem small_board_no_win {n : ℕ} (h : n ≤ 4) : ¬ P1CanWin n ∅ ∅ := by
  rcases n with _ | _ | _ | _ | _ | n
  · exact not_p1CanWin_zero
  · exact refute_sound refute_one
  · exact refute_sound refute_two
  · exact refute_sound refute_three
  · exact refute_sound refute_four
  · omega

/-- The `n = 5` case, from its own certificate: the exact-solver table
with quiet forks, replayed exhaustively inside Lean. -/
theorem p1_wins_five : P1CanWin 5 ∅ ∅ :=
  check_sound (t := fiveTable) (by native_decide)

/-- Each concrete size from 6 below the saturation bound, by one
checker run. -/
theorem check_below_bound {n : ℕ} (h6 : 6 ≤ n) (hlt : n < N₀) :
    check genTable n = true := by
  sorry

/-- The run at the saturation bound itself. -/
theorem check_at_bound : check genTable N₀ = true := by
  sorry

theorem plan_confined : planConfined genTable = true := by
  native_decide

theorem p1_wins_of_five_le {n : ℕ} (h : 5 ≤ n) : P1CanWin n ∅ ∅ := by
  rcases eq_or_lt_of_le h with h5 | h6
  · exact h5 ▸ p1_wins_five
  · rcases Nat.lt_or_ge n N₀ with hlt | hge
    · exact check_sound (check_below_bound h6 hlt)
    · exact subsumption hge plan_confined check_at_bound

end SquareAchievement
