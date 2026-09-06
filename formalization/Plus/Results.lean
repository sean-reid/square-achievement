import SquareAchievement.Compute.ForcedSound
import Plus.Rule

/-!
# The plus rule wins the boards up to the base

Each certificate runs the forced-tree checker on the rule itself: no
table is consulted anywhere. The rule is evaluated afresh at every node.
-/

set_option linter.style.nativeDecide false

namespace SquareAchievement.Plus

/-- The rule wins by pure forcing on every board from 6 to 16. -/
theorem plus_forced_below_seventeen :
    ((List.range' 6 11).all fun n => checkForcedS plusMove box n) = true := by
  native_decide

/-- The rule wins by pure forcing on the base board. -/
theorem plus_forced_seventeen : checkForcedS plusMove box 17 = true := by
  native_decide

/-- The first player wins with the plus rule on every board from 6 to 17. -/
theorem plus_wins_of_le_seventeen {n : ℕ} (h6 : 6 ≤ n) (h17 : n ≤ 17) :
    P1CanWin n ∅ ∅ := by
  rcases Nat.lt_or_ge n 17 with hlt | hge
  · refine checkForcedS_sound (σ := plusMove) (box := box) ?_
    have hmem : n ∈ List.range' 6 11 := by
      rw [List.mem_range']
      exact ⟨n - 6, by omega, by omega⟩
    exact (List.all_eq_true.mp plus_forced_below_seventeen) n hmem
  · have : n = 17 := by omega
    subst this
    exact checkForcedS_sound plus_forced_seventeen

end SquareAchievement.Plus
