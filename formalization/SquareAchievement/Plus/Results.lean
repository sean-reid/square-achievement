import SquareAchievement.Compute.ForcedSound
import SquareAchievement.Plus.Rule
import SquareAchievement.Plus.Anchors
import SquareAchievement.Plus.Uniform

/-!
# The plus rule's certificates

Each certificate runs the forced-tree checker on the rule itself: no
table is consulted anywhere, and the rule is evaluated afresh at every
node. The runs at sizes 6 to 17 prove those boards directly; the run
on the anchor board and the three anchored families feed the uniform
argument for every larger board.
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

/-- Following the rule wins on every board from 6 to 17: the tree of
its own moves is a winning tree. -/
theorem plus_wins_with_of_le_seventeen {n : ℕ} (h6 : 6 ≤ n) (h17 : n ≤ 17) :
    WinsWith plusMove n [] := by
  rcases Nat.lt_or_ge n 17 with hlt | hge
  · refine checkForcedS_winsWith (plusMove_takesWins h6) ?_
    have hmem : n ∈ List.range' 6 11 := by
      rw [List.mem_range']
      exact ⟨n - 6, by omega, by omega⟩
    exact (List.all_eq_true.mp plus_forced_below_seventeen) n hmem
  · have : n = 17 := by omega
    subst this
    exact checkForcedS_winsWith (plusMove_takesWins h6) plus_forced_seventeen

/-- The rule's forced run on the anchor board, every reply pair. -/
theorem plus_forced_anchor : checkForcedS plusMove box anchorBoard = true := by
  native_decide

theorem far_anchors_safe : farAnchorsSafe = true := by native_decide
theorem exact_anchors_safe : exactAnchorsSafe = true := by native_decide
theorem far_near_anchors_safe : farNearAnchorsSafe = true := by native_decide

/-- Following the rule wins on every board from the base up. -/
theorem plus_wins_with_of_seventeen_le {n : ℕ} (hn : 17 ≤ n) : WinsWith plusMove n [] :=
  plus_uniform_aux hn plus_forced_anchor far_anchors_safe exact_anchors_safe
    far_near_anchors_safe

/-- The plus rule wins the square achievement game on every board of
size at least six, and the winning tree is the rule's own play: at
every node of the derivation the first player's move is the move the
rule returns. No lookup table appears in the statement or the proof. -/
theorem plus_wins_with {n : ℕ} (h : 6 ≤ n) : WinsWith plusMove n [] := by
  rcases Nat.lt_or_ge n 17 with hlt | hge
  · exact plus_wins_with_of_le_seventeen h (by omega)
  · exact plus_wins_with_of_seventeen_le hge

/-- The first player wins on every board of size at least six. -/
theorem plus_wins {n : ℕ} (h : 6 ≤ n) : P1CanWin n ∅ ∅ := by
  have := (plus_wins_with h).p1CanWin (by simp)
  simpa [stonesOf] using this

end SquareAchievement.Plus
