import SquareAchievement.Compute.Uniform
import SquareAchievement.Results.Subsumption

/-!
# The uniform theorem

One checked run at the generation board, together with executable
table properties, should win every larger board at once. The intended
proof strengthens the soundness induction of `check_sound`: the
invariant carries a position of the generation board plus inert far
opponent stones, replies split into near ones, which the checked run
enumerates, and far ones, which resolve through class and farm
entries; `forcingComplete` confines the opponent's unforced replies
to the first two, `plan_confined` and the span geometry keep every
square the strategy touches inside the generation board, and the farm
entries, anchored by `checkFrom` runs on a board large enough to
realize each farm, cover the pairs that can reach into the corner
region. The statement is expected to grow a farm-safety hypothesis
once its executable form is fixed.
-/

namespace SquareAchievement

set_option linter.style.nativeDecide false

/-- Smoke instances of the forcing property on small boards; the run
at the generation board is the release-build certificate. -/
theorem forcing_six : forcingComplete genTable 6 = true := by native_decide

theorem forcing_seven : forcingComplete genTable 7 = true := by native_decide

/-- The forcing property at the generation board. The compiled run
returns true in about two hours, so like the per-size checks this
stays `sorry` until the final build discharges it by
`native_decide`. -/
theorem forcing_fifteen : forcingComplete genTable 15 = true := by
  sorry

/-- One checked run at the generation board wins every board from the
generation board up. -/
theorem check_sound_uniform {t : Table} {n : ℕ} (hn : 15 ≤ n)
    (hcheck : check t 15 = true)
    (hconf : planConfined t = true)
    (hforce : forcingComplete t 15 = true) :
    P1CanWin n ∅ ∅ := by
  sorry

end SquareAchievement
