import SquareAchievement.Compute.ForcedSound
import SquareAchievement.Data.TableGen

/-!
# The uniform theorem

One forced-tree run at the base board, together with executable table
properties, wins every larger board at once. The base is
`17 = box + far - 1`: an opponent square with a corner in the box and
a stone below the far threshold fits inside the base board, where the
run has checked it, so every square escaping the base has both reply
stones at the far threshold or beyond, which is exactly the territory
the farm entries govern. The intended proof replays the base run:
near replies verbatim, unforced replies answered by the standing
threat, the two reply stones abstracted through class representatives
or, for farming pairs, through the anchored farm subtrees. The
statement is expected to grow a farm-completeness hypothesis once its
executable form is fixed.
-/

namespace SquareAchievement

set_option linter.style.nativeDecide false

/-- The anchor formulas reproduce every farm entry's cell. -/
theorem gen_anchors_valid : anchorsValid genTable = true := by native_decide

/-- Every farm entry, anchored by a concrete far pair, wins its
subtree without ever forcing the opponent onto its farm cell. -/
theorem farm_safe_gen : farmSafe genTable = true := by native_decide

/-- The forced-tree certificate at the base board. -/
theorem forced_seventeen : checkForced genTable 17 = true := by
  sorry

theorem plan_confined : planConfined genTable = true := by native_decide

/-- One forced run at the base board wins every board from the base
up. -/
theorem check_sound_uniform {t : Table} {n : ℕ} (hn : 17 ≤ n)
    (hconf : planConfined t = true)
    (hforce : checkForced t 17 = true)
    (hfarm : farmSafe t = true) :
    P1CanWin n ∅ ∅ := by
  sorry

end SquareAchievement
