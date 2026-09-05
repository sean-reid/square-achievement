import Threshold.General.Wrapper
import Threshold.Data.TableGen

/-!
# The uniform theorem

One forced-tree run at the base board, together with executable table
properties, wins every larger board at once. The base is
`17 = box + far - 1`: an opponent square with a corner in the box and
a stone below the far threshold fits inside the base board, where the
run has checked it, so every square escaping the base has both reply
stones at the far threshold or beyond, which is exactly the territory
the farm entries govern. The proof replays the base run: near
replies verbatim, unforced replies answered by the standing threat,
the two reply stones abstracted through class representatives or, for
farming pairs, through the anchored farm subtrees of `ExactFarm`,
whose three certificates range over coordinates and so cover every
farm pair a larger board can produce.
-/

namespace SquareAchievement

set_option linter.style.nativeDecide false

/-- Both replies far: one anchored run per farm cell. -/
theorem far_farm_safe_gen : farFarmSafe genTable = true := by
  native_decide

/-- A box-aligned near first reply, every escaping farm cell. -/
theorem exact_farm_safe_gen : exactFarmSafe genTable = true := by
  native_decide

/-- A box-aligned near second reply, every escaping farm cell. -/
theorem far_near_farm_safe_gen : farNearFarmSafe genTable = true := by
  native_decide

/-- The forced-tree certificate at the base board. -/
theorem forced_seventeen : checkForced genTable 17 = true := by
  native_decide

theorem plan_confined : planConfined genTable = true := by native_decide

/-- The x2 map avoids the opening and keys only generation-board
cells. -/
theorem x2_sane_gen : x2Sane genTable = true := by native_decide

/-- One forced run at the base board wins every board from the base
up. -/
theorem check_sound_uniform {t : Table} {n : ℕ} (hn : 17 ≤ n)
    (hbox : t.box = 6)
    (hconf : planConfined t = true)
    (hforce : checkForced t 17 = true)
    (hfar : farFarmSafe t = true)
    (hexact : exactFarmSafe t = true)
    (hfarnear : farNearFarmSafe t = true)
    (hsane : x2Sane t = true) :
    P1CanWin n ∅ ∅ :=
  check_sound_uniform_aux hn hbox hconf hforce hfar hexact hfarnear hsane

end SquareAchievement
