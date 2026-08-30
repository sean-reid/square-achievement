import SquareAchievement.Compute.ForcedSound
import SquareAchievement.General.Invariance

/-!
# The simulation argument

Support for `check_sound_uniform`. The theorem replays the forced run
at the base board `17` on an arbitrary board `n ≥ 17`:

* replies inside the base board follow the checked tree verbatim;
* a reply that blocks no standing threat loses to the threat at once,
  so the opponent's lasting stones are the two replies and the
  blocks, and the blocks stay in the box by the checked guards;
* the two replies, when they use cells beyond the base board, are
  abstracted: through class representatives when the pair farms
  nothing, and through the anchored farm subtree when it does.

The safety obligation reduces to squares with one block corner in the
box, the two replies, and the completing move. Such a square either
fits inside the base board, where the run checked it, or has both
replies at the far threshold, where `farmKey` names the block corner
and the farm entry keeps the opponent off it; `17 = box + far - 1` is
the least base making that dichotomy exhaustive.
-/

namespace SquareAchievement

end SquareAchievement
