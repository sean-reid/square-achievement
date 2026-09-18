import SquareAchievement.Compute.ForcedSound
import SquareAchievement.Plus.Rule

/-!
# The rule's certificates for every larger board

The uniform argument replays a forced run on the anchor board `23` on
every board from `17` up. Replies inside the base board `17` are read
verbatim; a reply beyond it is abstracted, and the rule reads only the
abstraction, so the run from a stand-in pair is the run from the real
pair. Three families of anchored runs, with the hidden corner as a
guard, cover every pair that has one:

* both replies far: the pair `(h1 + 17, h2 + 17)`, `(h1 + 17, h2)`
  has hidden corner `(h1, h2)`, and both stones lie beyond the base
  board;
* a near aligned first reply `(a, w)` with `12 ≤ w < 17`, whose far
  partner `(a + w - h, w)` completes the square through `(a, h)`;
* the mirror, with the aligned member second.

A pair with no hidden corner is replaced by the stand-ins `(22, 22)`
and `(22, 21)`, which have none with each other or with any near
stone, and the run from those stand-ins is part of the base run.
-/

namespace SquareAchievement.Plus

/-- The board every anchored run is played on. -/
def anchorBoard : ℕ := 23

/-- The rule's forced run on the anchor board from a reply pair, with
the hidden corner as a guard. -/
def anchorRun (o1 o2 hot : Cell) : Bool :=
  decide (farmKey box o1 o2 = some (.farm hot)) &&
    goForcedS plusMove box (squaresList anchorBoard) anchorBoard (some hot)
      (anchorBoard * anchorBoard + 1) [opening, o1, secondMove o1, o2]

/-- Both replies far: one anchored run per corner cell. -/
def farAnchorsSafe : Bool :=
  (List.range box).all fun h1 =>
    (List.range box).all fun h2 =>
      anchorRun (h1 + 17, h2 + 17) (h1 + 17, h2) (h1, h2)

/-- A near aligned first reply, every corner cell whose square escapes
the base board. -/
def exactAnchorsSafe : Bool :=
  (List.range box).all fun a =>
    (List.range 17).all fun w =>
      (List.range box).all fun h =>
        (if 2 * box ≤ w && 17 ≤ a + w - h then
          anchorRun (a, w) (a + w - h, w) (a, h) &&
            anchorRun (w, a) (w, a + w - h) (h, a)
        else true)

/-- A near aligned second reply, the same iteration with the partner
first. -/
def farNearAnchorsSafe : Bool :=
  (List.range box).all fun a =>
    (List.range 17).all fun w =>
      (List.range box).all fun h =>
        (if 2 * box ≤ w && 17 ≤ a + w - h then
          anchorRun (a + w - h, w) (a, w) (a, h) &&
            anchorRun (w, a + w - h) (w, a) (h, a)
        else true)

/-- The positions the three families run, as `(o1, o2, hot)`: the far
family, then for each aligned near reply its two exact anchors and
their two mirrors. -/
def anchorPositions : List (Cell × Cell × Cell) :=
  ((List.range box).flatMap fun h1 => (List.range box).map fun h2 =>
    ((h1 + 17, h2 + 17), (h1 + 17, h2), (h1, h2))) ++
  ((List.range box).flatMap fun a => (List.range 17).flatMap fun w =>
    (List.range box).flatMap fun h =>
      if 2 * box ≤ w && 17 ≤ a + w - h then
        [((a, w), (a + w - h, w), (a, h)), ((w, a), (w, a + w - h), (h, a)),
          ((a + w - h, w), (a, w), (a, h)), ((w, a + w - h), (w, a), (h, a))]
      else [])

end SquareAchievement.Plus
