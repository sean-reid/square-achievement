import SquareAchievement.Compute.Uniform

/-!
# Farm safety at the anchors

Three checks cover every farm pair a larger board can throw at the
strategy, each an anchored hot-guarded run on the anchor board. A
farm pair holds at most one stone of the base board, always
box-aligned with one far coordinate; the other stone, and both stones
of a fully far pair, are interchangeable with any stand-in outside
`board 12`, so one anchor per farm cell suffices:

* `farFarmSafe`: both replies far, anchored by the default-class
  pair, one run per farm cell;
* `exactFarmSafe`: a box-aligned near first reply, anchored with the
  real cell first and its aligned partner second;
* `farNearFarmSafe`: a box-aligned near second reply, anchored with
  the aligned partner first and the real cell second.

The iterations run over coordinate ranges, not table keys, so the
checks are complete by construction.
-/

namespace SquareAchievement

/-- The board every anchored run is played on. The anchors of
`ExactFarm` place a stone at coordinate `17`, and a default-class
anchor reaches row `hot.1 + 17 - hot.2 ≤ 22`, so `23` is the least
board holding every anchor pair. The runs would prove the same on any
larger board; the size only bounds the fuel and the square scan. -/
def anchorBoard : ℕ := 23

/-- One anchored hot-guarded run. -/
def anchorRun (t : Table) (o1 o2 hot : Cell) : Bool :=
  farmKey t.box o1 o2 == some (.farm hot) &&
    (match lookup t.box t.x2 o1 with
     | none => false
     | some x2 =>
       goForced t (squaresList anchorBoard) anchorBoard (some hot)
         (anchorBoard * anchorBoard + 1) [t.opening, o1, x2, o2])

/-- Both replies far: the default-class anchor, one per farm cell. -/
def farFarmSafe (t : Table) : Bool :=
  (List.range t.box).all fun h1 =>
    (List.range t.box).all fun h2 =>
      anchorRun t (h1 + 17 - h2, 17) (h1 + 17 - h2, h2) (h1, h2)

/-- A box-aligned near first reply, every farm cell whose square
escapes the base board. -/
def exactFarmSafe (t : Table) : Bool :=
  (List.range t.box).all fun a =>
    (List.range 17).all fun w =>
      (List.range t.box).all fun h =>
        (if 2 * t.box ≤ w && 17 ≤ a + w - h then
          anchorRun t (a, w) (a + w - h, w) (a, h) &&
            anchorRun t (w, a) (w, a + w - h) (h, a)
        else true)

/-- A box-aligned near second reply, same iteration with the aligned
partner moved to the first slot. -/
def farNearFarmSafe (t : Table) : Bool :=
  (List.range t.box).all fun a =>
    (List.range 17).all fun w =>
      (List.range t.box).all fun h =>
        (if 2 * t.box ≤ w && 17 ≤ a + w - h then
          anchorRun t (a + w - h, w) (a, w) (a, h) &&
            anchorRun t (w, a + w - h) (w, a) (h, a)
        else true)

end SquareAchievement
