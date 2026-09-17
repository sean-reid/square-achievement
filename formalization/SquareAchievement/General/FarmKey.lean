import SquareAchievement.Compute.Table

/-!
# The hidden corner of a reply pair

Two second-player stones beyond `board (2 * box)` share a square with
the corner box only as two corners of a square whose third corner is
a box cell: that cell is the pair's hidden corner. `farmKey` returns
it as a `Key.farm`, or `none` when the pair has no hidden corner.
-/

namespace SquareAchievement

/-- One orientation of the test: `p` is aligned with the box, its row
or its column indexed below `box`, and `q` completes a square whose
remaining box corner is returned. Truncated subtraction is guarded. -/
def farmCase (box : ℕ) (p q : Cell) : Option Key :=
  if p.1 < box && p.2 == q.2 && p.1 < q.1 && q.1 - p.1 ≤ p.2
      && p.2 - (q.1 - p.1) < box then
    some (.farm (p.1, p.2 - (q.1 - p.1)))
  else if p.2 < box && p.1 == q.1 && p.2 < q.2 && q.2 - p.2 ≤ p.1
      && p.1 - (q.2 - p.2) < box then
    some (.farm (p.1 - (q.2 - p.2), p.2))
  else if p.1 < box && q.2 < box && 1 ≤ p.2 - q.2 && p.2 - q.2 == q.1 - p.1 then
    some (.farm (p.1, q.2))
  else none

/-- The hidden corner of the pair `o1`, `o2`, both beyond
`board (2 * box)`, in either order. -/
def farmKey (box : ℕ) (o1 o2 : Cell) : Option Key :=
  if max o1.1 o1.2 < 2 * box || max o2.1 o2.2 < 2 * box then none
  else
    match farmCase box o1 o2 with
    | some k => some k
    | none => farmCase box o2 o1

end SquareAchievement
