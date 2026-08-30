import SquareAchievement.Compute.Uniform

/-!
# Farm safety for far-reaching exact keys

An exact first reply with one box coordinate and one coordinate at
the far threshold can farm with an off-board partner, and the pair's
square escapes the base board exactly when the anchored partner's far
coordinate reaches the base. Class branches carry farm entries and
`farmSafe` checks them; the exact branches carry none, so their
ordinary plans must already avoid the farm cell. This check runs the
anchored subtree for every such key and every escaping farm cell,
under the same never-the-only-block guard.
-/

namespace SquareAchievement

/-- The anchored hot-safety run for one exact key and one farm cell. -/
def exactAnchorSafe (t : Table) (c hot : Cell) : Bool :=
  match anchorPair (.cell c) hot with
  | none => false
  | some (o1, o2) =>
    farmKey t.box o1 o2 == some (.farm hot) &&
      (match lookup t.box t.x2 o1 with
       | none => false
       | some x2 =>
         goForced t (squaresList anchorBoard) anchorBoard (some hot)
           (anchorBoard * anchorBoard + 1) [t.opening, o1, x2, o2])

/-- Every class branch is safe for every farm cell its anchor
realizes. Iterating over all box cells rather than over the entries
present makes the check complete by construction: a real far pair
whose farm cell some class branch can reach is covered whether or not
the table stored an entry for it. -/
def classFarmSafe (t : Table) : Bool :=
  t.scripts.all fun kt =>
    match kt.1 with
    | .row _ | .col _ | .dflt =>
      (List.range t.box).all fun h1 =>
        (List.range t.box).all fun h2 =>
          match anchorPair kt.1 (h1, h2) with
          | none => true
          | some (o1, o2) =>
            if farmKey t.box o1 o2 == some (.farm (h1, h2)) then
              match lookup t.box t.x2 o1 with
              | none => false
              | some x2 =>
                goForced t (squaresList anchorBoard) anchorBoard
                  (some (h1, h2)) (anchorBoard * anchorBoard + 1)
                  [t.opening, o1, x2, o2]
            else true
    | _ => true

/-- Every box-aligned cell of the base board with one far coordinate
is safe for every farm cell whose square escapes the base board. The
iteration runs over cells, not table keys: a first reply on the base
board beyond the generation board farms all the same. -/
def exactFarmSafe (t : Table) : Bool :=
  (List.range t.box).all fun a =>
    (List.range 17).all fun w =>
      (List.range t.box).all fun h =>
        (if 2 * t.box ≤ w && 17 ≤ a + w - h then
          exactAnchorSafe t (a, w) (a, h)
        else true) &&
        (if 2 * t.box ≤ w && 17 ≤ a + w - h then
          exactAnchorSafe t (w, a) (h, a)
        else true)

end SquareAchievement
