import SquareAchievement.Compute.Checker

/-!
# Executable properties for the uniform theorem

The strengthened soundness argument at the generation board needs
facts about the verification tree beyond winning. First, after the
opening and the second move, every strategy move either wins or
creates a threat, so the opponent's only unforced replies are the
first two; that is what keeps far play down to the two reply stones
and rules out voluntary grabs of a farm cell mid-plan. Second, branch
subtrees can be re-verified from preset openings on larger boards,
which anchors the farm entries that no run at the generation board
exercises. Both are checker variants, decided by evaluation.
-/

namespace SquareAchievement

/-- `go`, additionally demanding that every strategy move past the
second either wins or creates a threat. -/
def goForcing (t : Table) (squares : List (List Cell)) (n : ℕ) :
    ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match strategyMove t squares hist with
    | none => false
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then false
      else if hasSquareL squares (m :: p1) then true
      else if 2 < hist.length
          && (minThreat squares (m :: p1) ((m :: p1) ++ p2)).isNone then
        false
      else
        let hist' := hist ++ [m]
        let replies := (allCells n).filter fun c => !(hist'.contains c)
        if replies.isEmpty then false
        else replies.all fun r =>
          !completesL squares p2 r && goForcing t squares n fuel (hist' ++ [r])

/-- Every strategy move past the second wins or threatens, over the
whole verification tree of the `n` board. -/
def forcingComplete (t : Table) (n : ℕ) : Bool :=
  goForcing t (squaresList n) n (n * n + 1) []

/-- The checker from a preset history, for anchoring branch subtrees
on boards larger than the generation board. -/
def checkFrom (t : Table) (n : ℕ) (opening : List Cell) : Bool :=
  go t (squaresList n) n (n * n + 1) opening

end SquareAchievement
