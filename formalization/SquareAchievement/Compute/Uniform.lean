import SquareAchievement.Compute.Checker

/-!
# The forced-tree checker

The game under a forcing table is narrow: past the second reply,
every strategy move threatens, so the opponent either blocks or loses
to the threat on the next move. `goForced` verifies exactly that
shape. The two reply levels are enumerated in full; beyond them each
node makes two whole-board scans, one to collect the strategy's
threat cells and one to confirm the opponent can complete nothing,
and recurses only on the blocks. `goForcedS_sound` covers every
non-blocking reply with a single two-move argument, so the checker
never has to visit them.

The node guards double as the uniform theorem's hypotheses: every
non-winning move and every threat cell must lie in the corner box,
which keeps the opponent's forced blocks in the box, and the optional
`hot` cell must never be the only block, which is the farm-safety
condition checked from anchored positions.
-/

namespace SquareAchievement

/-- Both coordinates inside the corner box. -/
def inBox (box : ℕ) (c : Cell) : Bool := c.1 < box && c.2 < box

/-- Every cell where `mine` would complete a square, unblocked, one
entry per square. -/
def threatsL (squares : List (List Cell)) (mine occupied : List Cell) :
    List Cell :=
  squares.filterMap fun sq =>
    match sq.filter (fun x => !mine.contains x) with
    | [m] => if occupied.contains m then none else some m
    | _ => none

/-- A strategy: the first player's move after a history, given the
board's squares. The table strategy is one instance; a rule is another. -/
abbrev Strategy := List (List Cell) → List Cell → Option Cell

/-- The forced-tree checker for any strategy. Full enumeration at the
two reply levels; past them the strategy must win or threaten from the
box, the opponent must have no completion, and only the block replies
recurse. `hot`, when given, must never be the only block. -/
def goForcedS (σ : Strategy) (box : ℕ) (squares : List (List Cell)) (n : ℕ)
    (hot : Option Cell) : ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match σ squares hist with
    | none => false
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then false
      else if hasSquareL squares (m :: p1) then true
      else if !inBox box m then false
      else if !(threatsL squares p2 ((m :: p1) ++ p2)).isEmpty then false
      else
        let hist' := hist ++ [m]
        if hist.length ≤ 2 then
          let replies := (allCells n).filter fun c => !(hist'.contains c)
          if replies.isEmpty then false
          else replies.all fun r => goForcedS σ box squares n hot fuel (hist' ++ [r])
        else
          let ths := threatsL squares (m :: p1) ((m :: p1) ++ p2)
          if ths.isEmpty then false
          else if !ths.all (inBox box) then false
          else if hot.any (fun h => ths.all (· == h)) then false
          else ths.all fun z => goForcedS σ box squares n hot fuel (hist' ++ [z])

/-- The strategy wins the `n` board through pure forcing. -/
def checkForcedS (σ : Strategy) (box n : ℕ) : Bool :=
  goForcedS σ box (squaresList n) n none (n * n + 1) []

end SquareAchievement
