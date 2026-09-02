import SquareAchievement.Compute.Checker

/-!
# The forced-tree checker

The game under a forcing table is narrow: past the second reply,
every strategy move threatens, so the opponent either blocks or loses
to the threat on the next move. `goForced` verifies exactly that
shape. The two reply levels are enumerated in full; beyond them each
node makes two whole-board scans, one to collect the strategy's
threat cells and one to confirm the opponent can complete nothing,
and recurses only on the blocks. `goForced_sound` covers every
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

/-- The forced-tree checker. Full enumeration at the two reply
levels; past them the strategy must win or threaten from the box,
the opponent must have no completion, and only the block replies
recurse. `hot`, when given, must never be the only block. -/
def goForced (t : Table) (squares : List (List Cell)) (n : ℕ)
    (hot : Option Cell) : ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match strategyMove t squares hist with
    | none => false
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then false
      else if hasSquareL squares (m :: p1) then true
      else if !inBox t.box m then false
      else if !(threatsL squares p2 ((m :: p1) ++ p2)).isEmpty then false
      else
        let hist' := hist ++ [m]
        if hist.length ≤ 2 then
          let replies := (allCells n).filter fun c => !(hist'.contains c)
          if replies.isEmpty then false
          else replies.all fun r => goForced t squares n hot fuel (hist' ++ [r])
        else
          let ths := threatsL squares (m :: p1) ((m :: p1) ++ p2)
          if ths.isEmpty then false
          else if !ths.all (inBox t.box) then false
          else if hot.any (fun h => ths.all (· == h)) then false
          else ths.all fun z => goForced t squares n hot fuel (hist' ++ [z])

/-- The table wins the `n` board through pure forcing. -/
def checkForced (t : Table) (n : ℕ) : Bool :=
  goForced t (squaresList n) n none (n * n + 1) []

/-- The board every anchored run is played on. The anchors of
`ExactFarm` place a stone at coordinate `17`, and a default-class
anchor reaches row `hot.1 + 17 - hot.2 ≤ 22`, so `23` is the least
board holding every anchor pair. The runs would prove the same on any
larger board; the size only bounds the fuel and the square scan. -/
def anchorBoard : ℕ := 23

mutual
  /-- Every cell an entry can ever play lies inside the given box. -/
  def entryConfined (box : ℕ) : Entry → Bool
    | .plan cells => cells.all (onBoard box)
    | .quiet move branches => onBoard box move && branchesConfined box branches

  def branchesConfined (box : ℕ) : List (Key × Entry) → Bool
    | [] => true
    | (_, e) :: rest => entryConfined box e && branchesConfined box rest
end

/-- P1's plan never leaves the corner box: the opening, every second
move, and every cell any entry can play lie inside `board t.box`. -/
def planConfined (t : Table) : Bool :=
  onBoard t.box t.opening &&
  (t.x2.all fun e => onBoard t.box e.2) &&
  t.scripts.all fun e => e.2.all fun e2 => entryConfined t.box e2.2

end SquareAchievement
