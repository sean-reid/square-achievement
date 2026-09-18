import SquareAchievement.Compute.Table

/-!
# The executable checker

The exhaustive verification of a strategy table: replay the table
strategy against every reply sequence. The strategy plays reflexes
first, the least completion for either side, then the table lookup,
then the first unplayed plan cell; `check` returns `true` only if
every line ends in a first-player square. `check_sound` connects it to
`P1CanWin`.
-/

namespace SquareAchievement

/-- Corner lists of every winning square on the `n` board. -/
def squaresList (n : ℕ) : List (List Cell) :=
  (List.range n).flatMap fun s =>
    (List.range n).flatMap fun r =>
      (List.range n).filterMap fun c =>
        if 0 < s && r + s < n && c + s < n then
          some [(r, c), (r, c + s), (r + s, c), (r + s, c + s)]
        else none

def hasSquareL (squares : List (List Cell)) (stones : List Cell) : Bool :=
  squares.any fun sq => sq.all stones.contains

/-- Placing `m` (empty) would finish a square for `stones`. -/
def completesL (squares : List (List Cell)) (stones : List Cell) (m : Cell) : Bool :=
  squares.any fun sq =>
    sq.contains m && sq.all fun x => x == m || stones.contains x

def cellLt (a b : Cell) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The least cell where `mine` would complete a square, none blocked. -/
def minThreat (squares : List (List Cell)) (mine occupied : List Cell) : Option Cell :=
  squares.foldl (init := none) fun best sq =>
    match sq.filter (fun x => !mine.contains x) with
    | [m] =>
      if occupied.contains m then best
      else
        match best with
        | none => some m
        | some b => if cellLt m b then some m else some b
    | _ => best

/-- Stones at even positions (`true`) or odd positions (`false`) of the
move history. -/
def stonesOf (first : Bool) : List Cell → List Cell
  | [] => []
  | a :: rest => if first then a :: stonesOf false rest else stonesOf true rest

/-- Resolve an entry in the position after `hist`: follow a plan, or
play a quiet move and fork on the reply to it. Fueled recursion; the
guards in `go` validate whatever comes out, so running dry is safe. -/
def resolveEntry (p1 hist : List Cell) : ℕ → Entry → Option Cell
  | 0, _ => none
  | _, .plan cells => cells.find? fun c => !p1.contains c
  | fuel + 1, .quiet move branches =>
    if !p1.contains move then
      some move
    else do
      let reply ← hist[hist.idxOf move + 1]?
      let e ← lookup branches reply
      resolveEntry p1 hist fuel e

/-- The table strategy's move for the position after `hist` (first
player to move): reflexes, the lookup, then plan-following. -/
def strategyMove (t : Table) (squares : List (List Cell)) (hist : List Cell) :
    Option Cell :=
  let p1 := stonesOf true hist
  let p2 := stonesOf false hist
  let occ := p1 ++ p2
  match minThreat squares p1 occ with
  | some m => some m
  | none =>
  match minThreat squares p2 occ with
  | some m => some m
  | none =>
  if hist.isEmpty then some t.opening
  else do
    let o1 ← hist[1]?
    let x2 ← lookup t.x2 o1
    if !p1.contains x2 then
      some x2
    else do
      let o2 ← hist[hist.idxOf x2 + 1]?
      let table ← lookup t.scripts o1
      let entry ← lookup table o2
      resolveEntry p1 hist (hist.length + 1) entry

def onBoard (n : ℕ) (c : Cell) : Bool := c.1 < n && c.2 < n

def allCells (n : ℕ) : List Cell :=
  (List.range n).flatMap fun r => (List.range n).map fun c => (r, c)

/-- Exhaustive search: first player to move after `hist`; true iff
every second-player continuation loses. -/
def go (t : Table) (squares : List (List Cell)) (n : ℕ) :
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
      else
        let hist' := hist ++ [m]
        let replies := (allCells n).filter fun c => !(hist'.contains c)
        if replies.isEmpty then false
        else replies.all fun r =>
          !completesL squares p2 r && go t squares n fuel (hist' ++ [r])

/-- The table wins every game on the `n` board. -/
def check (t : Table) (n : ℕ) : Bool :=
  go t (squaresList n) n (n * n + 1) []

/-- Diagnostic twin of `go`: the first failing line, if any. Carries no
proof obligations; `check` and its soundness theorem are the authority. -/
def goTrace (t : Table) (squares : List (List Cell)) (n : ℕ) :
    ℕ → List Cell → Option (List Cell)
  | 0, hist => some hist
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match strategyMove t squares hist with
    | none => some hist
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then some (hist ++ [m])
      else if hasSquareL squares (m :: p1) then none
      else
        let hist' := hist ++ [m]
        let replies := (allCells n).filter fun c => !(hist'.contains c)
        if replies.isEmpty then some hist'
        else
          replies.findSome? fun r =>
            if completesL squares p2 r then some (hist' ++ [r])
            else goTrace t squares n fuel (hist' ++ [r])

/-- The first failing line on the `n` board, if any. -/
def trace (t : Table) (n : ℕ) : Option (List Cell) :=
  goTrace t (squaresList n) n (n * n + 1) []

end SquareAchievement
