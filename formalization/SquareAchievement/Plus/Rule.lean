import SquareAchievement.Compute.Checker
import SquareAchievement.General.FarmKey

/-!
# The plus rule

A strategy stated without a lookup table. A *plus* is a stone the
first player holds together with the four cells at distance `s` from
it along the axes; playing an arm makes three corners of a side-`s`
square with the centre and a neighbouring arm, so the second player
must block the diagonal cell, and the last arm makes three corners of
two squares at once. A *tempo move* is a single forcing move: once it
is played the second player has no threat and the first player has
exactly one threat cell. The block may leave the second player with a
threat, which the next move of the line takes.

The rule. Open at `(2, 2)`. Reply below it at `(3, 2)`, except against
seven first replies touching the opening pair, where a fixed diagram
gives the second move. Take a win or a block by reflex whenever one
exists. Otherwise follow the line chosen at the second reply: at most
three tempo moves followed by a plus of side `1` or `2`, preferring
fewer tempo moves, then fewer arms not held, then the smaller side,
then the smaller centre, and never making a threat whose only block
is the hidden corner of the second player's two free stones.

The rule reads only an abstraction of the position: the first player's
stones (always in the `6 × 6` corner), the second player's stones
inside the `17 × 17` base board, and the hidden corner of the free
pair if any. A stone beyond the base board shares no square with two
corner stones, so it matters only through a square with the hidden
corner, and that is what the abstraction records.
-/

namespace SquareAchievement.Plus

/-- The corner region every plan stays in. -/
def box : ℕ := 6

/-- The base board: stones inside it are read verbatim. -/
def base : ℕ := 17

def opening : Cell := (2, 2)

/-- The second move: `(3, 2)` unless the first reply is one of seven
cells touching the opening pair. -/
def secondMove (o1 : Cell) : Cell :=
  if o1 = (1, 3) ∨ o1 = (2, 3) ∨ o1 = (3, 3) then (2, 1)
  else if o1 = (2, 1) ∨ o1 = (4, 3) then (2, 3)
  else if o1 = (3, 1) ∨ o1 = (3, 2) then (1, 2)
  else (3, 2)

/-- The squares through two given corners `a` and `b` within `board k`,
as corner lists: two if the corners share a row or a column, one if
they are diagonal, none otherwise. -/
def squaresThrough (k : ℕ) (a b : Cell) : List (List Cell) :=
  if a = b then []
  else if a.1 = b.1 then
    let d := max a.2 b.2 - min a.2 b.2
    let c := min a.2 b.2
    let r := a.1
    (if r + d < k then [[(r, c), (r, c + d), (r + d, c), (r + d, c + d)]] else []) ++
    (if d ≤ r then [[(r - d, c), (r - d, c + d), (r, c), (r, c + d)]] else [])
  else if a.2 = b.2 then
    let d := max a.1 b.1 - min a.1 b.1
    let r := min a.1 b.1
    let c := a.2
    (if c + d < k then [[(r, c), (r, c + d), (r + d, c), (r + d, c + d)]] else []) ++
    (if d ≤ c then [[(r, c - d), (r, c), (r + d, c - d), (r + d, c)]] else [])
  else
    let dr := max a.1 b.1 - min a.1 b.1
    let dc := max a.2 b.2 - min a.2 b.2
    if dr = dc then
      let r := min a.1 b.1
      let c := min a.2 b.2
      [[(r, c), (r, c + dr), (r + dr, c), (r + dr, c + dr)]]
    else []

/-- Cells where `mine` is one stone short of a square inside `board k`,
unblocked: found through pairs of stones, so the cost grows with the
stones on the board and not with the board. -/
def threatsIn (k : ℕ) (mine occ : List Cell) : List Cell :=
  let cands := mine.flatMap fun a => mine.flatMap fun b =>
    if cellLt a b then
      (squaresThrough k a b).filterMap fun sq =>
        match sq.filter (fun x => !mine.contains x) with
        | [m] => if occ.contains m then none else some m
        | _ => none
    else []
  (cands.foldl (fun acc m => if acc.contains m then acc else m :: acc) []).mergeSort
    fun x y => cellLt x y || x == y

/-- The first player's threats: squares inside the corner. -/
def myThreats (p1 occ : List Cell) : List Cell := threatsIn box p1 occ

/-- The second player's threats among the near stones: squares inside
the base board. -/
def theirThreats (p2 occ : List Cell) : List Cell := threatsIn base p2 occ

def boxCells : List Cell := allCells box

/-- The abstract position the rule reads. -/
structure Abs where
  p1 : List Cell
  p2 : List Cell
  hot : Option Cell

/-- Play `moves` under forcing semantics, as the checker judges them:
after each move the second player has no threat, the move makes at
least one, two threats win, and one threat is blocked, never on the
hidden corner. -/
def forceLine (a : Abs) : List Cell → Bool
  | [] => false
  | m :: rest =>
    if a.p1.contains m || a.p2.contains m then false
    else
      let p1 := m :: a.p1
      if !(theirThreats a.p2 (p1 ++ a.p2)).isEmpty then false
      else
        match myThreats p1 (p1 ++ a.p2) with
        | [] => false
        | [b] => if a.hot == some b then false else forceLine ⟨p1, b :: a.p2, a.hot⟩ rest
        | _ => true

/-- The four arms of the plus of side `s` at `c`. -/
def arms (c : Cell) (s : ℕ) : List Cell :=
  [(c.1 - s, c.2), (c.1 + s, c.2), (c.1, c.2 - s), (c.1, c.2 + s)]

/-- Arms lie in the box; the subtraction must not have wrapped. -/
def armsOk (c : Cell) (s : ℕ) : Bool :=
  s ≤ c.1 && s ≤ c.2 && c.1 + s < box && c.2 + s < box

/-- All orderings of a short list: by the position of the first
element, then recursively. -/
def permsAux : ℕ → List Cell → List (List Cell)
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | n + 1, xs => xs.flatMap fun x => (permsAux n (xs.erase x)).map (x :: ·)

def perms (xs : List Cell) : List (List Cell) := permsAux xs.length xs

/-- The key of a plus: remaining arms, side, centre. -/
abbrev PlusKey := ℕ × ℕ × Cell

def keyLe (a b : PlusKey) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 ||
    (a.2.1 == b.2.1 && (cellLt a.2.2 b.2.2 || a.2.2 == b.2.2))))

def lineLe : List Cell → List Cell → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => cellLt x y || (x == y && lineLe xs ys)

/-- Order candidate lines: by plus key, then by the line itself. -/
def candLe (a b : PlusKey × List Cell) : Bool :=
  (keyLe a.1 b.1 && !(keyLe b.1 a.1 && !(a.1 == b.1))) &&
    (!(a.1 == b.1) || lineLe a.2 b.2)

/-- Every plus the first player can complete by force from `a`, with
its key and its arm order. -/
def winningPluses (a : Abs) : List (PlusKey × List Cell) :=
  let cands := a.p1.flatMap fun c =>
    [1, 2].filterMap fun s =>
      if !armsOk c s then none
      else
        let todo := (arms c s).filter fun x => !a.p1.contains x
        if todo.isEmpty || todo.any a.p2.contains then none
        else
          match (perms todo).find? (forceLine a) with
          | some order => some ((todo.length, s, c), order)
          | none => none
  cands.mergeSort candLe

/-- Tempo moves from `a`: exactly one threat cell, and it is not the
hidden corner. -/
def tempoMoves (a : Abs) : List (Cell × Abs) :=
  boxCells.filterMap fun m =>
    if a.p1.contains m || a.p2.contains m then none
    else
      let p1 := m :: a.p1
      if !(theirThreats a.p2 (p1 ++ a.p2)).isEmpty then none
      else
        match myThreats p1 (p1 ++ a.p2) with
        | [b] => if a.hot == some b then none else some (m, ⟨p1, b :: a.p2, a.hot⟩)
        | _ => none

/-- Strict order on plus keys. -/
def keyLt (a b : PlusKey) : Bool := keyLe a b && !(a == b)

/-- The best line within `d` tempo moves: fewest tempo moves first,
then the plus key, ties to the earliest position in search order. A
position where the second player already threatens offers no plus. Returns
the whole line, tempo moves then arms. -/
def bestLine (a : Abs) : ℕ → List (Abs × List Cell) → Option (List Cell)
  | _, [] => none
  | d, frontier =>
    let found := frontier.filterMap fun (b, pre) =>
      if !(theirThreats b.p2 (b.p1 ++ b.p2)).isEmpty then none
      else
        match winningPluses b with
        | (key, order) :: _ => some (key, pre ++ order)
        | [] => none
    let best := found.foldl (fun acc c =>
      match acc with
      | none => some c
      | some b => if keyLt c.1 b.1 then some c else some b) none
    match best with
    | some (_, line) => some line
    | none =>
      match d with
      | 0 => none
      | d + 1 =>
        bestLine a d (frontier.flatMap fun (b, pre) =>
          (tempoMoves b).map fun (m, b') => (b', pre ++ [m]))

/-- The line committed to at the second reply. -/
def lineOf (a : Abs) : Option (List Cell) := bestLine a 3 [(a, [])]

/-- The abstraction of a history: the first player's stones, the
second player's stones inside the base board, and the hidden corner of
the free pair. -/
def abstractOf (hist : List Cell) : Abs :=
  let p2 := (stonesOf false hist).filter (onBoard base)
  let hot := match hist[1]?, hist[3]? with
    | some o1, some o2 =>
      match farmKey box o1 o2 with
      | some (.farm h) => some h
      | _ => none
    | _, _ => none
  ⟨stonesOf true hist, p2, hot⟩

/-- The rule's move after `hist` (first player to move): reflexes on
the abstract position, the opening, the second move, then the first
unplayed cell of the line committed to at the second reply. -/
def plusMove (_ : List (List Cell)) (hist : List Cell) : Option Cell :=
  let a := abstractOf hist
  let occ := a.p1 ++ a.p2
  match myThreats a.p1 occ with
  | m :: _ => some m
  | [] =>
  match theirThreats a.p2 occ with
  | m :: _ => some m
  | [] =>
  if hist.isEmpty then some opening
  else do
    let o1 ← hist[1]?
    let x2 := secondMove o1
    if !a.p1.contains x2 then some x2
    else do
      let line ← lineOf (abstractOf (hist.take 4))
      line.find? fun c => !a.p1.contains c

end SquareAchievement.Plus
