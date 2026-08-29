import SquareAchievement.Compute.Checker

/-!
# The byte-board checker

A fast twin of `check` for fork-free tables: the position rides along
as a `ByteArray` (one byte per cell, 0 empty, 1 P1, 2 P2) and squares
become flat `UInt32` corner-index tables, so the hot loops touch no
arbitrary-precision arithmetic and allocate nothing. The history list
collapses to the two replies the general table consults: the first
reply, and the reply after P1's tabled second move. The fast checker
serves the executable only, cross-checked against the certified `check`;
`check` remains the sole citation in soundness proofs.
-/

namespace SquareAchievement

/-- Sentinel cell index meaning "no threat". -/
def noCell : UInt32 := 0xFFFFFFFF

/-- Corner cell indices of every square, four per square. -/
def cornersIdx (n : ℕ) : Array UInt32 := Id.run do
  let mut a : Array UInt32 := #[]
  for sq in squaresList n do
    for c in sq do
      a := a.push (UInt32.ofNat (c.1 * n + c.2))
  return a

/-- Ids of the squares through each cell, indexed by cell number. -/
def squaresAt (n : ℕ) : Array (List UInt32) := Id.run do
  let mut arr : Array (List UInt32) := .replicate (n * n) []
  let mut s : UInt32 := 0
  for sq in squaresList n do
    for c in sq do
      let i := c.1 * n + c.2
      arr := arr.set! i (s :: arr[i]!)
    s := s + 1
  return arr

/-- The least cell where the side holding `mine` stones would complete
a square, `noCell` when every such cell is taken or absent. -/
def minThreatB (corners : Array UInt32) (board : ByteArray)
    (mine : UInt8) : UInt32 := Id.run do
  let nsq := corners.size / 4
  let mut best := noCell
  for s in [0:nsq] do
    let b := 4 * s
    let c0 := corners[b]!
    let c1 := corners[b + 1]!
    let c2 := corners[b + 2]!
    let c3 := corners[b + 3]!
    let v0 := board.get! c0.toNat
    let v1 := board.get! c1.toNat
    let v2 := board.get! c2.toNat
    let v3 := board.get! c3.toNat
    let m0 : UInt32 := if v0 == mine then 0 else 1
    let m1 : UInt32 := if v1 == mine then 0 else 1
    let m2 : UInt32 := if v2 == mine then 0 else 1
    let m3 : UInt32 := if v3 == mine then 0 else 1
    if m0 + m1 + m2 + m3 == 1 then
      let cell := if m0 == 1 then c0 else if m1 == 1 then c1
        else if m2 == 1 then c2 else c3
      let v := if m0 == 1 then v0 else if m1 == 1 then v1
        else if m2 == 1 then v2 else v3
      if v == 0 && cell < best then
        best := cell
  return best

/-- Placing a stone of `mine` on the (empty) cell `i` finishes a square. -/
def completesB (corners : Array UInt32) (atSq : Array (List UInt32))
    (board : ByteArray) (mine : UInt8) (i : UInt32) : Bool :=
  (atSq[i.toNat]?.getD []).any fun s =>
    let b := 4 * s.toNat
    let own := fun (c : UInt32) => c == i || board.get! c.toNat == mine
    own corners[b]! && own corners[b + 1]! &&
      own corners[b + 2]! && own corners[b + 3]!

/-- P1 holds the cell; false off the board. -/
def heldP1 (board : ByteArray) (n : ℕ) (c : Cell) : Bool :=
  let i := c.1 * n + c.2
  i < board.size && board.get! i == 1

/-- The strategy's move for a fork-free table, driven by the two
remembered replies instead of a history list. -/
def strategyMoveB (t : Table) (corners : Array UInt32) (n : ℕ)
    (o1 o2 : Option Cell) (board : ByteArray) : Option Cell :=
  let t1 := minThreatB corners board 1
  if t1 != noCell then some (t1.toNat / n, t1.toNat % n)
  else
    let t2 := minThreatB corners board 2
    if t2 != noCell then some (t2.toNat / n, t2.toNat % n)
    else
      match o1 with
      | none => some t.opening
      | some o1c => do
        let x2 ← lookup t.box t.x2 o1c
        if !heldP1 board n x2 then
          some x2
        else do
          let o2c ← o2
          let table ← lookup t.box t.scripts o1c
          let entry ← lookup t.box table o2c
          match entry with
          | .plan cells => cells.find? fun c => !heldP1 board n c
          | .quiet .. => none

/-- Exhaustive search for fork-free tables. `o1` is the first reply;
`o2` is the reply that follows P1's tabled second move, however that
move arrived. `free` counts empty cells. -/
def goB (t : Table) (corners : Array UInt32) (atSq : Array (List UInt32))
    (n : ℕ) :
    ℕ → Option Cell → Option Cell → ByteArray → ℕ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, o1, o2, board, free => Id.run do
    match strategyMoveB t corners n o1 o2 board with
    | none => return false
    | some m =>
      if !onBoard n m then return false
      let mi := UInt32.ofNat (m.1 * n + m.2)
      if board.get! mi.toNat != 0 then return false
      if completesB corners atSq board 1 mi then return true
      if free == 1 then return false
      let board := board.set! mi.toNat 1
      let justX2 := o2 == none && (o1.bind (lookup t.box t.x2)) == some m
      for i in [0:n * n] do
        if board.get! i == 0 then
          if completesB corners atSq board 2 (UInt32.ofNat i) then
            return false
          let r : Cell := (i / n, i % n)
          let o1' := if o1 == none then some r else o1
          let o2' := if justX2 then some r else o2
          if !(goB t corners atSq n fuel o1' o2' (board.set! i 2)
              (free - 2)) then
            return false
      return true

/-- The byte-board checker for fork-free tables. -/
def checkFast (t : Table) (n : ℕ) : Bool :=
  goB t (cornersIdx n) (squaresAt n) n (n * n + 1) none none
    (ByteArray.mk (.replicate (n * n) 0)) (n * n)

/-- Diagnostic twin of `goB`: the first failing line, if any. Carries
the moves so far in reverse; no proof obligations. -/
def goBTrace (t : Table) (corners : Array UInt32)
    (atSq : Array (List UInt32)) (n : ℕ) :
    ℕ → Option Cell → Option Cell → ByteArray → ℕ → List Cell →
      Option (List Cell)
  | 0, _, _, _, _, hist => some hist.reverse
  | fuel + 1, o1, o2, board, free, hist => Id.run do
    match strategyMoveB t corners n o1 o2 board with
    | none => return some hist.reverse
    | some m =>
      if !onBoard n m then return some (m :: hist).reverse
      let mi := UInt32.ofNat (m.1 * n + m.2)
      if board.get! mi.toNat != 0 then return some (m :: hist).reverse
      if completesB corners atSq board 1 mi then return none
      if free == 1 then return some (m :: hist).reverse
      let board := board.set! mi.toNat 1
      let justX2 := o2 == none && (o1.bind (lookup t.box t.x2)) == some m
      let hist := m :: hist
      for i in [0:n * n] do
        if board.get! i == 0 then
          let r : Cell := (i / n, i % n)
          if completesB corners atSq board 2 (UInt32.ofNat i) then
            return some (r :: hist).reverse
          let o1' := if o1 == none then some r else o1
          let o2' := if justX2 then some r else o2
          match goBTrace t corners atSq n fuel o1' o2'
              (board.set! i 2) (free - 2) (r :: hist) with
          | some line => return some line
          | none => pure ()
      return none

/-- The first failing line on the `n` board via the byte-board search. -/
def traceFast (t : Table) (n : ℕ) : Option (List Cell) :=
  goBTrace t (cornersIdx n) (squaresAt n) n (n * n + 1) none none
    (ByteArray.mk (.replicate (n * n) 0)) (n * n) []
