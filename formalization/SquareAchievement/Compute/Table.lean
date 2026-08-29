import SquareAchievement.Core.Square

/-!
# Strategy tables

The executable form of a generated strategy: an opening move, a second
move per first reply, and a forcing plan per (first reply, second
reply). Far replies resolve through alignment classes (a far stone
sharing a row or column with the corner box) and then a default, in
that order, mirroring the generating pipeline exactly.
-/

namespace SquareAchievement

inductive Key where
  | cell (c : Cell)
  | row (r : ℕ)
  | col (c : ℕ)
  | farm (t : Cell)
  | dflt
deriving DecidableEq, BEq, Repr

/-- A table entry: a forcing plan (play the first cell not already
P1's), or a quiet move that forks on the reply to it. -/
inductive Entry where
  | plan (cells : List Cell)
  | quiet (move : Cell) (branches : List (Key × Entry))
deriving Repr

structure Table where
  opening : Cell
  box : ℕ
  x2 : List (Key × Cell)
  scripts : List (Key × List (Key × Entry))

/-- The alignment class of a cell relative to the `box`-sized corner. -/
def classOf (box : ℕ) (c : Cell) : Key :=
  if c.1 < box && box ≤ c.2 then .row c.1
  else if c.2 < box && box ≤ c.1 then .col c.2
  else .dflt

/-- Exact key first, then alignment class, then the default. -/
def lookup {α : Type _} (box : ℕ) (entries : List (Key × α)) (c : Cell) : Option α :=
  match entries.lookup (.cell c) with
  | some v => some v
  | none =>
    match entries.lookup (classOf box c) with
    | some v => some v
    | none => entries.lookup .dflt

/-- One orientation of the farm test: an aligned member `p` pins the
box cell the pair can farm through. Mirrors the generating pipeline's
farm_relation case for case, with truncated subtraction guarded. -/
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

/-- The hot box cell a far reply pair can farm through, if any. -/
def farmKey (box : ℕ) (o1 o2 : Cell) : Option Key :=
  if max o1.1 o1.2 < 2 * box || max o2.1 o2.2 < 2 * box then none
  else
    match farmCase box o1 o2 with
    | some k => some k
    | none => farmCase box o2 o1

/-- The second-reply lookup. An exact second-reply entry is only
pair-safe when the first reply is exact too: shifting an abstract
first reply moves the pair's farm cell away from the one the exact
entry was generated against, so for an inexact first reply the farm
key outranks the exact key. -/
def lookupO2 {α : Type _} (box : ℕ) (entries : List (Key × α))
    (o1Exact : Bool) (o1 o2 : Cell) : Option α :=
  let farmHit := (farmKey box o1 o2).bind (fun k => entries.lookup k)
  match if o1Exact then none else farmHit with
  | some v => some v
  | none =>
    match entries.lookup (.cell o2) with
    | some v => some v
    | none =>
      match farmHit with
      | some v => some v
      | none =>
        match entries.lookup (classOf box o2) with
        | some v => some v
        | none => entries.lookup .dflt

end SquareAchievement
