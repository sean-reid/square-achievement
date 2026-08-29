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

end SquareAchievement
