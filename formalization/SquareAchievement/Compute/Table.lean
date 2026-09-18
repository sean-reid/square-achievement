import SquareAchievement.Core.Square

/-!
# Strategy tables

The data format of the `5 × 5` table: an opening move, a second move
per first reply, and per reply pair an entry, a forcing plan or a
quiet move that branches on the reply to it. A lookup matches the
exact cell first and falls back to the default.
-/

namespace SquareAchievement

/-- A table key: an exact cell or the default. `farm` is the key
`farmKey` returns for the hidden corner of a reply pair; no table
carries it. -/
inductive Key where
  | cell (c : Cell)
  | farm (h : Cell)
  | dflt
deriving DecidableEq, BEq, Repr

/-- A table entry: a forcing plan (play the first cell the first player
does not hold), or a quiet move that branches on the reply to it. -/
inductive Entry where
  | plan (cells : List Cell)
  | quiet (move : Cell) (branches : List (Key × Entry))
deriving Repr

/-- A table: the opening, the region its plans stay in, the second
move per first reply, and the entries per reply pair. -/
structure Table where
  opening : Cell
  box : ℕ
  x2 : List (Key × Cell)
  scripts : List (Key × List (Key × Entry))

/-- The exact key, then the default. -/
def lookup {α : Type _} (entries : List (Key × α)) (c : Cell) : Option α :=
  entries.lookup (.cell c) <|> entries.lookup .dflt

end SquareAchievement
