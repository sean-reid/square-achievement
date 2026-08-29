import SquareAchievement.Core.Position

/-!
# The game

Players alternate placing stones on empty board cells, P1 first; the
first player holding all four corners of a winning square wins, and a
full board with no winner is a draw.

`P1CanWin n p1 p2` says the player to move (P1) forces a win from the
given position. A draw counts as failure, so the `step` constructor
demands a nonempty reply set: quietly filling the last cell wins
nothing. The predicate is inductive rather than recursive so that
winning strategies are finite objects: a proof tree is exactly a
strategy tree, with one P1 move per node and all P2 replies covered.
-/

inductive P1CanWin (n : ℕ) : Finset Cell → Finset Cell → Prop
  /-- P1 completes a square right now. -/
  | now {p1 p2 : Finset Cell} (m : Cell) (hm : m ∈ empties n p1 p2)
      (hwin : HasSquare (insert m p1)) :
      P1CanWin n p1 p2
  /-- P1 plays `m`; every P2 reply fails to complete a P2 square and
  leaves a position P1 still wins. -/
  | step {p1 p2 : Finset Cell} (m : Cell) (hm : m ∈ empties n p1 p2)
      (hne : (empties n (insert m p1) p2).Nonempty)
      (hsafe : ∀ r ∈ empties n (insert m p1) p2, ¬ HasSquare (insert r p2))
      (hwins : ∀ r ∈ empties n (insert m p1) p2,
        P1CanWin n (insert m p1) (insert r p2)) :
      P1CanWin n p1 p2

/-- A winning position always has a move available. -/
theorem P1CanWin.nonempty_empties {n : ℕ} {p1 p2 : Finset Cell}
    (h : P1CanWin n p1 p2) : (empties n p1 p2).Nonempty := by
  induction h with
  | now m hm hwin => exact ⟨m, hm⟩
  | step m hm hne hsafe hwins ih => exact ⟨m, hm⟩

/-- No board, no win: the 0-board has no cells to move on. -/
theorem not_p1CanWin_zero : ¬ P1CanWin 0 ∅ ∅ := by
  intro h
  obtain ⟨m, hm⟩ := h.nonempty_empties
  have := (mem_empties.mp hm).1
  have := (mem_board.mp this).1
  omega
