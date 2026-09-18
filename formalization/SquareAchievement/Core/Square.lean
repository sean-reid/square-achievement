import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# Cells, boards, and axis-aligned squares

Cells live in the infinite quarter-plane `ℕ × ℕ`; the `n × n` board is a
finset of it. Working in the quarter-plane makes cross-board statements
(a square on a small board is a square on every larger board) direct.

A winning square is the four-corner set of an axis-aligned square with
side length at least 1, so the smallest winner is a 2x2 block of cells.
-/

namespace SquareAchievement

abbrev Cell := ℕ × ℕ

/-- The `n × n` board in the quarter-plane. -/
def board (n : ℕ) : Finset Cell := Finset.range n ×ˢ Finset.range n

theorem mem_board {n : ℕ} {x : Cell} : x ∈ board n ↔ x.1 < n ∧ x.2 < n := by
  simp [board]

/-- The four corners of the axis-aligned square anchored at `(r, c)`
with side length `s`. -/
def corners (r c s : ℕ) : Finset Cell :=
  {(r, c), (r, c + s), (r + s, c), (r + s, c + s)}

theorem mem_corners {r c s : ℕ} {x : Cell} :
    x ∈ corners r c s ↔
      x = (r, c) ∨ x = (r, c + s) ∨ x = (r + s, c) ∨ x = (r + s, c + s) := by
  simp [corners]

/-- `stones` contains all four corners of some winning square. -/
def HasSquare (stones : Finset Cell) : Prop :=
  ∃ r c s, 0 < s ∧ corners r c s ⊆ stones

theorem HasSquare.mono {A B : Finset Cell} (h : HasSquare A) (hAB : A ⊆ B) :
    HasSquare B := by
  obtain ⟨r, c, s, hs, hsub⟩ := h
  exact ⟨r, c, s, hs, hsub.trans hAB⟩

theorem not_hasSquare_empty : ¬ HasSquare (∅ : Finset Cell) := by
  rintro ⟨r, c, s, -, hsub⟩
  exact absurd (hsub (by simp [mem_corners])) (Finset.notMem_empty (r, c))

/-- Fewer than four stones hold no square. -/
theorem not_hasSquare_of_card_lt {S : Finset Cell} (h : S.card < 4) :
    ¬ HasSquare S := by
  rintro ⟨a, b, s, hs, hsub⟩
  have h1 : ((a, b) : Cell) ≠ (a, b + s) := by
    simp [Prod.ext_iff]; omega
  have h2 : ((a, b) : Cell) ≠ (a + s, b) := by
    simp [Prod.ext_iff]; omega
  have h3 : ((a, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have h4 : ((a, b + s) : Cell) ≠ (a + s, b) := by
    simp [Prod.ext_iff]; omega
  have h5 : ((a, b + s) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have h6 : ((a + s, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have hcard : (corners a b s).card = 4 := by
    rw [corners]
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]),
      Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

end SquareAchievement
