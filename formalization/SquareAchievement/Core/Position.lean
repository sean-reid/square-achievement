import SquareAchievement.Core.Square

/-!
# Positions

A position is the pair of stone sets. Legality (on the board, disjoint)
is a separate predicate rather than a structure invariant so that
partial positions and hypothetical placements stay easy to manipulate.
`empties` drives every termination argument: it strictly shrinks with
each stone placed.
-/

/-- Cells of the `n × n` board not held by either player. -/
def empties (n : ℕ) (p1 p2 : Finset Cell) : Finset Cell :=
  board n \ (p1 ∪ p2)

theorem mem_empties {n : ℕ} {p1 p2 : Finset Cell} {x : Cell} :
    x ∈ empties n p1 p2 ↔ x ∈ board n ∧ x ∉ p1 ∧ x ∉ p2 := by
  simp [empties, and_assoc]

theorem empties_insert_left_ssubset {n : ℕ} {p1 p2 : Finset Cell} {m : Cell}
    (hm : m ∈ empties n p1 p2) :
    empties n (insert m p1) p2 ⊂ empties n p1 p2 := by
  constructor
  · intro x hx
    rw [mem_empties] at hx ⊢
    exact ⟨hx.1, fun h => hx.2.1 (Finset.mem_insert_of_mem h), hx.2.2⟩
  · intro hsub
    have := hsub hm
    rw [mem_empties] at this
    exact this.2.1 (Finset.mem_insert_self m p1)

theorem empties_insert_right_ssubset {n : ℕ} {p1 p2 : Finset Cell} {m : Cell}
    (hm : m ∈ empties n p1 p2) :
    empties n p1 (insert m p2) ⊂ empties n p1 p2 := by
  constructor
  · intro x hx
    rw [mem_empties] at hx ⊢
    exact ⟨hx.1, hx.2.1, fun h => hx.2.2 (Finset.mem_insert_of_mem h)⟩
  · intro hsub
    have := hsub hm
    rw [mem_empties] at this
    exact this.2.2 (Finset.mem_insert_self m p2)

theorem card_empties_insert_left_lt {n : ℕ} {p1 p2 : Finset Cell} {m : Cell}
    (hm : m ∈ empties n p1 p2) :
    (empties n (insert m p1) p2).card < (empties n p1 p2).card :=
  Finset.card_lt_card (empties_insert_left_ssubset hm)

theorem card_empties_insert_right_lt {n : ℕ} {p1 p2 : Finset Cell} {m : Cell}
    (hm : m ∈ empties n p1 p2) :
    (empties n p1 (insert m p2)).card < (empties n p1 p2).card :=
  Finset.card_lt_card (empties_insert_right_ssubset hm)
