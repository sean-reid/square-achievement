import SquareAchievement.General.Simulation

/-!
# Shared facts for the uniform wrappers

Small lemmas every wrapper of the simulation theorem needs, whatever
the strategy: what a fired farm key says, that small positions are
square-free and leave empty cells, and the finset shapes of the first
two stones of each side.
-/

namespace SquareAchievement

/-- A fired farm key names a farm cell. -/
theorem farmKey_farm {box : ℕ} {o1 o2 : Cell} {k : Key}
    (h : farmKey box o1 o2 = some k) : ∃ hc, k = Key.farm hc := by
  unfold farmKey at h
  split at h
  · exact absurd h (by simp)
  · have hcase : ∀ p q : Cell, ∀ k' : Key,
        farmCase box p q = some k' → ∃ hc, k' = Key.farm hc := by
      intro p q k' hc
      unfold farmCase at hc
      split at hc
      · exact ⟨_, (Option.some_inj.mp hc).symm⟩
      · split at hc
        · exact ⟨_, (Option.some_inj.mp hc).symm⟩
        · split at hc
          · exact ⟨_, (Option.some_inj.mp hc).symm⟩
          · exact absurd hc (by simp)
    split at h
    · rename_i k' hk'
      obtain ⟨hc, rfl⟩ := hcase _ _ _ hk'
      exact ⟨hc, (Option.some_inj.mp h).symm⟩
    · exact hcase _ _ _ h

/-- A farm cell lies in the box. -/
theorem farmKey_hot_box {box : ℕ} {o1 o2 hc : Cell}
    (h : farmKey box o1 o2 = some (.farm hc)) :
    hc.1 < box ∧ hc.2 < box := by
  obtain ⟨-, -, hcase⟩ := farmKey_spec h
  rcases hcase with hcase | hcase <;>
    rcases farmCase_spec hcase with
      ⟨c1, c2, c3, c4, c5, e1, e2⟩ | ⟨c1, c2, c3, c4, c5, e1, e2⟩ |
      ⟨c1, c2, c3, c4, e1, e2⟩ <;>
    omega

/-- Positions with at most three stones always have an empty cell. -/
theorem empties_nonempty {n : ℕ} (hn : 17 ≤ n) {p1 p2 : Finset Cell}
    (h : (p1 ∪ p2).card ≤ 3) : (empties n p1 p2).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hmem : ∀ w : Cell, w ∈ board n → w ∈ p1 ∪ p2 := by
    intro w hw
    by_contra hwn
    rw [Finset.mem_union, not_or] at hwn
    have : w ∈ empties n p1 p2 := mem_empties.mpr ⟨hw, hwn.1, hwn.2⟩
    rw [hne] at this
    exact absurd this (Finset.notMem_empty w)
  have hsub : ({(0, 0), (0, 1), (1, 0), (1, 1)} : Finset Cell) ⊆
      p1 ∪ p2 := by
    intro w hw
    apply hmem
    rw [mem_board]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> constructor <;> omega
  have : ({(0, 0), (0, 1), (1, 0), (1, 1)} : Finset Cell).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

/-- Two stones hold no square. -/
theorem not_hasSquare_pair {a b : Cell} :
    ¬ HasSquare (([a, b] : List Cell).toFinset) :=
  not_hasSquare_of_card_lt (lt_of_le_of_lt (List.toFinset_card_le _) (by simp))

/-- Three stones or fewer, as a union of the two sides. -/
theorem card_union_three (a b c : Cell) :
    ((insert a (insert b ∅) : Finset Cell) ∪ insert c ∅).card ≤ 3 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := Finset.card_insert_le a (insert b (∅ : Finset Cell))
  have h2 := Finset.card_insert_le b (∅ : Finset Cell)
  have h3 := Finset.card_insert_le c (∅ : Finset Cell)
  rw [Finset.card_empty] at h2 h3
  omega

end SquareAchievement
