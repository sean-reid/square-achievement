import SquareAchievement.Compute.ForcedSound

/-!
# Farm coverage of escaping squares

The heart of the uniform theorem's safety argument. A square that
does not fit inside the base board `17`, three of whose corners are a
box cell and the opponent's two reply stones, is always a farm
square: `farmKey` fires on the replies and names exactly the box
corner. Consequently a base-board run plus farm safety rules out
every opponent square on every board: squares inside the base are
checked by the run, and squares outside it need the box corner the
farm entry never surrenders.

The geometry: the box corner of an escaping square must be its
northwest corner (any other position forces the whole square inside
low coordinates, contradicting escape), the side is at least 12, and
whichever two of the remaining corners the replies occupy, one of
`farmCase`'s three orientations pins the northwest corner.
-/

namespace SquareAchievement

private theorem farmKey_open {box x y x' y' : ℕ}
    (hg1 : 2 * box ≤ max x y) (hg2 : 2 * box ≤ max x' y') :
    farmKey box (x, y) (x', y') =
      match farmCase box (x, y) (x', y') with
      | some k => some k
      | none => farmCase box (x', y') (x, y) := by
  unfold farmKey
  rw [if_neg]
  · rfl
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
    exact ⟨hg1, hg2⟩

private theorem farmCase_col' {box a b a' : ℕ} (h1 : a < box) (h3 : a < a')
    (h4 : a' - a ≤ b) (h5 : b - (a' - a) < box) :
    farmCase box (a, b) (a', b) = some (.farm (a, b - (a' - a))) := by
  unfold farmCase
  dsimp only
  rw [if_pos]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨h1, trivial⟩, h3⟩, h4⟩, h5⟩

private theorem farmCase_row' {box a b b' : ℕ} (h1 : b < box) (h3 : b < b')
    (h4 : b' - b ≤ a) (h5 : a - (b' - b) < box) :
    farmCase box (a, b) (a, b') = some (.farm (a - (b' - b), b)) := by
  unfold farmCase
  dsimp only
  rw [if_neg, if_pos]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨h1, trivial⟩, h3⟩, h4⟩, h5⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

private theorem farmCase_diag' {box a b a' b' : ℕ} (h1 : a < box)
    (h2 : b' < box) (h3 : 1 ≤ b - b') (h4 : b - b' = a' - a) (h5 : b' < b)
    (h6 : a < a') :
    farmCase box (a, b) (a', b') = some (.farm (a, b')) := by
  unfold farmCase
  dsimp only
  rw [if_neg, if_neg, if_pos]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

private theorem farmCase_none_far {box x y : ℕ} (q : Cell)
    (hx : box ≤ x) (hy : box ≤ y) :
    farmCase box (x, y) q = none := by
  unfold farmCase
  dsimp only
  rw [if_neg, if_neg, if_neg]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

private theorem farmCase_none_bent {box x y x' y' : ℕ}
    (hx : box ≤ x) (hxx : x ≠ x') :
    farmCase box (x, y) (x', y') = none := by
  unfold farmCase
  dsimp only
  rw [if_neg, if_neg, if_neg]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

/-- An escaping square whose corners hold a box cell and the two
reply stones is a farm square keyed by the box cell. -/
theorem escape_farm {r c s : ℕ} {blk o1 o2 : Cell}
    (hs : 0 < s) (hesc : 17 ≤ r + s ∨ 17 ≤ c + s)
    (hblk : blk ∈ corners r c s) (ho1 : o1 ∈ corners r c s)
    (ho2 : o2 ∈ corners r c s)
    (hb1 : blk ≠ o1) (hb2 : blk ≠ o2) (h12 : o1 ≠ o2)
    (hbox : blk ∈ board 6) :
    farmKey 6 o1 o2 = some (.farm blk) := by
  rw [mem_corners] at hblk ho1 ho2
  rw [mem_board] at hbox
  -- the box corner is the northwest corner, and the side is at least 12
  have hblkA : blk = (r, c) := by
    rcases hblk with rfl | rfl | rfl | rfl
    · rfl
    all_goals (exfalso; dsimp only at hbox; omega)
  subst hblkA
  dsimp only at hbox
  have hr : r < 6 := hbox.1
  have hc : c < 6 := hbox.2
  have hs12 : 12 ≤ s := by omega
  rcases ho1 with rfl | rfl | rfl | rfl <;> rcases ho2 with rfl | rfl | rfl | rfl
  · exact absurd rfl hb1
  · exact absurd rfl hb1
  · exact absurd rfl hb1
  · exact absurd rfl hb1
  · exact absurd rfl hb2
  · exact absurd rfl h12
  · -- (o1, o2) = ((r, c+s), (r+s, c)): diagonal orientation
    rw [farmKey_open (by omega) (by omega),
      farmCase_diag' hr hc (by omega) (by omega) (by omega) (by omega)]
  · -- ((r, c+s), (r+s, c+s)): same-column orientation
    rw [farmKey_open (by omega) (by omega),
      farmCase_col' hr (by omega) (by omega) (by omega),
      show c + s - (r + s - r) = c by omega]
  · exact absurd rfl hb2
  · -- ((r+s, c), (r, c+s)): swapped diagonal
    rw [farmKey_open (by omega) (by omega),
      farmCase_none_bent (by omega) (by omega),
      farmCase_diag' hr hc (by omega) (by omega) (by omega) (by omega)]
  · exact absurd rfl h12
  · -- ((r+s, c), (r+s, c+s)): same-row orientation
    rw [farmKey_open (by omega) (by omega),
      farmCase_row' hc (by omega) (by omega) (by omega),
      show r + s - (c + s - c) = r by omega]
  · exact absurd rfl hb2
  · -- ((r+s, c+s), (r, c+s)): swapped same-column
    rw [farmKey_open (by omega) (by omega),
      farmCase_none_far _ (by omega) (by omega),
      farmCase_col' hr (by omega) (by omega) (by omega),
      show c + s - (r + s - r) = c by omega]
  · -- ((r+s, c+s), (r+s, c)): swapped same-row
    rw [farmKey_open (by omega) (by omega),
      farmCase_none_far _ (by omega) (by omega),
      farmCase_row' hc (by omega) (by omega) (by omega),
      show r + s - (c + s - c) = r by omega]
  · exact absurd rfl h12

end SquareAchievement
