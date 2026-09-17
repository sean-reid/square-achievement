import SquareAchievement.Compute.ForcedSound
import SquareAchievement.General.FarmKey

/-!
# Escaping squares and the hidden corner

A square that does not fit inside `board 17`, three of whose corners
are a box cell and the second player's two reply stones, has that box
cell as the pair's hidden corner: `farmKey` fires on the replies and
returns exactly it (`escape_farm`). So a base-board run plus the
anchored runs rule out every second-player square on every board:
squares inside the base are checked by the run, and squares outside
it need the hidden corner, which the anchored run's guard keeps from
the second player.

The geometry: the box corner of an escaping square is its northwest
corner, the side is at least 12, and whichever two of the remaining
corners the replies occupy, one of `farmCase`'s three orientations
returns the northwest corner.
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

/-- What a fired `farmCase` certifies, orientation by orientation. -/
theorem farmCase_spec {box : ℕ} {p q h : Cell}
    (hc : farmCase box p q = some (.farm h)) :
    (p.1 < box ∧ p.2 = q.2 ∧ p.1 < q.1 ∧ q.1 - p.1 ≤ p.2 ∧
      p.2 - (q.1 - p.1) < box ∧ h.1 = p.1 ∧ h.2 = p.2 - (q.1 - p.1)) ∨
    (p.2 < box ∧ p.1 = q.1 ∧ p.2 < q.2 ∧ q.2 - p.2 ≤ p.1 ∧
      p.1 - (q.2 - p.2) < box ∧ h.1 = p.1 - (q.2 - p.2) ∧ h.2 = p.2) ∨
    (p.1 < box ∧ q.2 < box ∧ 1 ≤ p.2 - q.2 ∧ p.2 - q.2 = q.1 - p.1 ∧
      h.1 = p.1 ∧ h.2 = q.2) := by
  unfold farmCase at hc
  split at hc
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
    have hh := Key.farm.inj (Option.some_inj.mp hc)
    exact Or.inl ⟨h1, h2, h3, h4, h5, by rw [← hh], by rw [← hh]⟩
  · rename_i hn1
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
      have hh := Key.farm.inj (Option.some_inj.mp hc)
      exact Or.inr (Or.inl ⟨h1, h2, h3, h4, h5, by rw [← hh], by rw [← hh]⟩)
    · rename_i hn2
      split at hc
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcond
        have hh := Key.farm.inj (Option.some_inj.mp hc)
        exact Or.inr (Or.inr ⟨h1, h2, h3, h4, by rw [← hh], by rw [← hh]⟩)
      · exact absurd hc (by simp)

/-- What a fired `farmKey` certifies: the far gate and one fired
orientation. -/
theorem farmKey_spec {box : ℕ} {o1 o2 h : Cell}
    (hk : farmKey box o1 o2 = some (.farm h)) :
    2 * box ≤ max o1.1 o1.2 ∧ 2 * box ≤ max o2.1 o2.2 ∧
      (farmCase box o1 o2 = some (.farm h) ∨
        farmCase box o2 o1 = some (.farm h)) := by
  unfold farmKey at hk
  split at hk
  · exact absurd hk (by simp)
  · rename_i hgate
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
      at hgate
    refine ⟨hgate.1, hgate.2, ?_⟩
    split at hk
    · rename_i k hcase
      rw [Option.some_inj.mp hk] at hcase
      exact Or.inl hcase
    · exact Or.inr hk

private theorem mem_corners_of {r c s : ℕ} {x : Cell}
    (h : (x.1 = r ∧ x.2 = c) ∨ (x.1 = r ∧ x.2 = c + s) ∨ (x.1 = r + s ∧ x.2 = c) ∨
      (x.1 = r + s ∧ x.2 = c + s)) : x ∈ corners r c s := by
  rw [mem_corners]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    [exact Or.inl (Prod.ext h1 h2); exact Or.inr (Or.inl (Prod.ext h1 h2));
     exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)));
     exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))]

/-- The hidden corner lies in the box and is a corner of a square whose
corners include both replies. -/
theorem farmKey_corners {box : ℕ} {o1 o2 h : Cell}
    (hk : farmKey box o1 o2 = some (.farm h)) :
    h ∈ board box ∧ ∃ r c s, 0 < s ∧ h ∈ corners r c s ∧
      o1 ∈ corners r c s ∧ o2 ∈ corners r c s := by
  obtain ⟨-, -, hcase | hcase⟩ := farmKey_spec hk <;>
    rcases farmCase_spec hcase with
      ⟨c1, c2, c3, c4, c5, e1, e2⟩ | ⟨c1, c2, c3, c4, c5, e1, e2⟩ |
      ⟨c1, c2, c3, c4, e1, e2⟩
  · exact ⟨by rw [mem_board]; omega, o1.1, o1.2 - (o2.1 - o1.1), o2.1 - o1.1, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      mem_corners_of (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))⟩
  · exact ⟨by rw [mem_board]; omega, o1.1 - (o2.2 - o1.2), o1.2, o2.2 - o1.2, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))),
      mem_corners_of (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))⟩
  · exact ⟨by rw [mem_board]; omega, o1.1, o2.2, o1.2 - o2.2, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      mem_corners_of (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))⟩
  · exact ⟨by rw [mem_board]; omega, o2.1, o2.2 - (o1.1 - o2.1), o1.1 - o2.1, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))),
      mem_corners_of (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
  · exact ⟨by rw [mem_board]; omega, o2.1 - (o1.2 - o2.2), o2.2, o1.2 - o2.2, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))),
      mem_corners_of (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))⟩
  · exact ⟨by rw [mem_board]; omega, o2.1, o1.2, o2.2 - o1.2, by omega,
      mem_corners_of (Or.inl ⟨by omega, by omega⟩),
      mem_corners_of (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))),
      mem_corners_of (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩

/-- The near member of a pair with a hidden corner, the other member
beyond the base board: it is box-aligned with one far coordinate, the
hidden corner shares its box-aligned coordinate, and the pair's square
escapes the base. -/
theorem farm_near_fst {o1 o2 h : Cell}
    (hk : farmKey 6 o1 o2 = some (.farm h))
    (h1b : o1 ∈ board 17) (h2b : o2 ∉ board 17) :
    (o1.1 < 6 ∧ 12 ≤ o1.2 ∧ o1.2 < 17 ∧ h.1 = o1.1 ∧ h.2 < 6 ∧
      h.2 ≤ o1.2 ∧ 17 ≤ o1.1 + o1.2 - h.2) ∨
    (o1.2 < 6 ∧ 12 ≤ o1.1 ∧ o1.1 < 17 ∧ h.2 = o1.2 ∧ h.1 < 6 ∧
      h.1 ≤ o1.1 ∧ 17 ≤ o1.2 + o1.1 - h.1) := by
  obtain ⟨hg1, hg2, hcase⟩ := farmKey_spec hk
  rw [mem_board] at h1b
  have h2b' : 17 ≤ o2.1 ∨ 17 ≤ o2.2 := by
    rw [mem_board] at h2b
    omega
  rcases hcase with hcase | hcase <;>
    rcases farmCase_spec hcase with
      ⟨c1, c2, c3, c4, c5, e1, e2⟩ | ⟨c1, c2, c3, c4, c5, e1, e2⟩ |
      ⟨c1, c2, c3, c4, e1, e2⟩ <;>
    omega

/-- The mirror statement for a near second reply. -/
theorem farm_near_snd {o1 o2 h : Cell}
    (hk : farmKey 6 o1 o2 = some (.farm h))
    (h1b : o1 ∉ board 17) (h2b : o2 ∈ board 17) :
    (o2.1 < 6 ∧ 12 ≤ o2.2 ∧ o2.2 < 17 ∧ h.1 = o2.1 ∧ h.2 < 6 ∧
      h.2 ≤ o2.2 ∧ 17 ≤ o2.1 + o2.2 - h.2) ∨
    (o2.2 < 6 ∧ 12 ≤ o2.1 ∧ o2.1 < 17 ∧ h.2 = o2.2 ∧ h.1 < 6 ∧
      h.1 ≤ o2.1 ∧ 17 ≤ o2.2 + o2.1 - h.1) := by
  obtain ⟨hg1, hg2, hcase⟩ := farmKey_spec hk
  rw [mem_board] at h2b
  have h1b' : 17 ≤ o1.1 ∨ 17 ≤ o1.2 := by
    rw [mem_board] at h1b
    omega
  rcases hcase with hcase | hcase <;>
    rcases farmCase_spec hcase with
      ⟨c1, c2, c3, c4, c5, e1, e2⟩ | ⟨c1, c2, c3, c4, c5, e1, e2⟩ |
      ⟨c1, c2, c3, c4, e1, e2⟩ <;>
    omega

set_option maxHeartbeats 6400000 in
-- the case split over the corner assignments exceeds the default budget
/-- In an escaping square whose corners come from a reply, the two
reply stones, and box cells, the box cell is unique and the reply
stones are both corners: two box corners would confine the square,
and a repeated cell cannot fill two corners. -/
theorem escape_pick {a b s : ℕ} (hs : 0 < s)
    (hesc : 17 ≤ a + s ∨ 17 ≤ b + s)
    {x o1r o2r : Cell} {D : List Cell}
    (hD : ∀ w ∈ D, w ∈ board 6)
    (hA : (a, b) = x ∨ (a, b) = o1r ∨ (a, b) = o2r ∨ (a, b) ∈ D)
    (hB : (a, b + s) = x ∨ (a, b + s) = o1r ∨ (a, b + s) = o2r ∨
      (a, b + s) ∈ D)
    (hC : (a + s, b) = x ∨ (a + s, b) = o1r ∨ (a + s, b) = o2r ∨
      (a + s, b) ∈ D)
    (hE : (a + s, b + s) = x ∨ (a + s, b + s) = o1r ∨
      (a + s, b + s) = o2r ∨ (a + s, b + s) ∈ D) :
    ∃ d ∈ D, d ∈ corners a b s ∧ o1r ∈ corners a b s ∧
      o2r ∈ corners a b s ∧ d ≠ o1r ∧ d ≠ o2r ∧ o1r ≠ o2r := by
  have hs12 : 12 ≤ s ∨ 17 ≤ a + s ∨ 17 ≤ b + s := by omega
  have dAB : ((a, b) : Cell) ≠ (a, b + s) := by simp [Prod.ext_iff]; omega
  have dAC : ((a, b) : Cell) ≠ (a + s, b) := by simp [Prod.ext_iff]; omega
  have dAE : ((a, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have dBC : ((a, b + s) : Cell) ≠ (a + s, b) := by
    simp [Prod.ext_iff]; omega
  have dBE : ((a, b + s) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have dCE : ((a + s, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have hb := fun {w : Cell} (h : w ∈ D) => mem_board.mp (hD _ h)
  rcases hA with hA | hA | hA | hA <;>
    rcases hB with hB | hB | hB | hB <;>
    rcases hC with hC | hC | hC | hC <;>
    rcases hE with hE | hE | hE | hE <;>
    first
    -- a repeated cell cannot fill two distinct corners
    | exact absurd (hA.trans hB.symm) dAB
    | exact absurd (hA.trans hC.symm) dAC
    | exact absurd (hA.trans hE.symm) dAE
    | exact absurd (hB.trans hC.symm) dBC
    | exact absurd (hB.trans hE.symm) dBE
    | exact absurd (hC.trans hE.symm) dCE
    -- two box corners confine the square below the escape
    | (exfalso;
       first
       | (obtain ⟨u1, v1⟩ := hb hA; obtain ⟨u2, v2⟩ := hb hB;
          dsimp only at u1 v1 u2 v2; omega)
       | (obtain ⟨u1, v1⟩ := hb hA; obtain ⟨u2, v2⟩ := hb hC;
          dsimp only at u1 v1 u2 v2; omega)
       | (obtain ⟨u1, v1⟩ := hb hA; obtain ⟨u2, v2⟩ := hb hE;
          dsimp only at u1 v1 u2 v2; omega)
       | (obtain ⟨u1, v1⟩ := hb hB; obtain ⟨u2, v2⟩ := hb hC;
          dsimp only at u1 v1 u2 v2; omega)
       | (obtain ⟨u1, v1⟩ := hb hB; obtain ⟨u2, v2⟩ := hb hE;
          dsimp only at u1 v1 u2 v2; omega)
       | (obtain ⟨u1, v1⟩ := hb hC; obtain ⟨u2, v2⟩ := hb hE;
          dsimp only at u1 v1 u2 v2; omega))
    -- a valid assignment: build the witness
    | (first
       | refine ⟨(a, b), hA, by rw [mem_corners]; tauto, ?_, ?_, ?_, ?_, ?_⟩
       | refine ⟨(a, b + s), hB, by rw [mem_corners]; tauto,
           ?_, ?_, ?_, ?_, ?_⟩
       | refine ⟨(a + s, b), hC, by rw [mem_corners]; tauto,
           ?_, ?_, ?_, ?_, ?_⟩
       | refine ⟨(a + s, b + s), hE, by rw [mem_corners]; tauto,
           ?_, ?_, ?_, ?_, ?_⟩) <;>
      first
      | (rw [← hA, mem_corners]; tauto)
      | (rw [← hB, mem_corners]; tauto)
      | (rw [← hC, mem_corners]; tauto)
      | (rw [← hE, mem_corners]; tauto)
      | (rw [← hA]; first | exact dAB.symm | exact dAC.symm | exact dAE.symm)
      | (rw [← hB]; first | exact dAB | exact dBC.symm | exact dBE.symm)
      | (rw [← hC]; first | exact dAC | exact dBC | exact dCE.symm)
      | (rw [← hE]; first | exact dAE | exact dBE | exact dCE)
      | (rw [← hA, ← hB]; first | exact dAB | exact dAB.symm)
      | (rw [← hA, ← hC]; first | exact dAC | exact dAC.symm)
      | (rw [← hA, ← hE]; first | exact dAE | exact dAE.symm)
      | (rw [← hB, ← hC]; first | exact dBC | exact dBC.symm)
      | (rw [← hB, ← hE]; first | exact dBE | exact dBE.symm)
      | (rw [← hC, ← hE]; first | exact dCE | exact dCE.symm)

/-- An escaping square whose corners hold a box cell and the two
reply stones has that box cell as the pair's hidden corner. -/
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
