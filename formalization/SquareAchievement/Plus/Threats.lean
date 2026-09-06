import SquareAchievement.General.Simulation
import SquareAchievement.Plus.Rule

/-!
# The pair-based threat scan is the square scan

`threatsIn` finds threats through pairs of stones; the checker's
`threatsL` scans every square of the board. With the stones inside the
board they agree, so the rule's reflexes see exactly the completions
the checker sees. This is what lets the strong soundness theorem
attribute the checker's two-move wins to the rule itself.
-/

namespace SquareAchievement.Plus

open SquareAchievement

/-- Every list `squaresThrough` emits is a square of the board. -/
theorem squaresThrough_sub {k : ℕ} {a b : Cell} (ha : a ∈ board k) (hb : b ∈ board k)
    {sq : List Cell} (h : sq ∈ squaresThrough k a b) : sq ∈ squaresList k := by
  rw [mem_board] at ha hb
  rw [mem_squaresList]
  unfold squaresThrough at h
  split_ifs at h with h1 h2 h3
  · simp at h
  · have hne : a.2 ≠ b.2 := fun h' => h1 (Prod.ext h2 h')
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at h
    rcases h with ⟨hlt, rfl⟩ | ⟨hle, rfl⟩
    · exact ⟨a.1, min a.2 b.2, max a.2 b.2 - min a.2 b.2, by omega, by omega, by omega, rfl⟩
    · refine ⟨a.1 - (max a.2 b.2 - min a.2 b.2), min a.2 b.2, max a.2 b.2 - min a.2 b.2,
        by omega, by omega, by omega, ?_⟩
      simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
      omega
  · have hne : a.1 ≠ b.1 := fun h' => h1 (Prod.ext h' h3)
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at h
    rcases h with ⟨hlt, rfl⟩ | ⟨hle, rfl⟩
    · exact ⟨min a.1 b.1, a.2, max a.1 b.1 - min a.1 b.1, by omega, by omega, by omega, rfl⟩
    · refine ⟨min a.1 b.1, a.2 - (max a.1 b.1 - min a.1 b.1), max a.1 b.1 - min a.1 b.1,
        by omega, by omega, by omega, ?_⟩
      simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
      omega
  · rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hd, rfl⟩ := h
    exact ⟨min a.1 b.1, min a.2 b.2, max a.1 b.1 - min a.1 b.1,
      by omega, by omega, by omega, rfl⟩

/-- Every square through two distinct corners is emitted for that pair. -/
theorem mem_squaresThrough {k r c s : ℕ} (hs : 0 < s) (hr : r + s < k) (hc : c + s < k)
    {a b : Cell} (ha : a ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)])
    (hb : b ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)]) (hab : cellLt a b = true) :
    [(r, c), (r, c + s), (r + s, c), (r + s, c + s)] ∈ squaresThrough k a b := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  simp only [cellLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hab
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [squaresThrough, Prod.mk.injEq] <;>
    split_ifs <;>
    simp only [List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false, false_or, List.cons.injEq, Prod.mk.injEq, and_true, true_and] <;>
    omega

/-- Membership survives the fold that removes duplicates. -/
theorem mem_dedup_foldl (l : List Cell) :
    ∀ (acc : List Cell) (z : Cell),
      z ∈ l.foldl (fun acc m => if acc.contains m then acc else m :: acc) acc ↔
        z ∈ l ∨ z ∈ acc := by
  induction l with
  | nil => intro acc z; simp
  | cons m rest ih =>
    intro acc z
    rw [List.foldl_cons, ih]
    by_cases hm : acc.contains m = true
    · simp only [hm, if_true, List.mem_cons]
      have : m ∈ acc := List.contains_iff_mem.mp hm
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((rfl | h) | h)
        · exact Or.inr this
        · exact Or.inl h
        · exact Or.inr h
    · simp only [hm, Bool.false_eq_true, if_false, List.mem_cons]
      tauto

/-- The pair scan and the square scan agree. -/
theorem mem_threatsIn_iff {k : ℕ} {mine occ : List Cell} (hmine : ∀ x ∈ mine, x ∈ board k)
    {z : Cell} : z ∈ threatsIn k mine occ ↔ z ∈ threatsL (squaresList k) mine occ := by
  unfold threatsIn
  rw [List.mem_mergeSort, mem_dedup_foldl]
  simp only [List.not_mem_nil, or_false, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, b, hb, hz⟩
    split_ifs at hz with hab
    · rw [List.mem_filterMap] at hz
      obtain ⟨sq, hsq, hm⟩ := hz
      have hsqL := squaresThrough_sub (hmine a ha) (hmine b hb) hsq
      split at hm
      · rename_i m heq
        split at hm
        · simp at hm
        · rename_i hocc
          obtain rfl := Option.some_inj.mp hm
          exact threatsL_of_filter hsqL heq (by revert hocc; cases occ.contains m <;> simp)
      · simp at hm
    · simp at hz
  · intro h
    obtain ⟨sq, hsq, hfil, hocc⟩ := mem_threatsL h
    obtain ⟨r, c, s, hs, hr, hc, rfl⟩ := mem_squaresList.mp hsq
    -- three corners lie in `mine`; two of them, in order, generate the square
    have hnd := squaresList_nodup hsq
    have hcorner : ∀ x ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)],
        x ≠ z → x ∈ mine := by
      intro x hx hxz
      by_contra hxm
      have : x ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)].filter
          (fun y => !mine.contains y) :=
        List.mem_filter.mpr ⟨hx, by simpa using hxm⟩
      rw [hfil, List.mem_singleton] at this
      exact hxz this
    have hzsq : z ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)] :=
      List.mem_of_mem_filter (hfil ▸ List.mem_cons_self ..)
    -- pick the two smallest corners other than z
    obtain ⟨a, b, ha, hb, hab, haz, hbz⟩ : ∃ a b : Cell,
        a ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)] ∧
        b ∈ [(r, c), (r, c + s), (r + s, c), (r + s, c + s)] ∧
        cellLt a b = true ∧ a ≠ z ∧ b ≠ z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzsq
      rcases hzsq with rfl | rfl | rfl | rfl
      · exact ⟨(r, c + s), (r + s, c), by simp, by simp,
          by simp [cellLt]; omega, by simp [Prod.ext_iff]; omega, by simp [Prod.ext_iff]; omega⟩
      · exact ⟨(r, c), (r + s, c), by simp, by simp,
          by simp [cellLt]; omega, by simp [Prod.ext_iff]; omega, by simp [Prod.ext_iff]; omega⟩
      · exact ⟨(r, c), (r, c + s), by simp, by simp,
          by simp [cellLt]; omega, by simp [Prod.ext_iff]; omega, by simp [Prod.ext_iff]; omega⟩
      · exact ⟨(r, c), (r, c + s), by simp, by simp,
          by simp [cellLt]; omega, by simp [Prod.ext_iff]; omega, by simp [Prod.ext_iff]; omega⟩
    refine ⟨a, hcorner a ha haz, b, hcorner b hb hbz, ?_⟩
    rw [if_pos hab, List.mem_filterMap]
    refine ⟨_, mem_squaresThrough hs hr hc ha hb hab, ?_⟩
    rw [hfil]
    simp only [hocc, Bool.false_eq_true, if_false]

/-- The rule takes its wins: with its stones in the corner and the
opponent's near stones the only ones that can occupy a corner cell, its
first reflex plays a completion whenever the board offers one. -/
theorem plusMove_takesWins {n : ℕ} (hn : 6 ≤ n) : TakesWinsOn plusMove box n [] := by
  intro tail hlen hp1box hboard hne
  simp only [List.nil_append] at hp1box hboard hne ⊢
  set a := abstractOf tail with ha
  have hp1 : a.p1 = stonesOf true tail := rfl
  have hp1box' : ∀ x ∈ stonesOf true tail, x ∈ board 6 :=
    fun x hx => inBox_iff.mp (hp1box x hx)
  -- occupancy on the box: the rule's near list against the whole history
  have hocc : ∀ x ∈ board 6, (x ∈ a.p1 ++ a.p2 ↔ x ∈ tail) := by
    intro x hx6
    rw [List.mem_append, mem_stonesOf tail true]
    simp only [Bool.not_true]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_filter h)
    · rintro (h | h)
      · exact Or.inl h
      · right
        refine List.mem_filter.mpr ⟨h, ?_⟩
        rw [mem_board] at hx6
        simp only [onBoard, base, Bool.and_eq_true]
        exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩
  have hcross := fun z =>
    mem_threatsL_iff_cross (B := 6) (n := n) (le_refl 6) hn hp1box' hocc (z := z)
  have hne6 : threatsL (squaresList 6) (stonesOf true tail) (a.p1 ++ a.p2) ≠ [] := by
    intro hnil
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
    have := (hcross z).mpr hz
    rw [hnil] at this
    simp at this
  have hmy : myThreats a.p1 (a.p1 ++ a.p2) ≠ [] := by
    intro hnil
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne6
    have : z ∈ myThreats a.p1 (a.p1 ++ a.p2) := (mem_threatsIn_iff (k := 6) hp1box').mpr hz
    rw [hnil] at this
    simp at this
  obtain ⟨z, rest, hzr⟩ := List.exists_cons_of_ne_nil hmy
  refine ⟨z, ?_, ?_⟩
  · simp only [plusMove, ← ha, hzr]
  · have hz : z ∈ myThreats a.p1 (a.p1 ++ a.p2) := by rw [hzr]; exact List.mem_cons_self ..
    exact (hcross z).mp ((mem_threatsIn_iff (k := 6) hp1box').mp hz)

end SquareAchievement.Plus
