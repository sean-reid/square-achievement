import SquareAchievement.Compute.CheckerSound

/-!
# Invariance and saturation geometry

Support for the subsumption argument. The executable primitives read a
position only through membership on the cells of listed squares, so a
stone lying on no listed square is invisible to them: that is what
makes a far reply inert. And a square with two distinct corners inside
`board B` lies entirely inside `board (2 * B)`, which is why a finite
saturation bound exists: beyond it, no new square can involve two cells
of the active region.
-/

namespace SquareAchievement

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-! ## Square lists across board sizes -/

theorem squaresList_mono {m n : ℕ} (h : m ≤ n) {sq : List Cell}
    (hsq : sq ∈ squaresList m) : sq ∈ squaresList n := by
  obtain ⟨r, c, s, hs, hr, hc, rfl⟩ := mem_squaresList.mp hsq
  exact mem_squaresList.mpr ⟨r, c, s, hs, by omega, by omega, rfl⟩

/-! ## Saturation geometry -/

/-- Two distinct corners inside `board B` confine the whole square to
`board (2 * B)`. -/
theorem corners_span_bounded {r c s B : ℕ} {x y : Cell}
    (hx : x ∈ corners r c s) (hy : y ∈ corners r c s) (hxy : x ≠ y)
    (hxB : x ∈ board B) (hyB : y ∈ board B) :
    r + s < 2 * B ∧ c + s < 2 * B := by
  rw [mem_corners] at hx hy
  rw [mem_board] at hxB hyB
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    simp_all <;> omega

/-! ## Congruence: the primitives see only listed-square cells -/

theorem hasSquareL_congr {squares : List (List Cell)} {L L' : List Cell}
    (h : ∀ sq ∈ squares, ∀ x ∈ sq, (x ∈ L ↔ x ∈ L')) :
    hasSquareL squares L = hasSquareL squares L' := by
  apply bool_eq_of_iff
  simp only [hasSquareL, List.any_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨sq, hsq, hall⟩
    exact ⟨sq, hsq, fun x hx => (h sq hsq x hx).mp (hall x hx)⟩
  · rintro ⟨sq, hsq, hall⟩
    exact ⟨sq, hsq, fun x hx => (h sq hsq x hx).mpr (hall x hx)⟩

theorem completesL_congr {squares : List (List Cell)} {L L' : List Cell}
    {m : Cell} (h : ∀ sq ∈ squares, ∀ x ∈ sq, (x ∈ L ↔ x ∈ L')) :
    completesL squares L m = completesL squares L' m := by
  apply bool_eq_of_iff
  simp only [completesL, List.any_eq_true, List.all_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq]
  constructor
  · rintro ⟨sq, hsq, hm, hall⟩
    refine ⟨sq, hsq, hm, fun x hx => ?_⟩
    rcases hall x hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr ((h sq hsq x hx).mp h')
  · rintro ⟨sq, hsq, hm, hall⟩
    refine ⟨sq, hsq, hm, fun x hx => ?_⟩
    rcases hall x hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr ((h sq hsq x hx).mpr h')

private def threatStep (occ : List Cell) (missing : List Cell)
    (best : Option Cell) : Option Cell :=
  match missing with
  | [m] =>
    if occ.contains m then best
    else
      match best with
      | none => some m
      | some b => if cellLt m b then some m else some b
  | _ => best

private theorem minThreat_eq_foldl (squares : List (List Cell))
    (mine occ : List Cell) (init : Option Cell) :
    squares.foldl
      (fun best sq =>
        match sq.filter (fun x => !mine.contains x) with
        | [m] =>
          if occ.contains m then best
          else
            match best with
            | none => some m
            | some b => if cellLt m b then some m else some b
        | _ => best) init =
    squares.foldl
      (fun best sq => threatStep occ (sq.filter (fun x => !mine.contains x)) best)
      init := by
  induction squares generalizing init with
  | nil => rfl
  | cons sq rest ih => simp only [List.foldl_cons, threatStep, ih]

theorem minThreat_congr {squares : List (List Cell)}
    {mine mine' occ occ' : List Cell}
    (hm : ∀ sq ∈ squares, ∀ x ∈ sq, (x ∈ mine ↔ x ∈ mine'))
    (ho : ∀ sq ∈ squares, ∀ x ∈ sq, (x ∈ occ ↔ x ∈ occ')) :
    minThreat squares mine occ = minThreat squares mine' occ' := by
  suffices hgen : ∀ (sqs : List (List Cell)) (init : Option Cell),
      (∀ sq ∈ sqs, ∀ x ∈ sq, (x ∈ mine ↔ x ∈ mine')) →
      (∀ sq ∈ sqs, ∀ x ∈ sq, (x ∈ occ ↔ x ∈ occ')) →
      sqs.foldl
        (fun best sq => threatStep occ (sq.filter (fun x => !mine.contains x)) best)
        init =
      sqs.foldl
        (fun best sq => threatStep occ' (sq.filter (fun x => !mine'.contains x)) best)
        init by
    simp only [minThreat]
    exact hgen squares none hm ho
  intro sqs
  induction sqs with
  | nil => intro init _ _; rfl
  | cons sq rest ih =>
    intro init hm' ho'
    have hmsq := hm' sq (List.mem_cons_self ..)
    have hosq := ho' sq (List.mem_cons_self ..)
    have hfilter :
        sq.filter (fun x => !mine.contains x) =
        sq.filter (fun x => !mine'.contains x) := by
      apply List.filter_congr
      intro x hx
      apply congrArg Bool.not
      apply bool_eq_of_iff
      simp only [List.contains_iff_mem]
      exact hmsq x hx
    have hinit : threatStep occ (sq.filter (fun x => !mine.contains x)) init =
        threatStep occ' (sq.filter (fun x => !mine'.contains x)) init := by
      rw [hfilter]
      rcases hcase : sq.filter (fun x => !mine'.contains x) with _ | ⟨m, _ | _⟩
      · rfl
      · have hmem : m ∈ sq :=
          List.mem_of_mem_filter (hcase ▸ List.mem_cons_self ..)
        have : occ.contains m = occ'.contains m := by
          apply bool_eq_of_iff
          simp only [List.contains_iff_mem]
          exact hosq m hmem
        simp only [threatStep, this]
      · rfl
    simp only [List.foldl_cons, hinit]
    exact ih _ (fun s hs => hm' s (List.mem_cons_of_mem _ hs))
      (fun s hs => ho' s (List.mem_cons_of_mem _ hs))

/-- A stone on no listed square is invisible to the square scan. -/
theorem hasSquareL_cons_far {squares : List (List Cell)} {L : List Cell}
    {r : Cell} (h : ∀ sq ∈ squares, r ∉ sq) :
    hasSquareL squares (r :: L) = hasSquareL squares L := by
  apply hasSquareL_congr
  intro sq hsq x hx
  simp only [List.mem_cons]
  constructor
  · rintro (rfl | hmem)
    · exact absurd hx (h sq hsq)
    · exact hmem
  · exact Or.inr

end SquareAchievement
