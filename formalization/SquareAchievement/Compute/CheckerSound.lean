import SquareAchievement.Compute.Checker
import SquareAchievement.Game.Rules

/-!
# Soundness of the checker

`check t n = true` yields a `P1CanWin` proof tree. The strategy itself
needs no correctness argument: the checker's guards validate every move
it emits and enumerate every reply, so any table passing the search is
a winning strategy. The induction carries three invariants: the history
has even length (P1 to move), every stone is on the board, and P2 holds
no square yet.
-/

namespace SquareAchievement

/-! ## Stones of a history -/

theorem mem_stonesOf {x : Cell} : ∀ (l : List Cell) (b : Bool),
    x ∈ l ↔ x ∈ stonesOf b l ∨ x ∈ stonesOf (!b) l := by
  intro l
  induction l with
  | nil => intro b; simp [stonesOf]
  | cons a rest ih =>
    intro b
    cases b with
    | true =>
      rw [show stonesOf true (a :: rest) = a :: stonesOf false rest from rfl,
        show stonesOf (!true) (a :: rest) = stonesOf true rest from rfl]
      simp only [List.mem_cons]
      rw [ih false]
      simp only [Bool.not_false]
      tauto
    | false =>
      rw [show stonesOf false (a :: rest) = stonesOf true rest from rfl,
        show stonesOf (!false) (a :: rest) = a :: stonesOf false rest from rfl]
      simp only [List.mem_cons]
      rw [ih true]
      simp only [Bool.not_true]
      tauto

theorem stonesOf_snoc (b : Bool) (l : List Cell) (x : Cell) :
    stonesOf b (l ++ [x]) =
      if (l.length % 2 = 0) = (b = true) then stonesOf b l ++ [x]
      else stonesOf b l := by
  induction l generalizing b with
  | nil => cases b <;> simp [stonesOf]
  | cons a rest ih =>
    have hpar : ((a :: rest).length % 2 = 0) ↔ ¬ (rest.length % 2 = 0) := by
      simp only [List.length_cons]
      omega
    cases b <;>
      simp only [List.cons_append, stonesOf, ih true, ih false] <;>
      by_cases hr : rest.length % 2 = 0 <;>
      simp [hr] <;>
      simp_all

theorem stonesOf_snoc_even_true {l : List Cell} {x : Cell}
    (h : l.length % 2 = 0) :
    stonesOf true (l ++ [x]) = stonesOf true l ++ [x] := by
  rw [stonesOf_snoc, if_pos]
  simp [h]

theorem stonesOf_snoc_even_false {l : List Cell} {x : Cell}
    (h : l.length % 2 = 0) :
    stonesOf false (l ++ [x]) = stonesOf false l := by
  rw [stonesOf_snoc, if_neg]
  simp [h]

theorem stonesOf_snoc_odd_true {l : List Cell} {x : Cell}
    (h : l.length % 2 = 1) :
    stonesOf true (l ++ [x]) = stonesOf true l := by
  rw [stonesOf_snoc, if_neg]
  simp [h]

theorem stonesOf_snoc_odd_false {l : List Cell} {x : Cell}
    (h : l.length % 2 = 1) :
    stonesOf false (l ++ [x]) = stonesOf false l ++ [x] := by
  rw [stonesOf_snoc, if_pos]
  simp [h]

/-! ## Squares: executable vs propositional -/

theorem mem_squaresList {n : ℕ} {sq : List Cell} :
    sq ∈ squaresList n ↔
      ∃ r c s, 0 < s ∧ r + s < n ∧ c + s < n ∧
        sq = [(r, c), (r, c + s), (r + s, c), (r + s, c + s)] := by
  simp only [squaresList, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨s, hs, r, hr, c, hc, hif⟩
    split at hif
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨r, c, s, hcond.1.1, hcond.1.2, hcond.2, (Option.some_inj.mp hif).symm⟩
    · exact absurd hif (by simp)
  · rintro ⟨r, c, s, hs, hr, hc, rfl⟩
    refine ⟨s, by omega, r, by omega, c, by omega, ?_⟩
    simp [hs, hr, hc]

theorem corners_toFinset (r c s : ℕ) :
    ([(r, c), (r, c + s), (r + s, c), (r + s, c + s)] : List Cell).toFinset =
      corners r c s := by
  simp [corners]

theorem hasSquareL_iff {n : ℕ} {L : List Cell} (hb : ∀ x ∈ L, x ∈ board n) :
    hasSquareL (squaresList n) L = true ↔ HasSquare L.toFinset := by
  simp only [hasSquareL, List.any_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨sq, hsq, hall⟩
    obtain ⟨r, c, s, hs, -, -, rfl⟩ := mem_squaresList.mp hsq
    refine ⟨r, c, s, hs, ?_⟩
    rw [← corners_toFinset]
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hall x hx
  · rintro ⟨r, c, s, hs, hsub⟩
    have hfar : (r + s, c + s) ∈ board n := by
      have : (r + s, c + s) ∈ corners r c s := by simp [mem_corners]
      have := hsub this
      rw [List.mem_toFinset] at this
      exact hb _ this
    rw [mem_board] at hfar
    refine ⟨[(r, c), (r, c + s), (r + s, c), (r + s, c + s)],
      mem_squaresList.mpr ⟨r, c, s, hs, hfar.1, hfar.2, rfl⟩, ?_⟩
    intro x hx
    have : x ∈ corners r c s := by
      rw [← corners_toFinset, List.mem_toFinset] at *
      exact hx
    have := hsub this
    rwa [List.mem_toFinset] at this

theorem hasSquareL_sound {n : ℕ} {L : List Cell}
    (h : hasSquareL (squaresList n) L = true) : HasSquare L.toFinset := by
  simp only [hasSquareL, List.any_eq_true, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨sq, hsq, hall⟩ := h
  obtain ⟨r, c, s, hs, -, -, rfl⟩ := mem_squaresList.mp hsq
  refine ⟨r, c, s, hs, ?_⟩
  rw [← corners_toFinset]
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact hall x hx

/-- The safety workhorse: a reply that completes nothing leaves P2
square-free. -/
theorem not_hasSquare_insert {n : ℕ} {p2 : List Cell} {r : Cell}
    (hrb : r ∈ board n) (hb : ∀ x ∈ p2, x ∈ board n)
    (hno : ¬ HasSquare p2.toFinset)
    (hc : completesL (squaresList n) p2 r = false) :
    ¬ HasSquare (insert r p2.toFinset) := by
  rintro ⟨a, c, s, hs, hsub⟩
  have hcorner_board : ∀ x ∈ corners a c s, x ∈ board n := by
    intro x hx
    have := hsub hx
    rcases Finset.mem_insert.mp this with h | h
    · exact h ▸ hrb
    · exact hb x (List.mem_toFinset.mp h)
  have hfar : (a + s, c + s) ∈ board n :=
    hcorner_board _ (by simp [mem_corners])
  rw [mem_board] at hfar
  by_cases hrmem : r ∈ corners a c s
  · -- the square runs through r, so completesL must have fired
    have : completesL (squaresList n) p2 r = true := by
      simp only [completesL, List.any_eq_true]
      refine ⟨[(a, c), (a, c + s), (a + s, c), (a + s, c + s)],
        mem_squaresList.mpr ⟨a, c, s, hs, hfar.1, hfar.2, rfl⟩, ?_⟩
      have hmem : r ∈ ([(a, c), (a, c + s), (a + s, c), (a + s, c + s)] : List Cell) := by
        rw [← List.mem_toFinset, corners_toFinset]
        exact hrmem
      simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true]
      refine ⟨hmem, ?_⟩
      intro x hx
      have hxc : x ∈ corners a c s := by
        rw [← corners_toFinset, List.mem_toFinset] at *
        exact hx
      rcases Finset.mem_insert.mp (hsub hxc) with h | h
      · simp [h]
      · simp [List.mem_toFinset.mp h]
    rw [hc] at this
    exact absurd this (by simp)
  · -- the square avoids r, so it already sat inside p2
    apply hno
    refine ⟨a, c, s, hs, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp (hsub hx) with h | h
    · exact absurd (h ▸ hx) hrmem
    · exact h

/-! ## Cells and boards -/

theorem mem_allCells {n : ℕ} {x : Cell} : x ∈ allCells n ↔ x ∈ board n := by
  cases x with
  | mk a b => simp [allCells, mem_board, List.mem_flatMap]

theorem onBoard_iff {n : ℕ} {x : Cell} : onBoard n x = true ↔ x ∈ board n := by
  simp [onBoard, mem_board]

/-! ## The main induction -/

theorem go_sound (t : Table) (n : ℕ) :
    ∀ (fuel : ℕ) (hist : List Cell),
      hist.length % 2 = 0 →
      (∀ x ∈ hist, x ∈ board n) →
      ¬ HasSquare (stonesOf false hist).toFinset →
      go t (squaresList n) n fuel hist = true →
      P1CanWin n (stonesOf true hist).toFinset (stonesOf false hist).toFinset := by
  intro fuel
  induction fuel with
  | zero => intro hist _ _ _ h; simp [go] at h
  | succ fuel ih =>
    intro hist hEven hBoard hNoSq2 h
    simp only [go] at h
    set p1L := stonesOf true hist with hp1L
    set p2L := stonesOf false hist with hp2L
    have hp2board : ∀ x ∈ p2L, x ∈ board n := fun x hx =>
      hBoard x ((mem_stonesOf hist false).mpr (Or.inl hx))
    split at h
    · exact absurd h (by simp)
    · rename_i m hsm
      split at h
      · exact absurd h (by simp)
      · rename_i hguard
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', List.contains_iff_mem] at hguard
        obtain ⟨⟨hmb, hm1'⟩, hm2'⟩ := hguard
        have hmbT : onBoard n m = true := by
          revert hmb; cases onBoard n m <;> simp
        have hmb' : m ∈ board n := onBoard_iff.mp hmbT
        have hmE : m ∈ empties n p1L.toFinset p2L.toFinset :=
          mem_empties.mpr ⟨hmb', by simpa using hm1', by simpa using hm2'⟩
        split at h
        · -- P1 completes a square: the `now` constructor
          rename_i hwin
          refine P1CanWin.now m hmE ?_
          have := hasSquareL_sound (n := n) (L := m :: p1L) hwin
          simpa using this
        · rename_i hnowin
          split at h
          · exact absurd h (by simp)
          · rename_i hrep
            rw [List.all_eq_true] at h
            -- shared facts about the extended history
            have hlen' : (hist ++ [m]).length % 2 = 1 := by
              rw [List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega
            have hstone1 : stonesOf true (hist ++ [m]) = p1L ++ [m] :=
              stonesOf_snoc_even_true hEven
            have hstone2 : stonesOf false (hist ++ [m]) = p2L :=
              stonesOf_snoc_even_false hEven
            have hp1'F : (p1L ++ [m]).toFinset = insert m p1L.toFinset := by
              ext x
              simp [List.toFinset_append]
            -- history membership splits into the two stone lists
            have hh : ∀ x : Cell, x ∈ hist ++ [m] ↔ x ∈ p1L ++ [m] ∨ x ∈ p2L := by
              intro x
              rw [mem_stonesOf (hist ++ [m]) true, hstone1]
              simp only [Bool.not_true]
              rw [hstone2]
            -- membership in the reply list matches membership in empties
            have hreplies : ∀ r : Cell,
                r ∈ (allCells n).filter (fun c => !((hist ++ [m]).contains c)) ↔
                r ∈ empties n (insert m p1L.toFinset) p2L.toFinset := by
              intro r
              rw [List.mem_filter, mem_empties]
              constructor
              · rintro ⟨hall, hnc⟩
                have hnmem : r ∉ hist ++ [m] := by
                  intro hx
                  simp [hx] at hnc
                rw [hh] at hnmem
                push Not at hnmem
                refine ⟨mem_allCells.mp hall, ?_, ?_⟩
                · intro hx
                  apply hnmem.1
                  rcases Finset.mem_insert.mp hx with h' | h'
                  · simp [h']
                  · simp [List.mem_toFinset.mp h']
                · intro hx
                  exact hnmem.2 (List.mem_toFinset.mp hx)
              · rintro ⟨hb, h1, h2⟩
                refine ⟨mem_allCells.mpr hb, ?_⟩
                have hnmem : r ∉ hist ++ [m] := by
                  rw [hh]
                  push Not
                  refine ⟨?_, fun hx => h2 (List.mem_toFinset.mpr hx)⟩
                  intro hx
                  apply h1
                  rcases List.mem_append.mp hx with h' | h'
                  · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h')
                  · rw [List.mem_singleton] at h'
                    rw [h']
                    exact Finset.mem_insert_self m _
                simp [hnmem]
            -- assemble the `step` constructor
            have hne : (empties n (insert m p1L.toFinset) p2L.toFinset).Nonempty := by
              have : ((allCells n).filter
                  (fun c => !((hist ++ [m]).contains c))) ≠ [] := by
                intro hnil
                rw [hnil] at hrep
                simp at hrep
              obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ this
              exact ⟨r, (hreplies r).mp hr⟩
            have hsafe : ∀ r ∈ empties n (insert m p1L.toFinset) p2L.toFinset,
                ¬ HasSquare (insert r p2L.toFinset) := by
              intro r hr
              have hr' := (hreplies r).mpr hr
              have hpred := h r hr'
              rw [Bool.and_eq_true] at hpred
              have hcf : completesL (squaresList n) p2L r = false := by
                have := hpred.1
                simpa using this
              have hrb : r ∈ board n := (mem_empties.mp hr).1
              exact not_hasSquare_insert hrb hp2board hNoSq2 hcf
            refine P1CanWin.step m hmE hne hsafe ?_
            intro r hr
            have hr' := (hreplies r).mpr hr
            have hpred := h r hr'
            rw [Bool.and_eq_true] at hpred
            have hgo := hpred.2
            have hrb : r ∈ board n := (mem_empties.mp hr).1
            have hnosq' : ¬ HasSquare (insert r p2L.toFinset) :=
              hsafe r hr
            -- recurse on the doubly extended history
            have hlen'' : ((hist ++ [m]) ++ [r]).length % 2 = 0 := by
              simp [List.length_append]; omega
            have hboard'' : ∀ x ∈ (hist ++ [m]) ++ [r], x ∈ board n := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · rcases List.mem_append.mp hx with hx | hx
                · exact hBoard x hx
                · rw [List.mem_singleton] at hx; exact hx ▸ hmb'
              · rw [List.mem_singleton] at hx; exact hx ▸ hrb
            have hs1 : stonesOf true ((hist ++ [m]) ++ [r]) = p1L ++ [m] := by
              rw [stonesOf_snoc_odd_true hlen', hstone1]
            have hs2 : stonesOf false ((hist ++ [m]) ++ [r]) = p2L ++ [r] := by
              rw [stonesOf_snoc_odd_false hlen', hstone2]
            have hnosq'' : ¬ HasSquare (stonesOf false ((hist ++ [m]) ++ [r])).toFinset := by
              rw [hs2]
              intro hcon
              apply hnosq'
              have : (p2L ++ [r]).toFinset = insert r p2L.toFinset := by
                ext x
                simp [List.toFinset_append]
              rwa [this] at hcon
            have := ih ((hist ++ [m]) ++ [r]) hlen'' hboard'' hnosq'' hgo
            rw [hs1, hs2] at this
            have hins : (p2L ++ [r]).toFinset = insert r p2L.toFinset := by
              ext x
              simp [List.toFinset_append]
            rwa [hp1'F, hins] at this

theorem check_sound {t : Table} {n : ℕ} (h : check t n = true) :
    P1CanWin n ∅ ∅ := by
  have := go_sound t n (n * n + 1) [] (by simp) (by simp)
    (by simpa [stonesOf] using not_hasSquare_empty) (by simpa [check] using h)
  simpa [stonesOf] using this

end SquareAchievement
