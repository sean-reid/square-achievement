import SquareAchievement.Compute.Uniform
import SquareAchievement.Compute.CheckerSound
import SquareAchievement.Compute.WinsWith

/-!
# Soundness of the forced-tree checker

`goForced` recurses only on block replies; soundness covers the rest.
At each forced node the strategy threatens, so a reply that blocks no
threat leaves one standing, and the threat cell wins on the next
move. The per-node scan `threatsL squares p2 = []` replaces the
per-reply completion checks of `go`: it says no empty cell finishes a
square for the opponent, which is the safety obligation of
`P1CanWin.step`.
-/

namespace SquareAchievement

/-- The corner list of a listed square has no duplicates. -/
theorem squaresList_nodup {n : ℕ} {sq : List Cell}
    (hsq : sq ∈ squaresList n) : sq.Nodup := by
  obtain ⟨r, c, s, hs, hr, hc, rfl⟩ := mem_squaresList.mp hsq
  have h1 : (r, c) ≠ (r, c + s) := by simp [Prod.ext_iff]; omega
  have h2 : (r, c) ≠ (r + s, c) := by simp [Prod.ext_iff]; omega
  have h3 : (r, c) ≠ (r + s, c + s) := by simp [Prod.ext_iff]; omega
  have h4 : (r, c + s) ≠ (r + s, c) := by simp [Prod.ext_iff]; omega
  have h5 : (r, c + s) ≠ (r + s, c + s) := by simp [Prod.ext_iff]; omega
  have h6 : (r + s, c) ≠ (r + s, c + s) := by simp [Prod.ext_iff]; omega
  simp [List.nodup_cons, h1, h2, h3, h4, h5, h6]

/-- Cells of a listed square lie on the board. -/
theorem squaresList_on_board {n : ℕ} {sq : List Cell}
    (hsq : sq ∈ squaresList n) : ∀ x ∈ sq, x ∈ board n := by
  obtain ⟨r, c, s, hs, hr, hc, rfl⟩ := mem_squaresList.mp hsq
  intro x hx
  rw [mem_board]
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> constructor <;> omega

/-- What a `threatsL` entry certifies: a listed square one unoccupied
cell away from `mine`. -/
theorem mem_threatsL {squares : List (List Cell)} {mine occ : List Cell}
    {z : Cell} (h : z ∈ threatsL squares mine occ) :
    ∃ sq ∈ squares, sq.filter (fun x => !mine.contains x) = [z] ∧
      occ.contains z = false := by
  simp only [threatsL, List.mem_filterMap] at h
  obtain ⟨sq, hsq, hm⟩ := h
  refine ⟨sq, hsq, ?_⟩
  split at hm
  · rename_i m' heq
    split at hm
    · simp at hm
    · rename_i hocc
      obtain rfl := Option.some_inj.mp hm
      refine ⟨heq, ?_⟩
      revert hocc
      cases occ.contains m' <;> simp
  · simp at hm


/-- Conversely, a square one empty cell away from `mine` puts that
cell in `threatsL`. -/
theorem threatsL_of_filter {squares : List (List Cell)}
    {mine occ : List Cell} {sq : List Cell} {z : Cell}
    (hsq : sq ∈ squares)
    (hfil : sq.filter (fun x => !mine.contains x) = [z])
    (hocc : occ.contains z = false) :
    z ∈ threatsL squares mine occ := by
  have hocc' : z ∉ occ := by
    intro hx
    rw [List.contains_iff_mem.mpr hx] at hocc
    exact absurd hocc (by simp)
  simp only [threatsL, List.mem_filterMap]
  exact ⟨sq, hsq, by rw [hfil]; simp [hocc']⟩

/-- Playing a threat cell completes its square. -/
theorem threat_wins {n : ℕ} {mine occ : List Cell} {z : Cell}
    (h : z ∈ threatsL (squaresList n) mine occ) :
    HasSquare (insert z mine.toFinset) ∧ z ∈ board n ∧
      occ.contains z = false := by
  obtain ⟨sq, hsq, hfil, hocc⟩ := mem_threatsL h
  have hzsq : z ∈ sq :=
    List.mem_of_mem_filter (hfil ▸ List.mem_cons_self ..)
  have hzb : z ∈ board n := squaresList_on_board hsq z hzsq
  obtain ⟨r, c, s, hs, hr, hc, hshape⟩ := mem_squaresList.mp hsq
  refine ⟨⟨r, c, s, hs, ?_⟩, hzb, hocc⟩
  rw [← corners_toFinset, ← hshape]
  intro x hx
  rw [List.mem_toFinset] at hx
  by_cases hxm : mine.contains x
  · exact Finset.mem_insert_of_mem
      (List.mem_toFinset.mpr (List.contains_iff_mem.mp hxm))
  · have : x ∈ sq.filter (fun x => !mine.contains x) :=
      List.mem_filter.mpr ⟨hx, by simpa using hxm⟩
    rw [hfil, List.mem_singleton] at this
    rw [this]
    exact Finset.mem_insert_self z _

/-- With the opponent's scan empty, no empty cell completes for them. -/
theorem completesL_eq_false_of_threats_nil {n : ℕ} {mine occ : List Cell}
    {r : Cell} (hnil : threatsL (squaresList n) mine occ = [])
    (hro : occ.contains r = false) (hrm : r ∉ mine) :
    completesL (squaresList n) mine r = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  simp only [completesL, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at hc
  obtain ⟨sq, hsq, hrmem, hall⟩ := hc
  have hnodup := squaresList_nodup hsq
  have hfil : sq.filter (fun x => !mine.contains x) = [r] := by
    have hrf : r ∈ sq.filter (fun x => !mine.contains x) :=
      List.mem_filter.mpr ⟨hrmem, by simpa using hrm⟩
    have honly : ∀ x ∈ sq.filter (fun x => !mine.contains x), x = r := by
      intro x hx
      have hxsq := List.mem_of_mem_filter hx
      have hxnm : x ∉ mine := by
        have := (List.mem_filter.mp hx).2
        simpa [List.contains_iff_mem] using this
      rcases hall x hxsq with h' | h'
      · exact by simpa using h'
      · exact absurd h' hxnm
    have hnodupf : (sq.filter (fun x => !mine.contains x)).Nodup :=
      hnodup.filter _
    rcases hcase : sq.filter (fun x => !mine.contains x) with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rw [hcase] at hrf; simp at hrf
    · rw [hcase] at hrf honly
      have := honly a (List.mem_cons_self ..)
      simp_all
    · rw [hcase] at honly hnodupf
      have ha := honly a (by simp)
      have hb := honly b (by simp)
      rw [List.nodup_cons] at hnodupf
      exact absurd (ha.trans hb.symm) (fun hab => hnodupf.1 (hab ▸ by simp))
  have : r ∈ threatsL (squaresList n) mine occ :=
    threatsL_of_filter hsq hfil hro
  rw [hnil] at this
  simp at this

/-- Soundness of the forced-tree checker, in the strong form: the tree
the strategy itself plays is winning. The same induction as `go_sound`;
the non-blocking replies, which the checker never visits, are covered
by the strategy taking the standing threat, which `TakesWinsOn`
guarantees. -/
theorem goForcedS_winsWith (σ : Strategy) (box n : ℕ) (hot : Option Cell) :
    ∀ (fuel : ℕ) (hist : List Cell),
      hist.length % 2 = 0 →
      (∀ x ∈ hist, x ∈ board n) →
      (∀ x ∈ stonesOf true hist, inBox box x = true) →
      TakesWinsOn σ box n hist →
      ¬ HasSquare (stonesOf false hist).toFinset →
      goForcedS σ box (squaresList n) n hot fuel hist = true →
      WinsWith σ n hist := by
  intro fuel
  induction fuel with
  | zero => intro hist _ _ _ _ _ h; simp [goForcedS] at h
  | succ fuel ih =>
    intro hist hEven hBoard hP1box htake hNoSq2 h
    simp only [goForcedS] at h
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
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', Bool.not_eq_true,
          List.contains_iff_mem] at hguard
        obtain ⟨⟨hmb, hm1'⟩, hm2'⟩ := hguard
        have hmbT : onBoard n m = true := by
          revert hmb; cases onBoard n m <;> simp
        have hmb' : m ∈ board n := onBoard_iff.mp hmbT
        have hmE : m ∈ empties n p1L.toFinset p2L.toFinset :=
          mem_empties.mpr ⟨hmb', by simpa using hm1', by simpa using hm2'⟩
        split at h
        · -- P1 completes a square: the `now` constructor
          rename_i hwin
          refine WinsWith.now m hsm hmE ?_
          have := hasSquareL_sound (n := n) (L := m :: p1L) hwin
          simpa using this
        · rename_i hnowin
          split at h
          · exact absurd h (by simp)
          · rename_i hmbox
            have hmboxT : inBox box m = true := by
              revert hmbox; cases inBox box m <;> simp
            split at h
            · exact absurd h (by simp)
            · rename_i hp2scan
              have hscan : threatsL (squaresList n) p2L ((m :: p1L) ++ p2L) = [] := by
                have : ((threatsL (squaresList n) p2L ((m :: p1L) ++ p2L)).isEmpty) = true := by
                  revert hp2scan
                  cases (threatsL (squaresList n) p2L ((m :: p1L) ++ p2L)).isEmpty <;> simp
                simpa [List.isEmpty_iff] using this
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
                simp [List.toFinset_append, or_comm]
              have hh : ∀ x : Cell, x ∈ hist ++ [m] ↔ x ∈ p1L ++ [m] ∨ x ∈ p2L := by
                intro x
                rw [mem_stonesOf (hist ++ [m]) true, hstone1]
                simp only [Bool.not_true]
                rw [hstone2]
              -- safety for every empty reply, from the single scan
              have hsafe : ∀ r ∈ empties n (insert m p1L.toFinset) p2L.toFinset,
                  ¬ HasSquare (insert r p2L.toFinset) := by
                intro r hr
                obtain ⟨hrb, hr1, hr2⟩ := mem_empties.mp hr
                have hrm : r ∉ p2L := fun hx => hr2 (List.mem_toFinset.mpr hx)
                have hrocc : (((m :: p1L) ++ p2L).contains r) = false := by
                  rw [Bool.eq_false_iff]
                  intro hx
                  rw [List.contains_iff_mem, List.mem_append, List.mem_cons] at hx
                  rcases hx with (rfl | hx) | hx
                  · exact hr1 (Finset.mem_insert_self r _)
                  · exact hr1 (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx))
                  · exact hrm hx
                have hcf := completesL_eq_false_of_threats_nil hscan hrocc hrm
                exact not_hasSquare_insert hrb hp2board hNoSq2 hcf
              -- recursion helper shared by both level shapes
              have hrec : ∀ r : Cell, r ∈ board n →
                  r ∉ hist ++ [m] →
                  goForcedS σ box (squaresList n) n hot fuel ((hist ++ [m]) ++ [r]) = true →
                  WinsWith σ n ((hist ++ [m]) ++ [r]) := by
                intro r hrb hrmem hgo
                have hrE : r ∈ empties n (insert m p1L.toFinset) p2L.toFinset := by
                  rw [hh] at hrmem
                  push_neg at hrmem
                  refine mem_empties.mpr ⟨hrb, ?_, ?_⟩
                  · intro hx
                    apply hrmem.1
                    rcases Finset.mem_insert.mp hx with h' | h'
                    · simp [h']
                    · simp [List.mem_toFinset.mp h']
                  · intro hx
                    exact hrmem.2 (List.mem_toFinset.mp hx)
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
                have hins : (p2L ++ [r]).toFinset = insert r p2L.toFinset := by
                  ext x
                  simp [List.toFinset_append, or_comm]
                have hnosq'' : ¬ HasSquare (stonesOf false ((hist ++ [m]) ++ [r])).toFinset := by
                  rw [hs2, hins]
                  exact hsafe r hrE
                have hP1box'' : ∀ x ∈ stonesOf true ((hist ++ [m]) ++ [r]), inBox box x = true := by
                  intro x hx
                  rw [hs1, List.mem_append, List.mem_singleton] at hx
                  rcases hx with hx | rfl
                  · exact hP1box x hx
                  · exact hmboxT
                have htake'' : TakesWinsOn σ box n ((hist ++ [m]) ++ [r]) := by
                  rw [List.append_assoc]
                  exact htake.extend _
                exact ih ((hist ++ [m]) ++ [r]) hlen'' hboard'' hP1box'' htake'' hnosq'' hgo
              split at h
              · -- free level: every reply enumerated
                rename_i hfree
                have hreplies : ∀ r : Cell,
                    r ∈ (allCells n).filter (fun c => !((hist ++ [m]).contains c)) ↔
                    r ∈ empties n (insert m p1L.toFinset) p2L.toFinset := by
                  intro r
                  rw [List.mem_filter, mem_empties]
                  constructor
                  · rintro ⟨hall, hnc⟩
                    have hnmem : r ∉ hist ++ [m] := by
                      intro hx
                      simp [List.contains_iff_mem, hx] at hnc
                    rw [hh] at hnmem
                    push_neg at hnmem
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
                      push_neg
                      refine ⟨?_, fun hx => h2 (List.mem_toFinset.mpr hx)⟩
                      intro hx
                      apply h1
                      rcases List.mem_append.mp hx with h' | h'
                      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h')
                      · rw [List.mem_singleton] at h'
                        rw [h']
                        exact Finset.mem_insert_self m _
                    simp [List.contains_iff_mem, hnmem]
                split at h
                · exact absurd h (by simp)
                · rename_i hrep
                  rw [List.all_eq_true] at h
                  have hne : (empties n (insert m p1L.toFinset) p2L.toFinset).Nonempty := by
                    have : ((allCells n).filter
                        (fun c => !((hist ++ [m]).contains c))) ≠ [] := by
                      intro hnil
                      rw [hnil] at hrep
                      simp at hrep
                    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ this
                    exact ⟨r, (hreplies r).mp hr⟩
                  refine WinsWith.step m hsm hmE hne hsafe ?_
                  intro r hr
                  have hr' := (hreplies r).mpr hr
                  obtain ⟨hrb, -, -⟩ := mem_empties.mp hr
                  have hrmem : r ∉ hist ++ [m] := by
                    have := (List.mem_filter.mp hr').2
                    intro hx
                    simp [List.contains_iff_mem, hx] at this
                  exact hrec r hrb hrmem (h r hr')
              · -- forced level: threats stand, only blocks recurse
                rename_i hlv
                split at h
                · exact absurd h (by simp)
                · rename_i hthne
                  split at h
                  · exact absurd h (by simp)
                  · rename_i hthbox
                    split at h
                    · exact absurd h (by simp)
                    · rename_i hhot
                      rw [List.all_eq_true] at h
                      set ths := threatsL (squaresList n) (m :: p1L) ((m :: p1L) ++ p2L) with hths
                      have hthne' : ths ≠ [] := by
                        intro hnil
                        rw [hnil] at hthne
                        simp at hthne
                      obtain ⟨z₀, hz₀⟩ := List.exists_mem_of_ne_nil _ hthne'
                      -- a threat cell is an empty cell
                      have hthE : ∀ z ∈ ths,
                          z ∈ empties n (insert m p1L.toFinset) p2L.toFinset ∧
                          HasSquare (insert z (insert m p1L.toFinset)) := by
                        intro z hz
                        obtain ⟨hwin', hzb, hzocc⟩ := threat_wins (hths ▸ hz)
                        rw [Bool.eq_false_iff] at hzocc
                        have hz3 : z ≠ m ∧ z ∉ p1L ∧ z ∉ p2L := by
                          refine ⟨?_, ?_, ?_⟩ <;> intro hx <;> apply hzocc <;>
                            rw [List.contains_iff_mem, List.mem_append,
                              List.mem_cons]
                          · exact Or.inl (Or.inl hx)
                          · exact Or.inl (Or.inr hx)
                          · exact Or.inr hx
                        refine ⟨mem_empties.mpr ⟨hzb, ?_, ?_⟩, ?_⟩
                        · intro hx
                          rcases Finset.mem_insert.mp hx with h' | h'
                          · exact hz3.1 h'
                          · exact hz3.2.1 (List.mem_toFinset.mp h')
                        · intro hx
                          exact hz3.2.2 (List.mem_toFinset.mp hx)
                        · have : (m :: p1L).toFinset = insert m p1L.toFinset := by
                            ext x; simp
                          rwa [this] at hwin'
                      have hne : (empties n (insert m p1L.toFinset) p2L.toFinset).Nonempty :=
                        ⟨z₀, (hthE z₀ hz₀).1⟩
                      refine WinsWith.step m hsm hmE hne hsafe ?_
                      intro r hr
                      by_cases hrths : r ∈ ths
                      · -- the block: the checker visited this branch
                        obtain ⟨hrb, -, -⟩ := mem_empties.mp hr
                        have hrmem : r ∉ hist ++ [m] := by
                          obtain ⟨-, -, hzocc⟩ := threat_wins (hths ▸ hrths)
                          rw [Bool.eq_false_iff] at hzocc
                          intro hx
                          rw [hh] at hx
                          apply hzocc
                          rw [List.contains_iff_mem, List.mem_append]
                          rcases hx with hx | hx
                          · rcases List.mem_append.mp hx with hx | hx
                            · exact Or.inl (List.mem_cons_of_mem m hx)
                            · rw [List.mem_singleton] at hx
                              rw [hx]
                              exact Or.inl (List.mem_cons_self ..)
                          · exact Or.inr hx
                        exact hrec r hrb hrmem (h r hrths)
                      · -- non-blocking reply: the strategy takes a standing threat
                        obtain ⟨hz₀E, -⟩ := hthE z₀ hz₀
                        have hz₀ne : z₀ ≠ r := fun he => hrths (he ▸ hz₀)
                        obtain ⟨hz₀b, hz₀1, hz₀2⟩ := mem_empties.mp hz₀E
                        obtain ⟨hrb, hr1, hr2⟩ := mem_empties.mp hr
                        have hlen'' : ((hist ++ [m]) ++ [r]).length % 2 = 0 := by
                          simp [List.length_append]; omega
                        have hs1 : stonesOf true ((hist ++ [m]) ++ [r]) = p1L ++ [m] := by
                          rw [stonesOf_snoc_odd_true hlen', hstone1]
                        have hs2 : stonesOf false ((hist ++ [m]) ++ [r]) = p2L ++ [r] := by
                          rw [stonesOf_snoc_odd_false hlen', hstone2]
                        have hboard'' : ∀ x ∈ (hist ++ [m]) ++ [r], x ∈ board n := by
                          intro x hx
                          rcases List.mem_append.mp hx with hx | hx
                          · rcases List.mem_append.mp hx with hx | hx
                            · exact hBoard x hx
                            · rw [List.mem_singleton] at hx; exact hx ▸ hmb'
                          · rw [List.mem_singleton] at hx; exact hx ▸ hrb
                        have hP1box'' : ∀ x ∈ stonesOf true ((hist ++ [m]) ++ [r]),
                            inBox box x = true := by
                          intro x hx
                          rw [hs1, List.mem_append, List.mem_singleton] at hx
                          rcases hx with hx | rfl
                          · exact hP1box x hx
                          · exact hmboxT
                        -- the standing threat is still a threat after the reply
                        have hz₀th :
                            z₀ ∈ threatsL (squaresList n) (p1L ++ [m]) ((hist ++ [m]) ++ [r]) := by
                          obtain ⟨sq, hsq, hfil, hocc⟩ := mem_threatsL (hths ▸ hz₀)
                          refine threatsL_of_filter hsq ?_ ?_
                          · rw [← hfil]
                            apply List.filter_congr
                            intro x _
                            congr 1
                            rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
                            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                            tauto
                          · rw [Bool.eq_false_iff]
                            intro hx
                            rw [List.contains_iff_mem, List.mem_append, List.mem_singleton] at hx
                            rcases hx with hx | rfl
                            · rw [hh] at hx
                              rcases hx with hx | hx
                              · rw [List.mem_append, List.mem_singleton] at hx
                                rcases hx with hx | rfl
                                · exact hz₀1 (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx))
                                · exact hz₀1 (Finset.mem_insert_self _ _)
                              · exact hz₀2 (List.mem_toFinset.mpr hx)
                            · exact hz₀ne rfl
                        have hthne'' :
                            threatsL (squaresList n) (stonesOf true ((hist ++ [m]) ++ [r]))
                            ((hist ++ [m]) ++ [r]) ≠ [] := by
                          rw [hs1]
                          exact List.ne_nil_of_mem hz₀th
                        obtain ⟨z, hσz, hzth⟩ := htake ([m] ++ [r])
                          (by rw [← List.append_assoc]; exact hlen'')
                          (by rw [← List.append_assoc]; exact hP1box'')
                          (by rw [← List.append_assoc]; exact hboard'')
                          (by rw [← List.append_assoc]; exact hthne'')
                        rw [← List.append_assoc] at hσz hzth
                        rw [hs1] at hzth
                        obtain ⟨hwz, hzb, hzocc⟩ := threat_wins hzth
                        rw [Bool.eq_false_iff] at hzocc
                        refine WinsWith.now z hσz ?_ ?_
                        · rw [hs1, hs2]
                          refine mem_empties.mpr ⟨hzb, ?_, ?_⟩
                          · intro hx
                            rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
                            apply hzocc
                            rw [List.contains_iff_mem, List.mem_append, List.mem_append]
                            rcases hx with hx | hx
                            · exact Or.inl (Or.inl ((mem_stonesOf hist true).mpr (Or.inl hx)))
                            · exact Or.inl (Or.inr (List.mem_singleton.mpr hx))
                          · intro hx
                            rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
                            apply hzocc
                            rw [List.contains_iff_mem, List.mem_append, List.mem_append]
                            rcases hx with hx | hx
                            · exact Or.inl (Or.inl ((mem_stonesOf hist false).mpr (Or.inl hx)))
                            · exact Or.inr (List.mem_singleton.mpr hx)
                        · rw [hs1]; exact hwz

/-- The existential form, for any strategy that takes its wins. -/
theorem goForcedS_sound (σ : Strategy) (box n : ℕ) (hot : Option Cell)
    (fuel : ℕ) (hist : List Cell)
    (hEven : hist.length % 2 = 0)
    (hBoard : ∀ x ∈ hist, x ∈ board n)
    (hP1box : ∀ x ∈ stonesOf true hist, inBox box x = true)
    (htake : TakesWinsOn σ box n hist)
    (hNoSq2 : ¬ HasSquare (stonesOf false hist).toFinset)
    (h : goForcedS σ box (squaresList n) n hot fuel hist = true) :
    P1CanWin n (stonesOf true hist).toFinset (stonesOf false hist).toFinset :=
  (goForcedS_winsWith σ box n hot fuel hist hEven hBoard hP1box htake hNoSq2 h).p1CanWin hEven

/-- A checked run from the empty board: following the strategy wins. -/
theorem checkForcedS_winsWith {σ : Strategy} {box n : ℕ}
    (htake : TakesWinsOn σ box n []) (h : checkForcedS σ box n = true) :
    WinsWith σ n [] :=
  goForcedS_winsWith σ box n none (n * n + 1) [] (by simp) (by simp) (by simp [stonesOf])
    htake (by simpa [stonesOf] using not_hasSquare_empty) (by simpa [checkForcedS] using h)

theorem checkForcedS_sound {σ : Strategy} {box n : ℕ}
    (htake : TakesWinsOn σ box n []) (h : checkForcedS σ box n = true) :
    P1CanWin n ∅ ∅ := by
  have := (checkForcedS_winsWith htake h).p1CanWin (by simp)
  simpa [stonesOf] using this

/-! ## The table strategy takes its wins -/

/-- `threatsL` reads the occupancy list only through membership. -/
theorem threatsL_congr_occ {squares : List (List Cell)} {mine occ occ' : List Cell}
    (h : ∀ x, x ∈ occ ↔ x ∈ occ') :
    threatsL squares mine occ = threatsL squares mine occ' := by
  unfold threatsL
  congr 1
  funext sq
  split
  · rename_i m heq
    have : occ.contains m = occ'.contains m := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      exact h m
    rw [this]
  · rfl

/-- The choice `minThreat` makes between two threat cells. -/
def pickMin (best : Option Cell) (m : Cell) : Option Cell :=
  match best with
  | none => some m
  | some b => if cellLt m b then some m else some b

/-- `minThreat` folds `pickMin` over the threat cells, in order. -/
theorem minThreat_eq_foldl (squares : List (List Cell)) (mine occ : List Cell) :
    minThreat squares mine occ = (threatsL squares mine occ).foldl pickMin none := by
  unfold minThreat threatsL
  suffices hgen : ∀ (sqs : List (List Cell)) (init : Option Cell),
      sqs.foldl (fun best sq =>
        match sq.filter (fun x => !mine.contains x) with
        | [m] =>
          if occ.contains m then best
          else
            match best with
            | none => some m
            | some b => if cellLt m b then some m else some b
        | _ => best) init =
      (sqs.filterMap fun sq =>
        match sq.filter (fun x => !mine.contains x) with
        | [m] => if occ.contains m then none else some m
        | _ => none).foldl pickMin init from hgen squares none
  intro sqs
  induction sqs with
  | nil => intro init; rfl
  | cons sq rest ih =>
    intro init
    rw [List.foldl_cons, List.filterMap_cons]
    rcases hfil : sq.filter (fun x => !mine.contains x) with _ | ⟨m, _ | ⟨b, rest'⟩⟩
    · simp only; exact ih init
    · by_cases hocc : occ.contains m = true
      · simp only [hocc, if_true]; exact ih init
      · simp only [hocc, Bool.false_eq_true, if_false, List.foldl_cons]
        rw [ih]
        rfl
    · simp only; exact ih init

/-- A fold of `pickMin` that ends on a cell started on it or picked it. -/
theorem foldl_pickMin_mem : ∀ (l : List Cell) (init : Option Cell) {z : Cell},
    l.foldl pickMin init = some z → z ∈ l ∨ init = some z := by
  intro l
  induction l with
  | nil => intro init z h; exact Or.inr h
  | cons m rest ih =>
    intro init z h
    rw [List.foldl_cons] at h
    rcases ih _ h with hz | hz
    · exact Or.inl (List.mem_cons_of_mem _ hz)
    · unfold pickMin at hz
      split at hz
      · exact Or.inl (Option.some_inj.mp hz ▸ List.mem_cons_self ..)
      · split at hz
        · exact Or.inl (Option.some_inj.mp hz ▸ List.mem_cons_self ..)
        · exact Or.inr hz

/-- `minThreat` returns a member of `threatsL`. -/
theorem minThreat_some_mem {squares : List (List Cell)} {mine occ : List Cell} {z : Cell}
    (h : minThreat squares mine occ = some z) : z ∈ threatsL squares mine occ := by
  rw [minThreat_eq_foldl] at h
  rcases foldl_pickMin_mem _ none h with hz | hz
  · exact hz
  · simp at hz

/-- A fold of `pickMin` is `none` only on the empty list. -/
theorem foldl_pickMin_eq_none : ∀ (l : List Cell) (init : Option Cell),
    l.foldl pickMin init = none → l = [] ∧ init = none := by
  intro l
  induction l with
  | nil => intro init h; exact ⟨rfl, h⟩
  | cons m rest ih =>
    intro init h
    rw [List.foldl_cons] at h
    have := (ih _ h).2
    unfold pickMin at this
    split at this
    · simp at this
    · split at this <;> simp at this

/-- `minThreat` is `none` only when there is no threat. -/
theorem minThreat_eq_none {squares : List (List Cell)} {mine occ : List Cell}
    (h : minThreat squares mine occ = none) : threatsL squares mine occ = [] := by
  rw [minThreat_eq_foldl] at h
  exact (foldl_pickMin_eq_none _ none h).1

/-- The table strategy takes its wins: its first reflex is `minThreat`. -/
theorem takesWinsOn_table (t : Table) (n : ℕ) (root : List Cell) :
    TakesWinsOn (strategyMove t) t.box n root := by
  intro tail _ _ _ hne
  have hocc : ∀ x, x ∈ root ++ tail ↔
      x ∈ stonesOf true (root ++ tail) ++ stonesOf false (root ++ tail) := by
    intro x
    rw [mem_stonesOf (root ++ tail) true, List.mem_append]
    simp
  rw [threatsL_congr_occ hocc] at hne ⊢
  unfold strategyMove
  rcases hmin : minThreat (squaresList n) (stonesOf true (root ++ tail))
      (stonesOf true (root ++ tail) ++ stonesOf false (root ++ tail)) with _ | z
  · exact absurd (minThreat_eq_none hmin) hne
  · exact ⟨z, by simp [hmin], minThreat_some_mem hmin⟩

/-- The table instance, in the original shape. -/
theorem goForced_sound (t : Table) (n : ℕ) (hot : Option Cell) :
    ∀ (fuel : ℕ) (hist : List Cell),
      hist.length % 2 = 0 →
      (∀ x ∈ hist, x ∈ board n) →
      (∀ x ∈ stonesOf true hist, inBox t.box x = true) →
      ¬ HasSquare (stonesOf false hist).toFinset →
      goForced t (squaresList n) n hot fuel hist = true →
      P1CanWin n (stonesOf true hist).toFinset (stonesOf false hist).toFinset :=
  fun fuel hist hEven hBoard hP1box hNoSq2 h =>
    goForcedS_sound (strategyMove t) t.box n hot fuel hist hEven hBoard hP1box
      (takesWinsOn_table t n hist) hNoSq2 h

theorem checkForced_sound {t : Table} {n : ℕ}
    (h : checkForced t n = true) : P1CanWin n ∅ ∅ :=
  checkForcedS_sound (σ := strategyMove t) (box := t.box) (takesWinsOn_table t n []) h

end SquareAchievement
