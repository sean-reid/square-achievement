import SquareAchievement.Compute.CheckerSound

/-!
# The dual checker

`refuteP1` searches the other side of the game: it returns `true` when
the player to move cannot force a win, every P1 move being answered by
some reply that completes for P2, leads to a full-board draw, or leaves
P1 still unable to win. On the small boards the whole game tree fits in
one evaluation, so no strategy certificate is needed; `refute_sound`
turns the run into `¬ P1CanWin`. The induction inverts each `P1CanWin`
constructor against the run, carrying the mirror-image invariants of
`check_sound`: even history, stones on board, and P1 square-free.
-/

namespace SquareAchievement

/-- Two distinct free cells where `mine` would complete a square: the
mover cannot block both. -/
def twoThreats (squares : List (List Cell)) (mine free : List Cell) : Bool :=
  match free.find? fun t => completesL squares mine t with
  | none => false
  | some t => free.any fun t' => t' != t && completesL squares mine t'

/-- P1, to move after `hist`, cannot force a win. -/
def refuteP1 (squares : List (List Cell)) (n : ℕ) :
    ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    let free := (allCells n).filter fun c => !hist.contains c
    if free.any fun m => completesL squares p1 m then false
    else if twoThreats squares p2 free then true
    else
      free.all fun m =>
        let hist' := hist ++ [m]
        let replies := (allCells n).filter fun c => !hist'.contains c
        replies.isEmpty ||
        (replies.any fun r => completesL squares p2 r) ||
        replies.any fun r => refuteP1 squares n fuel (hist' ++ [r])

/-- The board admits no P1 win from the empty position. -/
def refute (n : ℕ) : Bool :=
  refuteP1 (squaresList n) n (n * n + 1) []

/-- The other direction of the completion bridge: a fired `completesL`
really is a finished square. -/
theorem completesL_sound {n : ℕ} {L : List Cell} {m : Cell}
    (h : completesL (squaresList n) L m = true) :
    HasSquare (insert m L.toFinset) := by
  simp only [completesL, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  obtain ⟨sq, hsq, -, hall⟩ := h
  obtain ⟨r, c, s, hs, -, -, rfl⟩ := mem_squaresList.mp hsq
  refine ⟨r, c, s, hs, ?_⟩
  rw [← corners_toFinset]
  intro x hx
  rw [List.mem_toFinset] at hx
  rcases hall x hx with h' | h'
  · rw [h']
    exact Finset.mem_insert_self m _
  · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h')

theorem refuteP1_sound (n : ℕ) :
    ∀ (fuel : ℕ) (hist : List Cell),
      hist.length % 2 = 0 →
      (∀ x ∈ hist, x ∈ board n) →
      ¬ HasSquare (stonesOf true hist).toFinset →
      refuteP1 (squaresList n) n fuel hist = true →
      ¬ P1CanWin n (stonesOf true hist).toFinset (stonesOf false hist).toFinset := by
  intro fuel
  induction fuel with
  | zero => intro hist _ _ _ h; simp [refuteP1] at h
  | succ fuel ih =>
    intro hist hEven hBoard hNoSq1 h hwin
    simp only [refuteP1] at h
    set p1L := stonesOf true hist with hp1L
    set p2L := stonesOf false hist with hp2L
    have hp1board : ∀ x ∈ p1L, x ∈ board n := fun x hx =>
      hBoard x ((mem_stonesOf hist true).mpr (Or.inl hx))
    have hist_split : ∀ x : Cell, x ∈ hist ↔ x ∈ p1L ∨ x ∈ p2L := by
      intro x
      rw [mem_stonesOf hist true]
      simp only [Bool.not_true]
      rw [← hp1L, ← hp2L]
    -- the completing-move scan came back clean
    split at h
    · exact absurd h (by simp)
    · rename_i hnocomp
      -- shared: membership in the free list, both directions
      have hfree : ∀ m : Cell,
          m ∈ empties n p1L.toFinset p2L.toFinset →
          m ∈ (allCells n).filter fun c => !hist.contains c := by
        intro m hm
        rw [mem_empties] at hm
        rw [List.mem_filter]
        refine ⟨mem_allCells.mpr hm.1, ?_⟩
        have : m ∉ hist := by
          rw [hist_split]
          push Not
          exact ⟨fun hx => hm.2.1 (List.mem_toFinset.mpr hx),
            fun hx => hm.2.2 (List.mem_toFinset.mpr hx)⟩
        simp [this]
      have hfree' : ∀ m : Cell,
          m ∈ ((allCells n).filter fun c => !hist.contains c) →
          m ∈ empties n p1L.toFinset p2L.toFinset := by
        intro m hm
        rw [List.mem_filter] at hm
        have hnmem : m ∉ hist := by
          intro hx
          simp [hx] at hm
        rw [hist_split] at hnmem
        push Not at hnmem
        rw [mem_empties]
        exact ⟨mem_allCells.mp hm.1,
          fun hx => hnmem.1 (List.mem_toFinset.mp hx),
          fun hx => hnmem.2 (List.mem_toFinset.mp hx)⟩
      -- inverting `now` needs only the clean scan; shared by both branches
      have hnow : ∀ m, m ∈ empties n p1L.toFinset p2L.toFinset →
          ¬ HasSquare (insert m p1L.toFinset) := by
        intro m hm
        have hmb : m ∈ board n := (mem_empties.mp hm).1
        have hcf : completesL (squaresList n) p1L m = false := by
          rcases hc : completesL (squaresList n) p1L m
          · rfl
          · exact absurd (List.any_eq_true.mpr ⟨m, hfree m hm, hc⟩) hnocomp
        exact not_hasSquare_insert hmb hp1board hNoSq1 hcf
      split at h
      · -- the double threat: whatever P1 plays, a completion remains
        rename_i htwo
        simp only [twoThreats] at htwo
        rcases hfind : (List.filter (fun c => !hist.contains c) (allCells n)).find?
            fun t => completesL (squaresList n) p2L t with _ | t
        · rw [hfind] at htwo; simp at htwo
        · rw [hfind] at htwo
          have htc : completesL (squaresList n) p2L t = true :=
            List.find?_some hfind
          have htf : t ∈ (allCells n).filter fun c => !hist.contains c :=
            List.mem_of_find?_eq_some hfind
          rw [List.any_eq_true] at htwo
          obtain ⟨t', ht'f, ht'⟩ := htwo
          rw [Bool.and_eq_true, bne_iff_ne] at ht'
          obtain ⟨hne', ht'c⟩ := ht'
          cases hwin with
          | now m hm hwin' => exact hnow m hm hwin'
          | step m hm hne hsafe hwins =>
            -- pick the threat cell P1's move did not cover
            have hpick : ∃ u, u ∈ ((allCells n).filter fun c => !hist.contains c) ∧
                completesL (squaresList n) p2L u = true ∧ u ≠ m := by
              by_cases hcase : t = m
              · exact ⟨t', ht'f, ht'c, fun hx => hne' (hx ▸ hcase.symm ▸ rfl)⟩
              · exact ⟨t, htf, htc, hcase⟩
            obtain ⟨u, huf, huc, hum⟩ := hpick
            have huE := hfree' u huf
            rw [mem_empties] at huE
            have huE' : u ∈ empties n (insert m p1L.toFinset) p2L.toFinset := by
              rw [mem_empties]
              refine ⟨huE.1, ?_, huE.2.2⟩
              intro hx
              rcases Finset.mem_insert.mp hx with hx | hx
              · exact hum hx
              · exact huE.2.1 hx
            exact hsafe u huE' (completesL_sound huc)
      · rw [List.all_eq_true] at h
        cases hwin with
        | now m hm hwin' => exact hnow m hm hwin'
        | step m hm hne hsafe hwins =>
          have hmfree := hfree m hm
          have hmb : m ∈ board n := (mem_empties.mp hm).1
          -- facts about the extended history
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
          have hh : ∀ x : Cell, x ∈ hist ++ [m] ↔ x ∈ p1L ++ [m] ∨ x ∈ p2L := by
            intro x
            rw [mem_stonesOf (hist ++ [m]) true, hstone1]
            simp only [Bool.not_true]
            rw [hstone2]
          have hreplies : ∀ r : Cell,
              r ∈ empties n (insert m p1L.toFinset) p2L.toFinset →
              r ∈ (allCells n).filter fun c => !((hist ++ [m]).contains c) := by
            intro r hr
            rw [mem_empties] at hr
            rw [List.mem_filter]
            refine ⟨mem_allCells.mpr hr.1, ?_⟩
            have : r ∉ hist ++ [m] := by
              rw [hh]
              push Not
              constructor
              · intro hx
                apply hr.2.1
                rw [← hp1'F]
                exact List.mem_toFinset.mpr hx
              · intro hx
                exact hr.2.2 (List.mem_toFinset.mpr hx)
            simp [this]
          have hreplies' : ∀ r : Cell,
              r ∈ ((allCells n).filter fun c => !((hist ++ [m]).contains c)) →
              r ∈ empties n (insert m p1L.toFinset) p2L.toFinset := by
            intro r hr
            rw [List.mem_filter] at hr
            have hnmem : r ∉ hist ++ [m] := by
              intro hx
              simp [hx] at hr
            rw [hh] at hnmem
            push Not at hnmem
            rw [mem_empties]
            refine ⟨mem_allCells.mp hr.1, ?_, ?_⟩
            · intro hx
              apply hnmem.1
              rw [← hp1'F] at hx
              exact List.mem_toFinset.mp hx
            · intro hx
              exact hnmem.2 (List.mem_toFinset.mp hx)
          -- the run's verdict for this particular m
          have hm' := h m hmfree
          rw [Bool.or_eq_true, Bool.or_eq_true] at hm'
          rcases hm' with (hempty | hcompl) | hdeep
          · -- no replies contradicts the constructor's nonemptiness
            obtain ⟨r, hr⟩ := hne
            have := hreplies r hr
            rw [List.isEmpty_iff] at hempty
            rw [hempty] at this
            exact absurd this (List.not_mem_nil)
          · -- a completing reply contradicts safety
            rw [List.any_eq_true] at hcompl
            obtain ⟨r, hrrep, hcomp⟩ := hcompl
            exact hsafe r (hreplies' r hrrep) (completesL_sound hcomp)
          · -- a refuted continuation contradicts the win
            rw [List.any_eq_true] at hdeep
            obtain ⟨r, hrrep, hdeepr⟩ := hdeep
            have hrE := hreplies' r hrrep
            have hrb : r ∈ board n := (mem_empties.mp hrE).1
            have hcf : completesL (squaresList n) p1L m = false := by
              rcases hc : completesL (squaresList n) p1L m
              · rfl
              · exact absurd (List.any_eq_true.mpr ⟨m, hmfree, hc⟩) hnocomp
            have hlen'' : ((hist ++ [m]) ++ [r]).length % 2 = 0 := by
              rw [List.length_append, List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega
            have hboard'' : ∀ x ∈ (hist ++ [m]) ++ [r], x ∈ board n := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · rcases List.mem_append.mp hx with hx | hx
                · exact hBoard x hx
                · rw [List.mem_singleton] at hx; exact hx ▸ hmb
              · rw [List.mem_singleton] at hx; exact hx ▸ hrb
            have hs1 : stonesOf true ((hist ++ [m]) ++ [r]) = p1L ++ [m] := by
              rw [stonesOf_snoc_odd_true hlen', hstone1]
            have hs2 : stonesOf false ((hist ++ [m]) ++ [r]) = p2L ++ [r] := by
              rw [stonesOf_snoc_odd_false hlen', hstone2]
            have hNoSq1'' :
                ¬ HasSquare (stonesOf true ((hist ++ [m]) ++ [r])).toFinset := by
              rw [hs1, hp1'F]
              exact not_hasSquare_insert hmb hp1board hNoSq1 hcf
            have hres := ih ((hist ++ [m]) ++ [r]) hlen'' hboard'' hNoSq1'' hdeepr
            rw [hs1, hs2, hp1'F] at hres
            have hins : (p2L ++ [r]).toFinset = insert r p2L.toFinset := by
              ext x
              simp [List.toFinset_append]
            rw [hins] at hres
            exact hres (hwins r hrE)

/-- Soundness of the dual run. -/
theorem refute_sound {n : ℕ} (h : refute n = true) : ¬ P1CanWin n ∅ ∅ := by
  have := refuteP1_sound n (n * n + 1) [] (by simp) (by simp)
    (by simpa [stonesOf] using not_hasSquare_empty) (by simpa [refute] using h)
  simpa [stonesOf] using this

end SquareAchievement
