import SquareAchievement.General.Dispatch
import Plus.Anchors
import Plus.Agreement
import Plus.Threats

/-!
# The plus rule wins every board from the base up

The wrapper for the rule. It walks the two free reply levels of the
rule's forced run on the anchor board and dispatches every real reply
pair to `simulate`: both replies inside the base board `17` replay the
base branch verbatim; a pair farming nothing replays the branch of the
stand-ins `(22, 22)` and `(22, 21)`; a farm pair replays its anchored
run. The rule reads only the abstraction of the position, so the
stand-in branch is the rule's own play against the real pair.
-/

namespace SquareAchievement.Plus

open SquareAchievement

/-! ## The first two moves -/

theorem threatsIn_nil {k : ℕ} {occ : List Cell} : threatsIn k [] occ = [] := by
  simp [threatsIn]

theorem cellLt_irrefl (a : Cell) : cellLt a a = false := by
  simp [cellLt]

theorem threatsIn_single {k : ℕ} {a : Cell} {occ : List Cell} :
    threatsIn k [a] occ = [] := by
  simp [threatsIn, cellLt_irrefl]

theorem opening_box : opening ∈ board 6 := by
  rw [mem_board]; decide

theorem secondMove_box (o1 : Cell) : secondMove o1 ∈ board 6 := by
  unfold secondMove
  split_ifs <;> (rw [mem_board]; decide)

theorem secondMove_ne_opening (o1 : Cell) : secondMove o1 ≠ opening := by
  unfold secondMove opening
  split_ifs <;> decide

theorem secondMove_ne_self (o1 : Cell) : secondMove o1 ≠ o1 := by
  unfold secondMove
  split_ifs with h1 h2 h3 <;> intro he
  · rcases h1 with rfl | rfl | rfl <;> simp at he
  · rcases h2 with rfl | rfl <;> simp at he
  · rcases h3 with rfl | rfl <;> simp at he
  · exact h3 (Or.inr he.symm)

/-- Far from the opening, the second move is the default. -/
theorem secondMove_far {o1 : Cell} (h : o1 ∉ board 6) : secondMove o1 = (3, 2) := by
  unfold secondMove
  rw [mem_board] at h
  split_ifs with h1 h2 h3
  · exfalso; rcases h1 with rfl | rfl | rfl <;> simp at h
  · exfalso; rcases h2 with rfl | rfl <;> simp at h
  · exfalso; rcases h3 with rfl | rfl <;> simp at h
  · rfl

theorem plusMove_nil {sq : List (List Cell)} : plusMove sq [] = some opening := by
  simp [plusMove, abstractOf, stonesOf, myThreats, theirThreats, threatsIn_nil]

theorem plusMove_two {sq : List (List Cell)} (o1 : Cell) :
    plusMove sq [opening, o1] = some (secondMove o1) := by
  have hne := secondMove_ne_opening o1
  simp only [plusMove, abstractOf, stonesOf, myThreats, theirThreats]
  by_cases h17 : onBoard base o1 = true
  · simp [h17, threatsIn_single, List.filter, hne]
  · simp [h17, threatsIn_single, threatsIn_nil, List.filter, hne]

/-! ## What the anchored certificates say -/

theorem anchorRun_spec {o1 o2 hot : Cell} (h : anchorRun o1 o2 hot = true) :
    farmKey box o1 o2 = some (.farm hot) ∧
      goForcedS plusMove box (squaresList anchorBoard) anchorBoard (some hot)
        (anchorBoard * anchorBoard + 1) [opening, o1, secondMove o1, o2] = true := by
  rw [anchorRun, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h

theorem farAnchors_run (hf : farAnchorsSafe = true) {h1 h2 : ℕ}
    (hh1 : h1 < box) (hh2 : h2 < box) :
    anchorRun (h1 + 17, h2 + 17) (h1 + 17, h2) (h1, h2) = true := by
  rw [farAnchorsSafe, List.all_eq_true] at hf
  have := hf h1 (List.mem_range.mpr hh1)
  rw [List.all_eq_true] at this
  exact this h2 (List.mem_range.mpr hh2)

theorem exactAnchors_run (hf : exactAnchorsSafe = true) {a w h : ℕ}
    (ha : a < box) (hw : w < 17) (hh : h < box)
    (hgate : 2 * box ≤ w) (hesc : 17 ≤ a + w - h) :
    anchorRun (a, w) (a + w - h, w) (a, h) = true ∧
      anchorRun (w, a) (w, a + w - h) (h, a) = true := by
  rw [exactAnchorsSafe, List.all_eq_true] at hf
  have := hf a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at this
  have := this w (List.mem_range.mpr hw)
  rw [List.all_eq_true] at this
  have := this h (List.mem_range.mpr hh)
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hgate, hesc⟩)] at this
  rw [Bool.and_eq_true] at this
  exact this

theorem farNearAnchors_run (hf : farNearAnchorsSafe = true) {a w h : ℕ}
    (ha : a < box) (hw : w < 17) (hh : h < box)
    (hgate : 2 * box ≤ w) (hesc : 17 ≤ a + w - h) :
    anchorRun (a + w - h, w) (a, w) (a, h) = true ∧
      anchorRun (w, a + w - h) (w, a) (h, a) = true := by
  rw [farNearAnchorsSafe, List.all_eq_true] at hf
  have := hf a (List.mem_range.mpr ha)
  rw [List.all_eq_true] at this
  have := this w (List.mem_range.mpr hw)
  rw [List.all_eq_true] at this
  have := this h (List.mem_range.mpr hh)
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hgate, hesc⟩)] at this
  rw [Bool.and_eq_true] at this
  exact this

/-! ## The wrapper -/

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
/-- The rule's forced run on the anchor board and its three anchored
families win every board from the base up. -/
theorem plus_uniform_aux {n : ℕ} (hn : 17 ≤ n)
    (hbase : checkForcedS plusMove box anchorBoard = true)
    (hfar : farAnchorsSafe = true)
    (hexact : exactAnchorsSafe = true)
    (hfarnear : farNearAnchorsSafe = true) :
    WinsWith plusMove n [] := by
  have hab : anchorBoard = 23 := rfl
  have hbox : box = 6 := rfl
  have hop6 : opening ∈ board 6 := opening_box
  have hb6n : ∀ w : Cell, w ∈ board 6 → w ∈ board n := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hb617 : ∀ w : Cell, w ∈ board 6 → w ∈ board 17 := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hb1723 : ∀ w : Cell, w ∈ board 17 → w ∈ board 23 := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hno12 : ∀ w : Cell, w ∉ board 17 → w ∉ board 12 := by
    intro w hw hc
    rw [mem_board] at hc
    exact hw (by rw [mem_board]; (try rw [hab]); omega)
  -- open the base run at the first level
  rw [checkForcedS] at hbase
  obtain ⟨fuel, hfuel⟩ : ∃ f, anchorBoard * anchorBoard + 1 = f + 1 :=
    ⟨anchorBoard * anchorBoard, rfl⟩
  rw [hfuel] at hbase
  simp only [goForcedS, plusMove_nil] at hbase
  split at hbase
  · exact absurd hbase (by simp)
  · rename_i hguard0
    split at hbase
    · rename_i hwin0
      exfalso
      have := hasSquareL_sound (n := anchorBoard) hwin0
      exact not_hasSquare_of_card_lt
        (lt_of_le_of_lt (List.toFinset_card_le _) (by simp [stonesOf])) this
    · split at hbase
      · exact absurd hbase (by simp)
      · split at hbase
        · exact absurd hbase (by simp)
        · split at hbase
          · rename_i hlv0
            split at hbase
            · exact absurd hbase (by simp)
            · rename_i hrep0
              rw [List.all_eq_true] at hbase
              -- the level-one walk of the base run
              have hsub2 : ∀ r1 : Cell, r1 ∈ board anchorBoard → r1 ≠ opening →
                  ∃ fuel',
                    (∀ o2c : Cell, o2c ∈ board anchorBoard → o2c ≠ opening →
                      o2c ≠ r1 → o2c ≠ secondMove r1 →
                      goForcedS plusMove box (squaresList anchorBoard) anchorBoard none
                        fuel' (opening :: r1 :: secondMove r1 :: o2c :: []) = true) := by
                intro r1 hr1b hr1op
                have hbr1 := hbase r1 (by
                  rw [List.mem_filter]
                  refine ⟨mem_allCells.mpr hr1b, ?_⟩
                  simp [List.contains_iff_mem, stonesOf]
                  exact fun he => hr1op (by simp [he]))
                rcases fuel with _ | fuel1
                · simp [goForcedS] at hbr1
                have hcons : (([] : List Cell) ++ [opening]) ++ [r1] = [opening, r1] := by simp
                rw [hcons] at hbr1
                simp only [goForcedS, plusMove_two] at hbr1
                split at hbr1
                · exact absurd hbr1 (by simp)
                · rename_i hguard1
                  split at hbr1
                  · rename_i hwin1
                    exfalso
                    have := hasSquareL_sound (n := anchorBoard) hwin1
                    exact not_hasSquare_of_card_lt (lt_of_le_of_lt
                      (List.toFinset_card_le _) (by simp [stonesOf])) this
                  · split at hbr1
                    · exact absurd hbr1 (by simp)
                    · split at hbr1
                      · exact absurd hbr1 (by simp)
                      · split at hbr1
                        · rename_i hlv1
                          split at hbr1
                          · exact absurd hbr1 (by simp)
                          · rename_i hrep1
                            rw [List.all_eq_true] at hbr1
                            refine ⟨fuel1, ?_⟩
                            intro o2c ho2cb ho2op ho2r1 ho2x2
                            have hbr2 := hbr1 o2c (by
                              rw [List.mem_filter]
                              refine ⟨mem_allCells.mpr ho2cb, ?_⟩
                              simp [List.contains_iff_mem]
                              exact ⟨fun he => ho2op (by simp [he]),
                                fun he => ho2r1 (by simp [he]),
                                fun he => ho2x2 (by simp [he])⟩)
                            have hsh : ([opening, r1] ++ [secondMove r1]) ++ [o2c] =
                                opening :: r1 :: secondMove r1 :: o2c :: [] := by
                              simp
                            rwa [hsh] at hbr2
                        · rename_i hlv1
                          exfalso
                          simp at hlv1
              -- assemble the root step: the rule opens at `opening`
              have e0t : (stonesOf true []).toFinset = (∅ : Finset Cell) := by simp [stonesOf]
              have e0f : (stonesOf false []).toFinset = (∅ : Finset Cell) := by simp [stonesOf]
              refine WinsWith.step opening plusMove_nil ?_ ?_ ?_ ?_ <;> rw [e0t, e0f]
              · exact mem_empties.mpr ⟨hb6n _ hop6, by simp, by simp⟩
              · exact empties_nonempty hn (by simp)
              · exact fun r _ => not_hasSquare_of_card_lt (by
                  have := Finset.card_insert_le r (∅ : Finset Cell)
                  simp at this ⊢)
              intro o1r ho1E
              obtain ⟨ho1n, ho1p1, -⟩ := mem_empties.mp ho1E
              have ho1op : o1r ≠ opening := by
                intro he
                exact ho1p1 (he ▸ Finset.mem_insert_self _ _)
              -- the real second move, and the base cell it is read from
              obtain ⟨o1b, ho1b23, ho1bop, hslot1, hx2eq, ho1b17, ho1bcases⟩ :
                  ∃ o1b : Cell, o1b ∈ board anchorBoard ∧ o1b ≠ opening ∧
                    SlotOk anchorBoard n o1b o1r ∧ secondMove o1b = secondMove o1r ∧
                    (o1r ∈ board 17 → o1b = o1r) ∧ (o1r ∉ board 17 → o1b = (22, 22)) := by
                by_cases ho117 : o1r ∈ board 17
                · exact ⟨o1r, hb1723 _ ho117, ho1op,
                    Or.inl ⟨rfl, ho117, hb1723 _ ho117⟩, rfl, fun _ => rfl,
                    fun h => absurd ho117 h⟩
                · refine ⟨(22, 22), by rw [mem_board, hab]; omega, by decide,
                    Or.inr ⟨by rw [mem_board, hab]; omega, by rw [mem_board]; omega,
                      ho1n, hno12 _ ho117, ho117⟩, ?_, fun h => absurd h ho117, fun _ => rfl⟩
                  rw [secondMove_far (by rw [mem_board]; omega),
                    secondMove_far (fun h6 => ho117 (hb617 _ h6))]
              set x2 := secondMove o1r with hx2def
              have hx2box : x2 ∈ board 6 := secondMove_box o1r
              have hx2op : x2 ≠ opening := secondMove_ne_opening o1r
              have hx2o1 : x2 ≠ o1r := secondMove_ne_self o1r
              obtain ⟨fuel1, hlvl2⟩ := hsub2 o1b ho1b23 ho1bop
              rw [hx2eq] at hlvl2
              -- the second step: the rule answers with the second move
              have hl2 : (([] : List Cell) ++ [opening]) ++ [o1r] = [opening, o1r] := rfl
              rw [hl2]
              have e1t : (stonesOf true [opening, o1r]).toFinset =
                  insert opening (∅ : Finset Cell) := by simp [stonesOf]
              have e1f : (stonesOf false [opening, o1r]).toFinset =
                  insert o1r (∅ : Finset Cell) := by simp [stonesOf]
              refine WinsWith.step x2 (plusMove_two o1r) ?_ ?_ ?_ ?_ <;> rw [e1t, e1f]
              · exact mem_empties.mpr ⟨hb6n _ hx2box, by simp [hx2op], by simp [hx2o1]⟩
              · exact empties_nonempty hn (card_union_three _ _ _)
              · intro r _
                refine not_hasSquare_of_card_lt ?_
                have h1 := Finset.card_insert_le r (insert o1r (∅ : Finset Cell))
                have h2 := Finset.card_insert_le o1r (∅ : Finset Cell)
                rw [Finset.card_empty] at h2
                omega
              intro o2r ho2E
              obtain ⟨ho2n, ho2p1, ho2p2⟩ := mem_empties.mp ho2E
              have ho2op : o2r ≠ opening := by
                intro he
                exact ho2p1 (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              have ho2x2 : o2r ≠ x2 := by
                intro he
                exact ho2p1 (he ▸ Finset.mem_insert_self _ _)
              have ho2o1 : o2r ≠ o1r := by
                intro he
                exact ho2p2 (he ▸ Finset.mem_insert_self _ _)
              have hl4 : ([opening, o1r] ++ [x2]) ++ [o2r] =
                  opening :: o1r :: x2 :: o2r :: [] := rfl
              rw [hl4]
              -- the rule takes its wins along every real history from here
              have htake : TakesWinsOn plusMove 6 n [opening, o1r, x2, o2r] :=
                (plusMove_takesWins (by omega)).extend _
              -- the base run's second-level subtree for a base pair
              have hbranch : ∀ o2b : Cell, o2b ∈ board anchorBoard → o2b ≠ opening →
                  o2b ≠ o1b → o2b ≠ x2 →
                  goForcedS plusMove box (squaresList anchorBoard) anchorBoard none fuel1
                    (opening :: o1b :: x2 :: o2b :: []) = true :=
                fun o2b hb hop ho1 hx2 => hlvl2 o2b hb hop ho1 hx2
              -- shared facts about a farm pair
              have hfarm : ∀ hc : Cell, farmKey 6 o1r o2r = some (.farm hc) →
                  hc ∈ board 17 ∧ hc ∉ ([o1r, o2r] : List Cell) ∧
                  (o1r ∉ board 17 ∨ o2r ∉ board 17 →
                    PairMode (some hc) o1r o2r ([o1r, o2r] : List Cell)) := by
                intro hc hfk
                have hhotbox := farmKey_hot_box hfk
                obtain ⟨hg1, hg2, -⟩ := farmKey_spec hfk
                refine ⟨by rw [mem_board]; omega, ?_, fun _ => ⟨hfk, ?_⟩⟩
                · intro hmem
                  rw [List.mem_cons, List.mem_cons] at hmem
                  rcases hmem with he | he | he
                  · have h1 : hc.1 = o1r.1 := congrArg Prod.fst he
                    have h2 : hc.2 = o1r.2 := congrArg Prod.snd he
                    omega
                  · have h1 : hc.1 = o2r.1 := congrArg Prod.fst he
                    have h2 : hc.2 = o2r.2 := congrArg Prod.snd he
                    omega
                  · simp at he
                · intro hmem
                  rw [List.mem_cons, List.mem_cons] at hmem
                  rcases hmem with he | he | he
                  · have h1 : hc.1 = o1r.1 := congrArg Prod.fst he
                    have h2 : hc.2 = o1r.2 := congrArg Prod.snd he
                    omega
                  · have h1 : hc.1 = o2r.1 := congrArg Prod.fst he
                    have h2 : hc.2 = o2r.2 := congrArg Prod.snd he
                    omega
                  · simp at he
              by_cases ho117 : o1r ∈ board 17
              · -- a first reply on the base board, read verbatim
                have ho1b_eq := ho1b17 ho117
                subst o1b
                by_cases ho217 : o2r ∈ board 17
                · -- both replies on the base board: the base branch
                  exact simulate plusMove (B := anchorBoard) none hn (by decide)
                    hop6 hx2box hslot1 (Or.inl ⟨rfl, ho217, hb1723 _ ho217⟩)
                    (plusMove_agree (Or.inl rfl) (Or.inl rfl) rfl rfl _ _) htake
                    fuel1 [] (by simp) (by simp)
                    (hbranch o2r (hb1723 _ ho217) ho2op ho2o1 ho2x2)
                    not_hasSquare_pair not_hasSquare_pair
                    (fun hoff => hoff.elim (fun h => absurd ho117 h) (fun h => absurd ho217 h))
                · rcases hfk : farmKey 6 o1r o2r with _ | k
                  · -- a keyless far second reply: a stand-in branch
                    have hro1 : ((22, 21) : Cell) ≠ o1r := by
                      intro he
                      rw [mem_board, ← he] at ho117
                      omega
                    have hrx2 : ((22, 21) : Cell) ≠ x2 := by
                      intro he
                      rw [mem_board, ← he] at hx2box
                      omega
                    exact simulate plusMove (B := anchorBoard) none hn (by decide)
                      hop6 hx2box hslot1
                      (Or.inr ⟨by rw [mem_board, hab]; omega, by rw [mem_board]; omega,
                        ho2n, hno12 _ ho217, ho217⟩)
                      (plusMove_agree (Or.inl rfl) (slotSame_far (by rw [mem_board]; decide) ho217)
                        (by
                          show farmKey 6 _ _ = farmKey 6 _ _
                          rw [hfk]; exact farmKey_standin_snd ho117) rfl _ _)
                      htake
                      fuel1 [] (by simp) (by simp)
                      (hbranch (22, 21) (by rw [mem_board, hab]; omega) (by decide) hro1 hrx2)
                      not_hasSquare_pair not_hasSquare_pair (fun _ => hfk)
                  · -- a farm pair with the near member first: its exact anchor
                    obtain ⟨hc, rfl⟩ := farmKey_farm hfk
                    have hhotbox := farmKey_hot_box hfk
                    obtain ⟨hhc17, hcne, hmode⟩ := hfarm hc hfk
                    rcases farm_near_fst hfk ho117 ho217 with hform | hform
                    · obtain ⟨ha6, hw12, hw17, hh1, hh2, hh2le, hesc⟩ := hform
                      have hrun' := (exactAnchors_run hexact
                        (a := o1r.1) (w := o1r.2) (h := hc.2)
                        (by (try rw [hbox]); omega) (by omega) (by (try rw [hbox]); omega)
                        (by (try rw [hbox]); omega) (by omega)).1
                      rw [show ((o1r.1, o1r.2) : Cell) = o1r from rfl,
                        show ((o1r.1, hc.2) : Cell) = hc by rw [← hh1]] at hrun'
                      obtain ⟨hkeyb, hrun⟩ := anchorRun_spec hrun'
                      exact simulate plusMove (B := anchorBoard) (some hc) hn (by decide)
                        hop6 hx2box hslot1
                        (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                          by rw [mem_board]; dsimp only; omega,
                          ho2n, hno12 _ ho217, ho217⟩)
                        (plusMove_agree (Or.inl rfl)
                          (slotSame_far (by rw [mem_board]; dsimp only; omega) ho217)
                          (hkeyb.trans hfk.symm) rfl _ _) htake
                        (anchorBoard * anchorBoard + 1) [] (by simp) (by simp)
                        hrun not_hasSquare_pair not_hasSquare_pair hmode
                    · obtain ⟨ha6, hw12, hw17, hh2, hh1, hh1le, hesc⟩ := hform
                      have hrun' := (exactAnchors_run hexact
                        (a := o1r.2) (w := o1r.1) (h := hc.1)
                        (by (try rw [hbox]); omega) (by omega) (by (try rw [hbox]); omega)
                        (by (try rw [hbox]); omega) (by omega)).2
                      rw [show ((o1r.1, o1r.2) : Cell) = o1r from rfl,
                        show ((hc.1, o1r.2) : Cell) = hc by rw [← hh2]] at hrun'
                      obtain ⟨hkeyb, hrun⟩ := anchorRun_spec hrun'
                      exact simulate plusMove (B := anchorBoard) (some hc) hn (by decide)
                        hop6 hx2box hslot1
                        (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                          by rw [mem_board]; dsimp only; omega,
                          ho2n, hno12 _ ho217, ho217⟩)
                        (plusMove_agree (Or.inl rfl)
                          (slotSame_far (by rw [mem_board]; dsimp only; omega) ho217)
                          (hkeyb.trans hfk.symm) rfl _ _) htake
                        (anchorBoard * anchorBoard + 1) [] (by simp) (by simp)
                        hrun not_hasSquare_pair not_hasSquare_pair hmode
              · -- a far first reply: the stand-in `(22, 22)` and the default second move
                have ho112 : o1r ∉ board 17 := ho117
                have ho1b22 : o1b = (22, 22) := ho1bcases ho117
                have hx2d : x2 = (3, 2) := secondMove_far (fun h6 => ho117 (hb617 _ h6))
                rcases hfk : farmKey 6 o1r o2r with _ | k
                · -- keyless: a stand-in for the first reply, verbatim or stand-in second
                  by_cases ho217 : o2r ∈ board 17
                  · have ho2o1b : o2r ≠ o1b := by
                      intro he
                      rw [he, ho1b22, mem_board] at ho217
                      omega
                    exact simulate plusMove (B := anchorBoard) none hn (by decide)
                      hop6 hx2box hslot1 (Or.inl ⟨rfl, ho217, hb1723 _ ho217⟩)
                      (plusMove_agree
                        (slotSame_far (by rw [ho1b22, mem_board]; decide) ho117) (Or.inl rfl)
                        (by
                          show farmKey 6 _ _ = farmKey 6 _ _
                          rw [hfk, ho1b22]; exact farmKey_standin_fst ho217)
                        hx2eq _ _) htake
                      fuel1 [] (by simp) (by simp)
                      (hbranch o2r (hb1723 _ ho217) ho2op ho2o1b ho2x2)
                      not_hasSquare_pair not_hasSquare_pair (fun _ => hfk)
                  · have hro1 : ((22, 21) : Cell) ≠ o1b := by rw [ho1b22]; decide
                    have hrx2 : ((22, 21) : Cell) ≠ x2 := by
                      intro he
                      rw [mem_board, ← he] at hx2box
                      omega
                    exact simulate plusMove (B := anchorBoard) none hn (by decide)
                      hop6 hx2box hslot1
                      (Or.inr ⟨by rw [mem_board, hab]; omega, by rw [mem_board]; omega,
                        ho2n, hno12 _ ho217, ho217⟩)
                      (plusMove_agree (slotSame_far (by rw [ho1b22, mem_board]; decide) ho117)
                        (slotSame_far (by rw [mem_board]; decide) ho217)
                        (by
                          show farmKey 6 _ _ = farmKey 6 _ _
                          rw [hfk, ho1b22]; exact farmKey_standins)
                        hx2eq _ _) htake
                      fuel1 [] (by simp) (by simp)
                      (hbranch (22, 21) (by rw [mem_board, hab]; omega) (by decide) hro1 hrx2)
                      not_hasSquare_pair not_hasSquare_pair (fun _ => hfk)
                · -- a farm pair with a far first member
                  obtain ⟨hc, rfl⟩ := farmKey_farm hfk
                  have hhotbox := farmKey_hot_box hfk
                  obtain ⟨hhc17, hcne, hmode⟩ := hfarm hc hfk
                  have hslot1' : SlotOk anchorBoard n o1b o1r := hslot1
                  by_cases ho217 : o2r ∈ board 17
                  · -- near second member: its anchor plays it second
                    rcases farm_near_snd hfk ho117 ho217 with hform | hform
                    · obtain ⟨ha6, hw12, hw17, hh1, hh2, hh2le, hesc⟩ := hform
                      have hrun' := (farNearAnchors_run hfarnear
                        (a := o2r.1) (w := o2r.2) (h := hc.2)
                        (by (try rw [hbox]); omega) (by omega) (by (try rw [hbox]); omega)
                        (by (try rw [hbox]); omega) (by omega)).1
                      rw [show ((o2r.1, o2r.2) : Cell) = o2r from rfl,
                        show ((o2r.1, hc.2) : Cell) = hc by rw [← hh1]] at hrun'
                      obtain ⟨hkeyb, hrun⟩ := anchorRun_spec hrun'
                      rw [secondMove_far (by rw [mem_board]; dsimp only; omega), ← hx2d] at hrun
                      exact simulate plusMove (B := anchorBoard) (some hc) hn (by decide)
                        hop6 hx2box
                        (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                          by rw [mem_board]; dsimp only; omega,
                          ho1n, hno12 _ ho117, ho117⟩)
                        (Or.inl ⟨rfl, ho217, hb1723 _ ho217⟩)
                        (plusMove_agree
                          (slotSame_far (by rw [mem_board]; dsimp only; omega) ho117) (Or.inl rfl)
                          (hkeyb.trans hfk.symm)
                          (by
                            rw [secondMove_far (by rw [mem_board]; dsimp only; omega)]
                            exact hx2d.symm) _ _) htake
                        (anchorBoard * anchorBoard + 1) [] (by simp) (by simp)
                        hrun not_hasSquare_pair not_hasSquare_pair hmode
                    · obtain ⟨ha6, hw12, hw17, hh2, hh1, hh1le, hesc⟩ := hform
                      have hrun' := (farNearAnchors_run hfarnear
                        (a := o2r.2) (w := o2r.1) (h := hc.1)
                        (by (try rw [hbox]); omega) (by omega) (by (try rw [hbox]); omega)
                        (by (try rw [hbox]); omega) (by omega)).2
                      rw [show ((o2r.1, o2r.2) : Cell) = o2r from rfl,
                        show ((hc.1, o2r.2) : Cell) = hc by rw [← hh2]] at hrun'
                      obtain ⟨hkeyb, hrun⟩ := anchorRun_spec hrun'
                      rw [secondMove_far (by rw [mem_board]; dsimp only; omega), ← hx2d] at hrun
                      exact simulate plusMove (B := anchorBoard) (some hc) hn (by decide)
                        hop6 hx2box
                        (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                          by rw [mem_board]; dsimp only; omega,
                          ho1n, hno12 _ ho117, ho117⟩)
                        (Or.inl ⟨rfl, ho217, hb1723 _ ho217⟩)
                        (plusMove_agree
                          (slotSame_far (by rw [mem_board]; dsimp only; omega) ho117) (Or.inl rfl)
                          (hkeyb.trans hfk.symm)
                          (by
                            rw [secondMove_far (by rw [mem_board]; dsimp only; omega)]
                            exact hx2d.symm) _ _) htake
                        (anchorBoard * anchorBoard + 1) [] (by simp) (by simp)
                        hrun not_hasSquare_pair not_hasSquare_pair hmode
                  · -- both members far: the far anchor
                    have hrun' := farAnchors_run hfar (h1 := hc.1) (h2 := hc.2)
                      (by (try rw [hbox]); omega) (by (try rw [hbox]); omega)
                    rw [show ((hc.1, hc.2) : Cell) = hc from rfl] at hrun'
                    obtain ⟨hkeyb, hrun⟩ := anchorRun_spec hrun'
                    rw [secondMove_far (by rw [mem_board]; dsimp only; omega), ← hx2d] at hrun
                    exact simulate plusMove (B := anchorBoard) (some hc) hn (by decide)
                      hop6 hx2box
                      (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                        by rw [mem_board]; dsimp only; omega,
                        ho1n, hno12 _ ho117, ho117⟩)
                      (Or.inr ⟨by rw [mem_board]; (try rw [hab]); dsimp only; omega,
                        by rw [mem_board]; dsimp only; omega,
                        ho2n, hno12 _ ho217, ho217⟩)
                      (plusMove_agree (slotSame_far (by rw [mem_board]; dsimp only; omega) ho117)
                        (slotSame_far (by rw [mem_board]; dsimp only; omega) ho217)
                        (hkeyb.trans hfk.symm)
                        (by
                          rw [secondMove_far (by rw [mem_board]; dsimp only; omega)]
                          exact hx2d.symm) _ _) htake
                      (anchorBoard * anchorBoard + 1) [] (by simp) (by simp)
                      hrun not_hasSquare_pair not_hasSquare_pair hmode
          · rename_i hlv0
            exfalso
            simp at hlv0

end SquareAchievement.Plus
