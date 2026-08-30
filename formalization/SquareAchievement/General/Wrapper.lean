import SquareAchievement.Compute.ExactFarm
import SquareAchievement.General.Simulation

/-!
# The wrapper

`check_sound_uniform_aux` walks the two free levels of the base run
and dispatches every real reply pair to `simulate`: both replies on
the base board replay the base branch verbatim; a far pair replays
the default-class anchor; a pair with one near box-aligned member
replays its exact-cell anchor. The strategy's first two moves are
the opening and the x2 entry for the first reply, which is also what
every anchor plays, because a far first reply and every anchor stone
resolve to the default x2 entry.
-/

namespace SquareAchievement

/-- The x2 map neither returns the opening nor keys cells beyond the
generation board, so the second move after any reply is the reply's
x2 lookup, and all far first replies share the default entry. -/
def x2Sane (t : Table) : Bool :=
  t.x2.all fun e =>
    e.2 ≠ t.opening &&
      (match e.1 with
       | .cell c => c.1 < 15 && c.2 < 15
       | _ => true)

/-- Fewer than four stones hold no square. -/
theorem no_square_card {S : Finset Cell} (h : S.card < 4) :
    ¬ HasSquare S := by
  rintro ⟨a, b, s, hs, hsub⟩
  have h1 : ((a, b) : Cell) ≠ (a, b + s) := by
    simp [Prod.ext_iff]; omega
  have h2 : ((a, b) : Cell) ≠ (a + s, b) := by
    simp [Prod.ext_iff]; omega
  have h3 : ((a, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have h4 : ((a, b + s) : Cell) ≠ (a + s, b) := by
    simp [Prod.ext_iff]; omega
  have h5 : ((a, b + s) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have h6 : ((a + s, b) : Cell) ≠ (a + s, b + s) := by
    simp [Prod.ext_iff]; omega
  have hcard : (corners a b s).card = 4 := by
    rw [corners]
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]),
      Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

/-- With at most two stones, no square scan finds a one-away
square. -/
theorem minThreat_short {k : ℕ} {mine occ : List Cell}
    (hm : mine.length ≤ 2) :
    minThreat (squaresList k) mine occ = none := by
  unfold minThreat
  have hgen : ∀ (sqs : List (List Cell)),
      (∀ sq ∈ sqs, sq ∈ squaresList k) →
      sqs.foldl (fun best sq =>
        match sq.filter (fun x => !mine.contains x) with
        | [m] =>
          if occ.contains m then best
          else
            match best with
            | none => some m
            | some b => if cellLt m b then some m else some b
        | _ => best) none = none := by
    intro sqs
    induction sqs with
    | nil => intro _; rfl
    | cons sq rest ih =>
      intro hall
      have hsq := hall sq (List.mem_cons_self ..)
      have hnd := squaresList_nodup hsq
      have hlen : sq.length = 4 := by
        obtain ⟨r, c, s, -, -, -, rfl⟩ := mem_squaresList.mp hsq
        rfl
      have hfil : 2 ≤ (sq.filter (fun x => !mine.contains x)).length := by
        have hsub : sq.toFinset ⊆
            (sq.filter (fun x => !mine.contains x)).toFinset ∪
              mine.toFinset := by
          intro x hx
          rw [List.mem_toFinset] at hx
          rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
          by_cases hm : x ∈ mine
          · exact Or.inr hm
          · exact Or.inl (List.mem_filter.mpr ⟨hx, by simpa using hm⟩)
        have h4 : sq.toFinset.card = 4 := by
          rw [List.toFinset_card_of_nodup hnd, hlen]
        have hle := Finset.card_le_card hsub
        have hu := Finset.card_union_le
          (sq.filter (fun x => !mine.contains x)).toFinset mine.toFinset
        have hf1 := (sq.filter (fun x => !mine.contains x)).toFinset_card_le
        have hf2 := mine.toFinset_card_le
        omega
      have hstep : (match sq.filter (fun x => !mine.contains x) with
          | [m] =>
            if occ.contains m then (none : Option Cell)
            else
              match (none : Option Cell) with
              | none => some m
              | some b => if cellLt m b then some m else some b
          | _ => none) = none := by
        rcases hcase : sq.filter (fun x => !mine.contains x) with
          _ | ⟨u, _ | ⟨v, w⟩⟩
        · rfl
        · rw [hcase] at hfil
          simp at hfil
        · rfl
      rw [List.foldl_cons]
      rw [hstep]
      exact ih fun s hs => hall s (List.mem_cons_of_mem _ hs)
  exact hgen _ (fun sq hsq => hsq)

/-- The first move of the strategy is the opening. -/
theorem strategyMove_nil {t : Table} {k : ℕ} :
    strategyMove t (squaresList k) [] = some t.opening := by
  unfold strategyMove
  dsimp only
  rw [minThreat_short (by simp [stonesOf]),
    minThreat_short (by simp [stonesOf])]
  rfl

/-- A successful raw lookup returns a stored value. -/
theorem lookup_raw_val {α : Type _} {entries : List (Key × α)}
    {k : Key} {v : α} (h : entries.lookup k = some v) :
    ∃ key, (key, v) ∈ entries := by
  induction entries with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨ek, ev⟩ := e
    rw [List.lookup_cons] at h
    split at h
    · exact ⟨ek, by rw [← Option.some_inj.mp h]; exact List.mem_cons_self ..⟩
    · obtain ⟨key, hm⟩ := ih h
      exact ⟨key, List.mem_cons_of_mem _ hm⟩

/-- The lookup of the x2 map returns one of its values. -/
theorem lookup_val {α : Type _} {box : ℕ} {entries : List (Key × α)}
    {c : Cell} {v : α} (h : lookup box entries c = some v) :
    ∃ key, (key, v) ∈ entries := by
  unfold lookup at h
  split at h
  · rename_i heq
    exact lookup_raw_val (heq.trans (by rw [h]))
  · split at h
    · rename_i heq
      exact lookup_raw_val (heq.trans (by rw [h]))
    · exact lookup_raw_val h

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

/-- Extract one anchored run from `farFarmSafe`. -/
theorem farFarmSafe_run {t : Table} (hf : farFarmSafe t = true)
    {h1 h2 : ℕ} (hh1 : h1 < t.box) (hh2 : h2 < t.box) :
    anchorRun t (h1 + 17 - h2, 17) (h1 + 17 - h2, h2) (h1, h2) = true := by
  rw [farFarmSafe, List.all_eq_true] at hf
  have := hf h1 (List.mem_range.mpr hh1)
  rw [List.all_eq_true] at this
  exact this h2 (List.mem_range.mpr hh2)

/-- Extract one anchored run from `exactFarmSafe`. -/
theorem exactFarmSafe_run {t : Table} (hf : exactFarmSafe t = true)
    {a w h : ℕ} (ha : a < t.box) (hw : w < 17) (hh : h < t.box)
    (hgate : 2 * t.box ≤ w) (hesc : 17 ≤ a + w - h) :
    anchorRun t (a, w) (a + w - h, w) (a, h) = true ∧
      anchorRun t (w, a) (w, a + w - h) (h, a) = true := by
  rw [exactFarmSafe, List.all_eq_true] at hf
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

/-- Extract one anchored run from `farNearFarmSafe`. -/
theorem farNearFarmSafe_run {t : Table} (hf : farNearFarmSafe t = true)
    {a w h : ℕ} (ha : a < t.box) (hw : w < 17) (hh : h < t.box)
    (hgate : 2 * t.box ≤ w) (hesc : 17 ≤ a + w - h) :
    anchorRun t (a + w - h, w) (a, w) (a, h) = true ∧
      anchorRun t (w, a + w - h) (w, a) (h, a) = true := by
  rw [farNearFarmSafe, List.all_eq_true] at hf
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

/-- What one anchored run certifies. -/
theorem anchorRun_spec {t : Table} {o1 o2 hot : Cell}
    (h : anchorRun t o1 o2 hot = true) :
    ∃ x2v, lookup t.box t.x2 o1 = some x2v ∧
      goForced t (squaresList anchorBoard) anchorBoard (some hot)
        (anchorBoard * anchorBoard + 1) [t.opening, o1, x2v, o2] = true := by
  rw [anchorRun, Bool.and_eq_true] at h
  obtain ⟨-, hrun⟩ := h
  rcases hl : lookup t.box t.x2 o1 with _ | v
  · rw [hl] at hrun
    simp at hrun
  · rw [hl] at hrun
    exact ⟨v, rfl, hrun⟩

/-- A cell beyond the generation board with no box coordinate
resolves to the default x2 entry. -/
theorem lookup_x2_far {t : Table} (hbox : t.box = 6)
    (hsane : x2Sane t = true) {c : Cell}
    (hfar : 15 ≤ c.1 ∨ 15 ≤ c.2) (h1 : 6 ≤ c.1) (h2 : 6 ≤ c.2) :
    lookup t.box t.x2 c = t.x2.lookup Key.dflt := by
  have hmiss : t.x2.lookup (Key.cell c) = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    rw [x2Sane, List.all_eq_true] at hsane
    have hs := hsane _ hp
    rw [Bool.and_eq_true] at hs
    obtain ⟨-, hk⟩ := hs
    obtain ⟨key, v⟩ := p
    match key with
    | .row _ | .col _ | .farm _ | .dflt => rfl
    | .cell c' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      show (!(c == c')) = true
      rw [Bool.not_eq_eq_eq_not]
      simp only [Bool.not_true]
      rw [beq_eq_false_iff_ne]
      intro he
      have h1 : c.1 = c'.1 := congrArg Prod.fst he
      have h2 : c.2 = c'.2 := congrArg Prod.snd he
      omega
  have hcls : classOf t.box c = Key.dflt := by
    rw [hbox]
    unfold classOf
    rw [if_neg, if_neg]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      omega
  unfold lookup
  rw [hmiss, hcls]
  rcases hd : t.x2.lookup Key.dflt with _ | v <;> simp

/-- The opening lies in the box. -/
theorem planConfined_opening {t : Table} (h : planConfined t = true) :
    t.opening ∈ board t.box := by
  rw [planConfined, Bool.and_eq_true, Bool.and_eq_true] at h
  exact onBoard_iff.mp h.1.1

/-- Every x2 value lies in the box. -/
theorem planConfined_x2 {t : Table} (h : planConfined t = true)
    {c v : Cell} (hl : lookup t.box t.x2 c = some v) :
    v ∈ board t.box := by
  obtain ⟨key, hmem⟩ := lookup_val hl
  rw [planConfined, Bool.and_eq_true, Bool.and_eq_true] at h
  have := h.1.2
  rw [List.all_eq_true] at this
  exact onBoard_iff.mp (this _ hmem)

/-- The second move of the strategy is the first reply's x2 lookup. -/
theorem strategyMove_two {t : Table} {k : ℕ} {o1 : Cell}
    (hsane : x2Sane t = true) :
    strategyMove t (squaresList k) [t.opening, o1] =
      lookup t.box t.x2 o1 := by
  unfold strategyMove
  dsimp only
  rw [minThreat_short (by simp [stonesOf]),
    minThreat_short (by simp [stonesOf])]
  rcases hl : lookup t.box t.x2 o1 with _ | v
  · simp [stonesOf, hl]
  · obtain ⟨key, hmem⟩ := lookup_val hl
    rw [x2Sane, List.all_eq_true] at hsane
    have := hsane _ hmem
    rw [Bool.and_eq_true] at this
    have hne : v ≠ t.opening := by simpa using this.1
    simp [stonesOf, hl, hne]

/-- Positions with at most three stones always have an empty cell. -/
theorem empties_nonempty {n : ℕ} (hn : 17 ≤ n) {p1 p2 : Finset Cell}
    (h : (p1 ∪ p2).card ≤ 3) : (empties n p1 p2).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hmem : ∀ w : Cell, w ∈ board n → w ∈ p1 ∪ p2 := by
    intro w hw
    by_contra hwn
    rw [Finset.mem_union] at hwn
    push_neg at hwn
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

set_option maxHeartbeats 3200000 in
/-- The wrapper: one forced base run and the three anchored farm
certificates win every board from the base up. -/
theorem check_sound_uniform_aux {t : Table} {n : ℕ} (hn : 17 ≤ n)
    (hbox : t.box = 6)
    (hconf : planConfined t = true)
    (hforce : checkForced t 17 = true)
    (hfar : farFarmSafe t = true)
    (hexact : exactFarmSafe t = true)
    (hfarnear : farNearFarmSafe t = true)
    (hsane : x2Sane t = true) :
    P1CanWin n ∅ ∅ := by
  have hop6 : t.opening ∈ board 6 := hbox ▸ planConfined_opening hconf
  have hb6n : ∀ w : Cell, w ∈ board 6 → w ∈ board n := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hb617 : ∀ w : Cell, w ∈ board 6 → w ∈ board 17 := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  -- open the base run at the first level
  rw [checkForced] at hforce
  obtain ⟨fuel, hfuel⟩ : ∃ f, 17 * 17 + 1 = f + 1 := ⟨17 * 17, rfl⟩
  rw [hfuel] at hforce
  simp only [goForced, strategyMove_nil] at hforce
  split at hforce
  · exact absurd hforce (by simp)
  · rename_i hguard0
    split at hforce
    · rename_i hwin0
      exfalso
      have := hasSquareL_sound (n := 17) hwin0
      exact no_square_card
        (lt_of_le_of_lt (List.toFinset_card_le _) (by simp [stonesOf])) this
    · split at hforce
      · exact absurd hforce (by simp)
      · split at hforce
        · exact absurd hforce (by simp)
        · split at hforce
          · rename_i hlv0
            split at hforce
            · exact absurd hforce (by simp)
            · rename_i hrep0
              rw [List.all_eq_true] at hforce
              -- the level-one walk, shared by every first-reply shape
              have hsub2 : ∀ r1 : Cell, r1 ∈ board 17 → r1 ≠ t.opening →
                  ∃ x2v fuel', lookup t.box t.x2 r1 = some x2v ∧
                    x2v ≠ r1 ∧
                    (∀ o2c : Cell, o2c ∈ board 17 → o2c ≠ t.opening →
                      o2c ≠ r1 → o2c ≠ x2v →
                      goForced t (squaresList 17) 17 none fuel'
                        (t.opening :: r1 :: x2v :: o2c :: []) = true) := by
                intro r1 hr117 hr1op
                have hbr1 := hforce r1 (by
                  rw [List.mem_filter]
                  refine ⟨mem_allCells.mpr hr117, ?_⟩
                  simp [List.contains_iff_mem, stonesOf]
                  exact fun he => hr1op (by simp [he]))
                rcases fuel with _ | fuel1
                · simp [goForced] at hbr1
                have hcons : (([] : List Cell) ++ [t.opening]) ++ [r1] =
                    [t.opening, r1] := by simp
                rw [hcons] at hbr1
                simp only [goForced, strategyMove_two hsane] at hbr1
                rcases hx2l : lookup t.box t.x2 r1 with _ | x2v
                · simp only [hx2l] at hbr1
                  exact absurd hbr1 (by simp)
                · simp only [hx2l] at hbr1
                  split at hbr1
                  · exact absurd hbr1 (by simp)
                  · rename_i hguard1
                    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true',
                      Bool.not_eq_true, List.contains_iff_mem] at hguard1
                    obtain ⟨⟨-, hx2p1⟩, hx2p2⟩ := hguard1
                    have hx2r1 : x2v ≠ r1 := by
                      intro he
                      simp [stonesOf, he] at hx2p2
                    split at hbr1
                    · rename_i hwin1
                      exfalso
                      have := hasSquareL_sound (n := 17) hwin1
                      exact no_square_card (lt_of_le_of_lt
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
                              refine ⟨x2v, fuel1, rfl, hx2r1, ?_⟩
                              intro o2c ho2c17 ho2op ho2r1 ho2x2
                              have hbr2 := hbr1 o2c (by
                                rw [List.mem_filter]
                                refine ⟨mem_allCells.mpr ho2c17, ?_⟩
                                simp [List.contains_iff_mem]
                                exact ⟨fun he => ho2op (by simp [he]),
                                  fun he => ho2r1 (by simp [he]),
                                  fun he => ho2x2 (by simp [he])⟩)
                              have hsh : ([t.opening, r1] ++ [x2v]) ++ [o2c] =
                                  t.opening :: r1 :: x2v :: o2c :: [] := by
                                simp
                              rwa [hsh] at hbr2
                          · rename_i hlv1
                            exfalso
                            simp at hlv1
              -- assemble the root step
              refine P1CanWin.step t.opening
                (mem_empties.mpr ⟨hb6n _ hop6, by simp, by simp⟩)
                (empties_nonempty hn (by simp))
                (fun r _ => no_square_card (by
                  have := Finset.card_insert_le r (∅ : Finset Cell)
                  simp at this ⊢))
                ?_
              intro o1r ho1E
              obtain ⟨ho1n, ho1p1, -⟩ := mem_empties.mp ho1E
              have ho1op : o1r ≠ t.opening := by
                intro he
                exact ho1p1 (he ▸ Finset.mem_insert_self _ _)
              sorry
          · rename_i hlv0
            exfalso
            simp at hlv0

end SquareAchievement
