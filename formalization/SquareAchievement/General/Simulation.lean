import SquareAchievement.Compute.ForcedSound
import SquareAchievement.General.Invariance
import SquareAchievement.General.Coverage

/-!
# The simulation argument

Support for `check_sound_uniform`. The theorem replays the forced run
at the base board `17` on an arbitrary board `n ≥ 17`:

* replies inside the base board follow the checked tree verbatim;
* a reply that blocks no standing threat loses to the threat at once,
  so the opponent's lasting stones are the two replies and the
  blocks, and the blocks stay in the box by the checked guards;
* the two replies, when they use cells beyond the base board, are
  abstracted: through class representatives when the pair farms
  nothing, and through the anchored farm subtree when it does.

The safety obligation reduces to squares with one block corner in the
box, the two replies, and the completing move. Such a square either
fits inside the base board, where the run checked it, or has both
replies at the far threshold, where `farmKey` names the block corner
and the farm entry keeps the opponent off it; `17 = box + far - 1` is
the least base making that dichotomy exhaustive.
-/

namespace SquareAchievement

/-! ## Containment: three near corners confine the square -/

/-- Three distinct corners inside `board B` confine the whole square
to `board B`: any three corners cover the far row and the far
column. -/
theorem three_corners_confine {B r c s : ℕ} {x y z : Cell}
    (hx : x ∈ corners r c s) (hy : y ∈ corners r c s)
    (hz : z ∈ corners r c s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxB : x ∈ board B) (hyB : y ∈ board B) (hzB : z ∈ board B) :
    r + s < B ∧ c + s < B := by
  rw [mem_corners] at hx hy hz
  rw [mem_board] at hxB hyB hzB
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl <;>
    simp_all <;> omega

/-- A listed square with three of its four (distinct) corners in a
smaller board's cells is listed on the smaller board. Stated through
the one-missing filter: everything the filter drops is a `mine`
stone. -/
theorem square_filter_confine {n B : ℕ} (hB : 0 < B) (hBn : B ≤ n)
    {mine : List Cell} (hmine : ∀ x ∈ mine, x ∈ board B)
    {sq : List Cell} (hsq : sq ∈ squaresList n) {z : Cell}
    (hfil : sq.filter (fun x => !mine.contains x) = [z]) :
    sq ∈ squaresList B := by
  obtain ⟨r, c, s, hs, hr, hc, rfl⟩ := mem_squaresList.mp hsq
  -- a corner other than z sits in `mine`, hence in the board
  have hin : ∀ x ∈ ([(r, c), (r, c + s), (r + s, c), (r + s, c + s)] :
      List Cell), x ≠ z → x ∈ board B := by
    intro x hxsq hxz
    by_cases hxm : x ∈ mine
    · exact hmine x hxm
    · have : x ∈ ([(r, c), (r, c + s), (r + s, c), (r + s, c + s)] :
          List Cell).filter (fun x => !mine.contains x) :=
        List.mem_filter.mpr ⟨hxsq, by simpa using hxm⟩
      rw [hfil, List.mem_singleton] at this
      exact absurd this hxz
  have hc1 : (r, c) ∈ corners r c s := by rw [mem_corners]; tauto
  have hc2 : (r, c + s) ∈ corners r c s := by rw [mem_corners]; tauto
  have hc3 : (r + s, c) ∈ corners r c s := by rw [mem_corners]; tauto
  have hc4 : (r + s, c + s) ∈ corners r c s := by rw [mem_corners]; tauto
  have d12 : ((r, c) : Cell) ≠ (r, c + s) := by simp [Prod.ext_iff]; omega
  have d13 : ((r, c) : Cell) ≠ (r + s, c) := by simp [Prod.ext_iff]; omega
  have d14 : ((r, c) : Cell) ≠ (r + s, c + s) := by simp [Prod.ext_iff]; omega
  have d23 : ((r, c + s) : Cell) ≠ (r + s, c) := by simp [Prod.ext_iff]; omega
  have d24 : ((r, c + s) : Cell) ≠ (r + s, c + s) := by
    simp [Prod.ext_iff]; omega
  have d34 : ((r + s, c) : Cell) ≠ (r + s, c + s) := by
    simp [Prod.ext_iff]; omega
  have hbound : r + s < B ∧ c + s < B := by
    by_cases e1 : ((r, c) : Cell) = z
    · exact three_corners_confine hc2 hc3 hc4 d23 d24 d34
        (hin _ (by simp) (e1 ▸ d12.symm)) (hin _ (by simp) (e1 ▸ d13.symm))
        (hin _ (by simp) (e1 ▸ d14.symm))
    · by_cases e2 : ((r, c + s) : Cell) = z
      · exact three_corners_confine hc1 hc3 hc4 d13 d14 d34
          (hin _ (by simp) e1) (hin _ (by simp) (e2 ▸ d23.symm))
          (hin _ (by simp) (e2 ▸ d24.symm))
      · by_cases e3 : ((r + s, c) : Cell) = z
        · exact three_corners_confine hc1 hc2 hc4 d12 d14 d24
            (hin _ (by simp) e1) (hin _ (by simp) e2)
            (hin _ (by simp) (e3 ▸ d34.symm))
        · exact three_corners_confine hc1 hc2 hc3 d12 d13 d23
            (hin _ (by simp) e1) (hin _ (by simp) e2)
            (hin _ (by simp) e3)
  exact mem_squaresList.mpr ⟨r, c, s, hs, hbound.1, hbound.2, rfl⟩

/-! ## Threat sets across boards

With the strategy's stones inside the box, a threat square has three
distinct corners in the box, so the whole square sits inside any
board of size at least the box; threat sets therefore agree between
any two such boards whenever occupancy agrees on the box. -/

theorem mem_threatsL_iff_cross {B n : ℕ} (h6 : 6 ≤ B) (hBn : B ≤ n)
    {mine occ occ' : List Cell} (hmine : ∀ x ∈ mine, x ∈ board 6)
    (hocc : ∀ x ∈ board 6, (x ∈ occ ↔ x ∈ occ')) {z : Cell} :
    z ∈ threatsL (squaresList B) mine occ ↔
      z ∈ threatsL (squaresList n) mine occ' := by
  have hboard6 : (6 : ℕ) ≤ B := h6
  constructor <;> intro h
  · obtain ⟨sq, hsq, hfil, hzocc⟩ := mem_threatsL h
    have hsq6 : sq ∈ squaresList 6 :=
      square_filter_confine (by omega) (by omega) hmine hsq hfil
    have hzsq : z ∈ sq :=
      List.mem_of_mem_filter (hfil ▸ List.mem_cons_self ..)
    have hz6 : z ∈ board 6 := squaresList_on_board hsq6 z hzsq
    refine threatsL_of_filter (squaresList_mono (by omega) hsq6) hfil ?_
    rw [Bool.eq_false_iff] at hzocc ⊢
    intro hx
    exact hzocc (by
      rw [List.contains_iff_mem] at hx ⊢
      exact (hocc z hz6).mpr hx)
  · obtain ⟨sq, hsq, hfil, hzocc⟩ := mem_threatsL h
    have hsq6 : sq ∈ squaresList 6 :=
      square_filter_confine (by omega) (by omega) hmine hsq hfil
    have hzsq : z ∈ sq :=
      List.mem_of_mem_filter (hfil ▸ List.mem_cons_self ..)
    have hz6 : z ∈ board 6 := squaresList_on_board hsq6 z hzsq
    refine threatsL_of_filter (squaresList_mono hboard6 hsq6) hfil ?_
    rw [Bool.eq_false_iff] at hzocc ⊢
    intro hx
    exact hzocc (by
      rw [List.contains_iff_mem] at hx ⊢
      exact (hocc z hz6).mp hx)

/-! ## The simulation

A base history (checked by a forced run on the base board) and a real
history on the target board agree everywhere except possibly at the
two reply slots. A shared slot holds one stone inside the base
region; a substituted slot pairs a base stand-in with a real stone,
both outside `board 12`, the real one outside `board 17`. The pair
mode records what `farmKey` says about the real replies: `none`
means no square escaping the base can use them (`escape_farm`), and
`some hot` means every such square runs through `hot`, which the
opponent never holds in a recursed position. -/

/-- One reply slot of the simulation: shared verbatim, or
substituted. -/
def SlotOk (B n : ℕ) (b r : Cell) : Prop :=
  (b = r ∧ r ∈ board 17 ∧ r ∈ board B) ∨
  (b ∈ board B ∧ b ∉ board 12 ∧ r ∈ board n ∧ r ∉ board 12 ∧
    r ∉ board 17)

/-- The pair mode: the real replies farm nothing, or they farm
exactly through `hot`. -/
def PairMode (hot : Option Cell) (r1 r2 : Cell) (p2r : List Cell) : Prop :=
  match hot with
  | none => farmKey 6 r1 r2 = none
  | some h => farmKey 6 r1 r2 = some (.farm h) ∧ h ∉ p2r

/-- The safety core: no real reply completes an opponent square. The
opponent's real stones are the two replies and box cells shared with
the base run. A hypothetical square with a substituted reply among
its corners escapes the base region, so `escape_farm` reduces it to
the pair mode; a square without one lies among cells the base run
shares, where the base scan and the base square-freeness kill it,
including a reply landing on a stand-in cell. -/
theorem simulate_safe {B n : ℕ} (hB : 17 ≤ B) (hot : Option Cell)
    {o1b o1r o2b o2r : Cell} {P D : List Cell}
    (hs1 : SlotOk B n o1b o1r) (hs2 : SlotOk B n o2b o2r)
    (hP : ∀ y ∈ P, y ∈ board 6) (hD : ∀ y ∈ D, y ∈ board 6)
    (hnoB : ¬ HasSquare (o1b :: o2b :: D).toFinset)
    (hpair : o1r ∉ board 17 ∨ o2r ∉ board 17 →
      PairMode hot o1r o2r (o1r :: o2r :: D))
    (hscanB : threatsL (squaresList B) (o1b :: o2b :: D)
      (P ++ (o1b :: o2b :: D)) = [])
    {x : Cell} (hxP : x ∉ P) (hxr : x ∉ o1r :: o2r :: D) :
    ¬ HasSquare (insert x (o1r :: o2r :: D).toFinset) := by
  rintro ⟨a, b, s, hs, hsub⟩
  have hdis : ∀ w ∈ corners a b s,
      w = x ∨ w = o1r ∨ w = o2r ∨ w ∈ D := by
    intro w hw
    have := hsub hw
    rcases Finset.mem_insert.mp this with rfl | hwp
    · exact Or.inl rfl
    · rw [List.mem_toFinset, List.mem_cons, List.mem_cons] at hwp
      tauto
  by_cases hesc : a + s < 17 ∧ b + s < 17
  · -- contained: every corner is on board 17, and substituted reply
    -- stones are not, so the corners live among base-shared cells
    have hcor17 : ∀ w ∈ corners a b s, w ∈ board 17 := by
      intro w hw
      rw [mem_corners] at hw
      rw [mem_board]
      rcases hw with rfl | rfl | rfl | rfl <;> constructor <;> omega
    have hcorB : ∀ w ∈ corners a b s, w ≠ x →
        w ∈ (o1b :: o2b :: D).toFinset := by
      intro w hw hwx
      rcases hdis w hw with rfl | rfl | rfl | hwD
      · exact absurd rfl hwx
      · rw [List.mem_toFinset, List.mem_cons]
        rcases hs1 with ⟨heq, -, -⟩ | ⟨-, -, -, -, h17⟩
        · exact Or.inl heq.symm
        · exact absurd (hcor17 _ hw) h17
      · rw [List.mem_toFinset, List.mem_cons, List.mem_cons]
        rcases hs2 with ⟨heq, -, -⟩ | ⟨-, -, -, -, h17⟩
        · exact Or.inr (Or.inl heq.symm)
        · exact absurd (hcor17 _ hw) h17
      · rw [List.mem_toFinset, List.mem_cons, List.mem_cons]
        exact Or.inr (Or.inr hwD)
    by_cases hxc : x ∈ corners a b s
    · -- the reply is a corner; the other corners are base stones
      by_cases hxbase : x ∈ (o1b :: o2b :: D).toFinset
      · -- the reply sits on a stand-in: the base already holds the
        -- whole square
        apply hnoB
        refine ⟨a, b, s, hs, fun w hw => ?_⟩
        by_cases hwx : w = x
        · exact hwx ▸ hxbase
        · exact hcorB w hw hwx
      · -- a genuine base reply: the base scan forbids it
        have hxB : x ∈ board B := by
          have := hcor17 x hxc
          rw [mem_board] at this ⊢
          omega
        have hp2B : ∀ y ∈ o1b :: o2b :: D, y ∈ board B := by
          intro y hy
          rw [List.mem_cons, List.mem_cons] at hy
          rcases hy with rfl | rfl | hyD
          · rcases hs1 with ⟨heq, -, hb⟩ | ⟨hb, -, -, -, -⟩ <;>
              [exact heq ▸ hb; exact hb]
          · rcases hs2 with ⟨heq, -, hb⟩ | ⟨hb, -, -, -, -⟩ <;>
              [exact heq ▸ hb; exact hb]
          · have := hD y hyD
            rw [mem_board] at this ⊢
            omega
        have hxnb : x ∉ o1b :: o2b :: D := fun hy =>
          hxbase (List.mem_toFinset.mpr hy)
        have hocc : ((P ++ (o1b :: o2b :: D)).contains x) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          rw [List.contains_iff_mem, List.mem_append] at hc
          rcases hc with hc | hc
          · exact hxP hc
          · exact hxnb hc
        have hcf := completesL_eq_false_of_threats_nil hscanB hocc hxnb
        apply not_hasSquare_insert hxB hp2B hnoB hcf
        refine ⟨a, b, s, hs, fun w hw => ?_⟩
        by_cases hwx : w = x
        · exact hwx ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hcorB w hw hwx)
    · -- the reply is not a corner: the base already holds the square
      apply hnoB
      refine ⟨a, b, s, hs, fun w hw => ?_⟩
      exact hcorB w hw (fun he => hxc (he ▸ hw))
  · -- escaping: the corners are the reply, the two reply stones, and
    -- one box cell, and the pair mode decides
    have hesc' : 17 ≤ a + s ∨ 17 ≤ b + s := by omega
    obtain ⟨d, hdD, hdc, ho1c, ho2c, hdo1, hdo2, ho12⟩ :=
      escape_pick hs hesc' hD
        (hdis _ (by rw [mem_corners]; tauto))
        (hdis _ (by rw [mem_corners]; tauto))
        (hdis _ (by rw [mem_corners]; tauto))
        (hdis _ (by rw [mem_corners]; tauto))
    by_cases h17 : o1r ∈ board 17 ∧ o2r ∈ board 17
    · -- three corners on board 17 confine the square: no escape
      have hd17 : d ∈ board 17 := by
        have := hD d hdD
        rw [mem_board] at this ⊢
        omega
      have := three_corners_confine hdc ho1c ho2c hdo1 hdo2 ho12
        hd17 h17.1 h17.2
      omega
    · have hfk := escape_farm hs hesc' hdc ho1c ho2c hdo1 hdo2 ho12
        (hD d hdD)
      have hpair' := hpair (by tauto)
      cases hot with
      | none =>
        rw [PairMode] at hpair'
        rw [hpair'] at hfk
        exact absurd hfk (by simp)
      | some h =>
        rw [PairMode] at hpair'
        obtain ⟨hsome, hnotin⟩ := hpair'
        rw [hsome] at hfk
        have hdh : h = d := by
          have := Option.some_inj.mp hfk
          exact (Key.farm.injEq .. ▸ this : _)
        exact hnotin (hdh ▸ List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hdD))

/-! ## Plumbing for the main induction -/

/-- Fewer than four stones hold no square. -/
theorem no_square_of_short {L : List Cell} (h : L.length < 4) :
    ¬ HasSquare L.toFinset := by
  rintro ⟨a, b, s, hs, hsub⟩
  have hcard : (corners a b s).card ≤ L.toFinset.card :=
    Finset.card_le_card hsub
  have hLc : L.toFinset.card ≤ L.length := L.toFinset_card_le
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
  have : (corners a b s).card = 4 := by
    rw [corners]
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
      Finset.card_insert_of_notMem (by simp [h4, h5]),
      Finset.card_insert_of_notMem (by simp [h6]),
      Finset.card_singleton]
  omega

/-- A winning move against box-confined stones lands in the box. -/
theorem win_move_in_box {p1 : List Cell} {m : Cell}
    (hp1 : ∀ y ∈ p1, y ∈ board 6)
    (hno : ¬ HasSquare p1.toFinset)
    (hwin : HasSquare (insert m p1.toFinset)) : m ∈ board 6 := by
  obtain ⟨a, b, s, hs, hsub⟩ := hwin
  have hmc : m ∈ corners a b s := by
    by_contra hmc
    apply hno
    refine ⟨a, b, s, hs, fun w hw => ?_⟩
    rcases Finset.mem_insert.mp (hsub hw) with rfl | h
    · exact absurd hw hmc
    · exact h
  -- three corners besides m are P1 stones in the box
  have hin : ∀ w ∈ corners a b s, w ≠ m → w ∈ board 6 := by
    intro w hw hwm
    rcases Finset.mem_insert.mp (hsub hw) with rfl | h
    · exact absurd rfl hwm
    · exact hp1 w (List.mem_toFinset.mp h)
  rw [mem_corners] at hmc
  have hc1 : ((a, b) : Cell) ∈ corners a b s := by rw [mem_corners]; tauto
  have hc2 : ((a, b + s) : Cell) ∈ corners a b s := by
    rw [mem_corners]; tauto
  have hc3 : ((a + s, b) : Cell) ∈ corners a b s := by
    rw [mem_corners]; tauto
  have hc4 : ((a + s, b + s) : Cell) ∈ corners a b s := by
    rw [mem_corners]; tauto
  rcases hmc with rfl | rfl | rfl | rfl
  · -- m is the northwest corner: the southeast pair confines it
    have h2 := hin _ hc2 (by simp [Prod.ext_iff]; omega)
    have h3 := hin _ hc3 (by simp [Prod.ext_iff]; omega)
    rw [mem_board] at h2 h3 ⊢
    dsimp only at h2 h3 ⊢
    omega
  · have h1 := hin _ hc1 (by simp [Prod.ext_iff]; omega)
    have h4 := hin _ hc4 (by simp [Prod.ext_iff]; omega)
    rw [mem_board] at h1 h4 ⊢
    dsimp only at h1 h4 ⊢
    omega
  · have h1 := hin _ hc1 (by simp [Prod.ext_iff]; omega)
    have h4 := hin _ hc4 (by simp [Prod.ext_iff]; omega)
    rw [mem_board] at h1 h4 ⊢
    dsimp only at h1 h4 ⊢
    omega
  · have h2 := hin _ hc2 (by simp [Prod.ext_iff]; omega)
    have h3 := hin _ hc3 (by simp [Prod.ext_iff]; omega)
    rw [mem_board] at h2 h3 ⊢
    dsimp only at h2 h3 ⊢
    omega

theorem inBox_iff {k : ℕ} {c : Cell} : inBox k c = true ↔ c ∈ board k := by
  simp [inBox, mem_board]

set_option maxHeartbeats 3200000 in
/-- Replaying a forced base run on the target board, from any forced
position whose histories differ only at the two reply slots. -/
theorem simulate (σ : Strategy) {B n : ℕ}
    (hot : Option Cell) (hn17 : 17 ≤ n) (hB17 : 17 ≤ B)
    {opc x2c o1b o1r o2b o2r : Cell}
    (hop : opc ∈ board 6) (hx2 : x2c ∈ board 6)
    (hs1 : SlotOk B n o1b o1r) (hs2 : SlotOk B n o2b o2r) :
    ∀ (fuel : ℕ) (tail : List Cell),
      tail.length % 2 = 0 →
      (∀ y ∈ tail, y ∈ board 6) →
      goForcedS σ 6 (squaresList B) B hot fuel
        (opc :: o1b :: x2c :: o2b :: tail) = true →
      ¬ HasSquare (o1b :: o2b :: stonesOf false tail).toFinset →
      ¬ HasSquare (opc :: x2c :: stonesOf true tail).toFinset →
      (o1r ∉ board 17 ∨ o2r ∉ board 17 →
        PairMode hot o1r o2r (o1r :: o2r :: stonesOf false tail)) →
      P1CanWin n (opc :: x2c :: stonesOf true tail).toFinset
        (o1r :: o2r :: stonesOf false tail).toFinset := by
  have hb6B : ∀ w : Cell, w ∈ board 6 → w ∈ board B := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hb6n : ∀ w : Cell, w ∈ board 6 → w ∈ board n := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  have hb612 : ∀ w : Cell, w ∈ board 6 → w ∈ board 12 := by
    intro w hw
    rw [mem_board] at hw ⊢
    omega
  intro fuel
  induction fuel with
  | zero => intro tail _ _ h _ _ _; simp [goForcedS] at h
  | succ fuel ih =>
    intro tail hlen htail h hnoB hp1no hpair
    set TT := stonesOf true tail with hTT
    set DB := stonesOf false tail with hDB
    have hTTt : ∀ y ∈ TT, y ∈ board 6 := fun y hy =>
      htail y ((mem_stonesOf tail true).mpr (Or.inl hy))
    have hDBt : ∀ y ∈ DB, y ∈ board 6 := fun y hy =>
      htail y ((mem_stonesOf tail false).mpr (Or.inl hy))
    set p1 := opc :: x2c :: TT with hp1def
    set p2B := o1b :: o2b :: DB with hp2Bdef
    set p2R := o1r :: o2r :: DB with hp2Rdef
    have hp1box : ∀ y ∈ p1, y ∈ board 6 := by
      intro y hy
      rw [hp1def, List.mem_cons, List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact hop
      · exact hx2
      · exact hTTt y hy
    have hstT : stonesOf true (opc :: o1b :: x2c :: o2b :: tail) = p1 := rfl
    have hstF : stonesOf false (opc :: o1b :: x2c :: o2b :: tail) = p2B :=
      rfl
    have ho1B : o1b ∈ board B := by
      rcases hs1 with ⟨heq, -, hb⟩ | ⟨hb, -, -, -, -⟩
      · exact heq ▸ hb
      · exact hb
    have ho2B : o2b ∈ board B := by
      rcases hs2 with ⟨heq, -, hb⟩ | ⟨hb, -, -, -, -⟩
      · exact heq ▸ hb
      · exact hb
    have ho1n : o1r ∈ board n := by
      rcases hs1 with ⟨heq, h17, -⟩ | ⟨-, -, hb, -, -⟩
      · rw [mem_board] at h17 ⊢; omega
      · exact hb
    have ho2n : o2r ∈ board n := by
      rcases hs2 with ⟨heq, h17, -⟩ | ⟨-, -, hb, -, -⟩
      · rw [mem_board] at h17 ⊢; omega
      · exact hb
    -- a box cell absent from the base position is absent from both
    have hfree : ∀ z : Cell, z ∈ board 6 →
        (((z : Cell) ∈ p1 → False) ∧ (z ∈ p2B → False)) →
        z ∉ p1 ∧ z ∉ p2R := by
      intro z hz6 hzb
      refine ⟨hzb.1, ?_⟩
      intro hz
      rw [hp2Rdef, List.mem_cons, List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · rcases hs1 with ⟨heq, -, -⟩ | ⟨-, -, -, h12, -⟩
        · exact hzb.2 (heq ▸ List.mem_cons_self ..)
        · exact h12 (hb612 _ hz6)
      · rcases hs2 with ⟨heq, -, -⟩ | ⟨-, -, -, h12, -⟩
        · exact hzb.2 (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
        · exact h12 (hb612 _ hz6)
      · exact hzb.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
    simp only [goForcedS] at h
    rw [hstT, hstF] at h
    split at h
    · exact absurd h (by simp)
    · rename_i m hsm
      split at h
      · exact absurd h (by simp)
      · rename_i hguard
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true',
          Bool.not_eq_true, List.contains_iff_mem] at hguard
        obtain ⟨⟨hmB, hm1⟩, hm2⟩ := hguard
        have hmB' : m ∈ board B := by
          rw [← onBoard_iff]
          revert hmB
          cases onBoard B m <;> simp
        have hm1' : m ∉ p1 := by simpa using hm1
        have hm2' : m ∉ p2B := by simpa using hm2
        split at h
        · -- the base run wins: the same move wins on the target board
          rename_i hwin
          have hw : HasSquare (insert m p1.toFinset) := by
            have := hasSquareL_sound (n := B) (L := m :: p1) hwin
            simpa using this
          have hm6 : m ∈ board 6 := win_move_in_box hp1box hp1no hw
          have hmfree := hfree m hm6 ⟨fun hc => hm1' hc, fun hc => hm2' hc⟩
          refine P1CanWin.now m (mem_empties.mpr ⟨hb6n m hm6, ?_, ?_⟩) hw
          · intro hc
            exact hmfree.1 (List.mem_toFinset.mp hc)
          · intro hc
            exact hmfree.2 (List.mem_toFinset.mp hc)
        · rename_i hnowin
          have hp1no' : ¬ HasSquare (insert m p1.toFinset) := by
            intro hc
            have : hasSquareL (squaresList B) (m :: p1) = true := by
              rw [hasSquareL_iff (n := B)]
              · simpa using hc
              · intro y hy
                rcases List.mem_cons.mp hy with rfl | hy
                · exact hmB'
                · exact hb6B y (hp1box y hy)
            exact absurd this (by simpa using hnowin)
          split at h
          · exact absurd h (by simp)
          · rename_i hmbox
            have hm6 : m ∈ board 6 := by
              rw [← inBox_iff (k := 6)]
              revert hmbox
              cases inBox 6 m <;> simp
            split at h
            · exact absurd h (by simp)
            · rename_i hp2scan
              have hscan : threatsL (squaresList B) p2B ((m :: p1) ++ p2B)
                  = [] := by
                have : (threatsL (squaresList B) p2B
                    ((m :: p1) ++ p2B)).isEmpty = true := by
                  revert hp2scan
                  cases (threatsL (squaresList B) p2B
                    ((m :: p1) ++ p2B)).isEmpty <;> simp
                simpa [List.isEmpty_iff] using this
              split at h
              · rename_i hlv
                exfalso
                simp only [List.length_cons] at hlv
                omega
              · rename_i hlv
                set ths := threatsL (squaresList B) (m :: p1)
                  ((m :: p1) ++ p2B) with hths
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
                      have hthne' : ths ≠ [] := by
                        intro hnil
                        rw [hnil] at hthne
                        simp at hthne
                      obtain ⟨z₀, hz₀⟩ := List.exists_mem_of_ne_nil _ hthne'
                      have hthsbox : ∀ z ∈ ths, z ∈ board 6 := by
                        have : ths.all (inBox 6) = true := by
                          revert hthbox
                          cases ths.all (inBox 6) <;> simp
                        rw [List.all_eq_true] at this
                        intro z hz
                        have := this z hz
                        exact inBox_iff.mp this
                      -- each threat is a live two-move win on both boards
                      have hthdata := fun z (hz : z ∈ ths) =>
                        threat_wins (n := B) (hths ▸ hz)
                      have hthfree : ∀ z ∈ ths, z ∉ p1 ∧ z ∉ p2R ∧ z ≠ m := by
                        intro z hz
                        obtain ⟨-, -, hocc⟩ := hthdata z hz
                        rw [Bool.eq_false_iff] at hocc
                        have hmem : ∀ w ∈ (m :: p1) ++ p2B, z ≠ w := by
                          intro w hw he
                          exact hocc (by
                            rw [List.contains_iff_mem]
                            exact he ▸ hw)
                        have hnot : z ∉ p1 ∧ z ∉ p2B ∧ z ≠ m := by
                          refine ⟨?_, ?_, hmem m (by simp)⟩
                          · intro hc
                            exact hmem z (by simp [hc]) rfl
                          · intro hc
                            exact hmem z (by simp [hc]) rfl
                        obtain ⟨hzfree1, hzfree2⟩ := hfree z (hthsbox z hz)
                          ⟨fun hc => hnot.1 hc, fun hc => hnot.2.1 hc⟩
                        exact ⟨hzfree1, hzfree2, hnot.2.2⟩
                      -- safety, from the base scan and the pair mode
                      have hsafe : ∀ r ∈ empties n (insert m p1.toFinset)
                          p2R.toFinset, ¬ HasSquare (insert r p2R.toFinset) := by
                        intro r hr
                        obtain ⟨hrb, hr1, hr2⟩ := mem_empties.mp hr
                        have hxP : r ∉ m :: p1 := by
                          intro hc
                          rcases List.mem_cons.mp hc with rfl | hc
                          · exact hr1 (Finset.mem_insert_self _ _)
                          · exact hr1 (Finset.mem_insert_of_mem
                              (List.mem_toFinset.mpr hc))
                        have hxr : r ∉ p2R := fun hc =>
                          hr2 (List.mem_toFinset.mpr hc)
                        exact simulate_safe hB17 hot hs1 hs2
                          (fun y hy => List.mem_cons.mp hy |>.elim
                            (fun he => he ▸ hm6) (hp1box y))
                          hDBt hnoB hpair hscan hxP hxr
                      -- the move is playable on the target board
                      have hmfree := hfree m hm6
                        ⟨fun hc => hm1' hc, fun hc => hm2' hc⟩
                      have hmE : m ∈ empties n p1.toFinset p2R.toFinset :=
                        mem_empties.mpr ⟨hb6n m hm6,
                          fun hc => hmfree.1 (List.mem_toFinset.mp hc),
                          fun hc => hmfree.2 (List.mem_toFinset.mp hc)⟩
                      -- a threat cell is empty on the target board
                      have hthE : ∀ z ∈ ths,
                          z ∈ empties n (insert m p1.toFinset) p2R.toFinset := by
                        intro z hz
                        obtain ⟨hz1, hz2, hzm⟩ := hthfree z hz
                        refine mem_empties.mpr ⟨hb6n z (hthsbox z hz), ?_, ?_⟩
                        · intro hc
                          rcases Finset.mem_insert.mp hc with rfl | hc
                          · exact hzm rfl
                          · exact hz1 (List.mem_toFinset.mp hc)
                        · intro hc
                          exact hz2 (List.mem_toFinset.mp hc)
                      have hne : (empties n (insert m p1.toFinset)
                          p2R.toFinset).Nonempty := ⟨z₀, hthE z₀ hz₀⟩
                      refine P1CanWin.step m hmE hne hsafe ?_
                      intro r hr
                      obtain ⟨hrb, hr1, hr2⟩ := mem_empties.mp hr
                      -- the two-move win through a standing threat
                      have hnow : ∀ z ∈ ths, z ≠ r →
                          P1CanWin n (insert m p1.toFinset)
                            (insert r p2R.toFinset) := by
                        intro z hz hzr
                        obtain ⟨hwz, -, -⟩ := hthdata z hz
                        have hwz' : HasSquare (insert z
                            (insert m p1.toFinset)) := by
                          have : (m :: p1).toFinset =
                              insert m p1.toFinset := by
                            ext w; simp
                          rwa [this] at hwz
                        have hzE := hthE z hz
                        obtain ⟨hzb', hz1', hz2'⟩ := mem_empties.mp hzE
                        refine P1CanWin.now z
                          (mem_empties.mpr ⟨hzb', hz1', ?_⟩) hwz'
                        intro hc
                        rcases Finset.mem_insert.mp hc with rfl | hc
                        · exact hzr rfl
                        · exact hz2' hc
                      by_cases hrths : r ∈ ths
                      · by_cases hrhot : hot = some r
                        · -- the block took the farm cell: win through
                          -- the second threat instead
                          have : ¬ (ths.all (· == r) = true) := by
                            intro hc
                            apply hhot
                            rw [hrhot]
                            simpa using hc
                          rw [List.all_eq_true] at this
                          push_neg at this
                          obtain ⟨z', hz', hz'r⟩ := this
                          exact hnow z' hz' (by simpa using hz'r)
                        · -- an ordinary block: follow the base branch
                          have hbase := h r hrths
                          have hr6 : r ∈ board 6 := hthsbox r hrths
                          obtain ⟨hrp1, hrp2R, hrm⟩ := hthfree r hrths
                          have hrp2B : r ∉ p2B := by
                            obtain ⟨-, -, hocc⟩ := hthdata r hrths
                            rw [Bool.eq_false_iff] at hocc
                            intro hc
                            exact hocc (by
                              rw [List.contains_iff_mem, List.mem_append]
                              exact Or.inr hc)
                          -- base-side square-freeness extends
                          have hnoB' : ¬ HasSquare
                              (insert r p2B.toFinset) := by
                            have hoccr : (((m :: p1) ++ p2B).contains r)
                                = false := (hthdata r hrths).2.2
                            have hcf := completesL_eq_false_of_threats_nil
                              hscan hoccr hrp2B
                            exact not_hasSquare_insert (hb6B r hr6)
                              (fun y hy => by
                                rw [hp2Bdef, List.mem_cons,
                                  List.mem_cons] at hy
                                rcases hy with rfl | rfl | hy
                                · exact ho1B
                                · exact ho2B
                                · exact hb6B y (hDBt y hy))
                              hnoB hcf
                          have htail' : ∀ y ∈ (tail ++ [m]) ++ [r],
                              y ∈ board 6 := by
                            intro y hy
                            rcases List.mem_append.mp hy with hy | hy
                            · rcases List.mem_append.mp hy with hy | hy
                              · exact htail y hy
                              · rw [List.mem_singleton] at hy
                                exact hy ▸ hm6
                            · rw [List.mem_singleton] at hy
                              exact hy ▸ hr6
                          have hlen' : ((tail ++ [m]) ++ [r]).length % 2
                              = 0 := by
                            simp [List.length_append]
                            omega
                          have hstT' : stonesOf true ((tail ++ [m]) ++ [r])
                              = TT ++ [m] := by
                            rw [stonesOf_snoc_odd_true
                              (by rw [List.length_append]; simp; omega),
                              stonesOf_snoc_even_true hlen]
                          have hstF' : stonesOf false ((tail ++ [m]) ++ [r])
                              = DB ++ [r] := by
                            rw [stonesOf_snoc_odd_false
                              (by rw [List.length_append]; simp; omega),
                              stonesOf_snoc_even_false hlen]
                          have hbase' : goForcedS σ 6 (squaresList B) B hot fuel
                              (opc :: o1b :: x2c :: o2b ::
                                ((tail ++ [m]) ++ [r])) = true := by
                            have : (opc :: o1b :: x2c :: o2b :: tail)
                                ++ [m] ++ [r] =
                                opc :: o1b :: x2c :: o2b ::
                                  ((tail ++ [m]) ++ [r]) := by
                              simp
                            rwa [this] at hbase
                          have hind := ih ((tail ++ [m]) ++ [r]) hlen'
                            htail' hbase'
                            (by
                              rw [hstF']
                              intro hc
                              apply hnoB'
                              have : (o1b :: o2b :: (DB ++ [r])).toFinset =
                                  insert r p2B.toFinset := by
                                ext w
                                rw [hp2Bdef]
                                simp [List.toFinset_append, or_comm]
                                tauto
                              rwa [this] at hc)
                            (by
                              rw [hstT']
                              intro hc
                              apply hp1no'
                              have : (opc :: x2c :: (TT ++ [m])).toFinset =
                                  insert m p1.toFinset := by
                                ext w
                                rw [hp1def]
                                simp [List.toFinset_append, or_comm]
                                tauto
                              rwa [this] at hc)
                            (by
                              rw [hstF']
                              intro hoff
                              have hp := hpair hoff
                              cases hot with
                              | none => exact hp
                              | some hh =>
                                rw [PairMode] at hp ⊢
                                refine ⟨hp.1, ?_⟩
                                intro hc
                                rw [List.mem_cons, List.mem_cons,
                                  List.mem_append] at hc
                                rcases hc with rfl | rfl | hc | hc
                                · exact hp.2 (List.mem_cons_self ..)
                                · exact hp.2 (List.mem_cons_of_mem _
                                    (List.mem_cons_self ..))
                                · exact hp.2 (List.mem_cons_of_mem _
                                    (List.mem_cons_of_mem _ hc))
                                · rw [List.mem_singleton] at hc
                                  exact hrhot (hc ▸ rfl))
                          rw [hstT', hstF'] at hind
                          have e1 : (opc :: x2c :: (TT ++ [m])).toFinset =
                              insert m p1.toFinset := by
                            ext w
                            rw [hp1def]
                            simp [List.toFinset_append, or_comm]
                            tauto
                          have e2 : (o1r :: o2r :: (DB ++ [r])).toFinset =
                              insert r p2R.toFinset := by
                            ext w
                            rw [hp2Rdef]
                            simp [List.toFinset_append, or_comm]
                            tauto
                          rwa [e1, e2] at hind
                      · -- not a block: the standing threat wins now
                        exact hnow z₀ hz₀ (fun he => hrths (he ▸ hz₀))

/-- The table instance: a forced base run of a table with box `6`. -/
theorem simulate_table (t : Table) (hbox : t.box = 6) {B n : ℕ}
    (hot : Option Cell) (hn17 : 17 ≤ n) (hB17 : 17 ≤ B)
    {opc x2c o1b o1r o2b o2r : Cell}
    (hop : opc ∈ board 6) (hx2 : x2c ∈ board 6)
    (hs1 : SlotOk B n o1b o1r) (hs2 : SlotOk B n o2b o2r) :
    ∀ (fuel : ℕ) (tail : List Cell),
      tail.length % 2 = 0 →
      (∀ y ∈ tail, y ∈ board 6) →
      goForced t (squaresList B) B hot fuel
        (opc :: o1b :: x2c :: o2b :: tail) = true →
      ¬ HasSquare (o1b :: o2b :: stonesOf false tail).toFinset →
      ¬ HasSquare (opc :: x2c :: stonesOf true tail).toFinset →
      (o1r ∉ board 17 ∨ o2r ∉ board 17 →
        PairMode hot o1r o2r (o1r :: o2r :: stonesOf false tail)) →
      P1CanWin n (opc :: x2c :: stonesOf true tail).toFinset
        (o1r :: o2r :: stonesOf false tail).toFinset := by
  intro fuel tail hlen htail hrun
  have hrun' : goForcedS (strategyMove t) 6 (squaresList B) B hot fuel
      (opc :: o1b :: x2c :: o2b :: tail) = true := by
    rw [goForced, hbox] at hrun
    exact hrun
  exact simulate (strategyMove t) hot hn17 hB17 hop hx2 hs1 hs2 fuel tail hlen htail hrun'

end SquareAchievement
