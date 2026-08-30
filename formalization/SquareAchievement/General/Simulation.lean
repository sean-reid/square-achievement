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

end SquareAchievement
