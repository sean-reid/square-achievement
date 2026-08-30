import SquareAchievement.Compute.ForcedSound
import SquareAchievement.General.Invariance

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

end SquareAchievement
