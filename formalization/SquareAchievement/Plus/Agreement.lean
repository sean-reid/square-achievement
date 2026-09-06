import SquareAchievement.General.Dispatch
import SquareAchievement.General.Coverage
import SquareAchievement.Plus.Rule

/-!
# The rule reads the same move from a real history and its base view

The rule depends on a history only through its abstraction (the first
player's stones, the opponent's stones inside the base board, the
latent corner of the free pair) and through the first reply's second
move. A real reply beyond the base board and its stand-in are both
dropped by the abstraction; a reply inside it is read verbatim; and the
wrapper chooses stand-ins with the same farm key and the same second
move. So the rule's move on the real board is its move on the base
history, at every node of the simulation.
-/

namespace SquareAchievement.Plus

/-- A reply slot the abstraction cannot tell apart: the same cell, or
two cells both beyond the base board. -/
def SlotSame (b r : Cell) : Prop := b = r ∨ (onBoard base b = false ∧ onBoard base r = false)

theorem filter_slots {o1b o1r o2b o2r : Cell} (h1 : SlotSame o1b o1r) (h2 : SlotSame o2b o2r)
    (rest : List Cell) :
    (o1r :: o2r :: rest).filter (onBoard base) = (o1b :: o2b :: rest).filter (onBoard base) := by
  rcases h1 with rfl | ⟨hb1, hr1⟩ <;> rcases h2 with rfl | ⟨hb2, hr2⟩ <;>
    simp [List.filter_cons, *]

theorem abstractOf_eq {o1b o1r o2b o2r x2 : Cell} (tail : List Cell)
    (h1 : SlotSame o1b o1r) (h2 : SlotSame o2b o2r)
    (hkey : farmKey box o1b o2b = farmKey box o1r o2r) :
    abstractOf (opening :: o1r :: x2 :: o2r :: tail) =
      abstractOf (opening :: o1b :: x2 :: o2b :: tail) := by
  have er : stonesOf false (opening :: o1r :: x2 :: o2r :: tail) =
      o1r :: o2r :: stonesOf false tail := rfl
  have eb : stonesOf false (opening :: o1b :: x2 :: o2b :: tail) =
      o1b :: o2b :: stonesOf false tail := rfl
  have etr : stonesOf true (opening :: o1r :: x2 :: o2r :: tail) =
      opening :: x2 :: stonesOf true tail := rfl
  have etb : stonesOf true (opening :: o1b :: x2 :: o2b :: tail) =
      opening :: x2 :: stonesOf true tail := rfl
  have g1r : (opening :: o1r :: x2 :: o2r :: tail)[1]? = some o1r := rfl
  have g3r : (opening :: o1r :: x2 :: o2r :: tail)[3]? = some o2r := rfl
  have g1b : (opening :: o1b :: x2 :: o2b :: tail)[1]? = some o1b := rfl
  have g3b : (opening :: o1b :: x2 :: o2b :: tail)[3]? = some o2b := rfl
  unfold abstractOf
  simp only [er, eb, etr, etb, g1r, g3r, g1b, g3b, hkey, filter_slots h1 h2]

/-- The rule's moves agree along a real history and its base view. -/
theorem plusMove_agree {o1b o1r o2b o2r : Cell}
    (h1 : SlotSame o1b o1r) (h2 : SlotSame o2b o2r)
    (hkey : farmKey box o1b o2b = farmKey box o1r o2r)
    (hx2 : secondMove o1b = secondMove o1r) (sq sq' : List (List Cell)) :
    ∀ tail : List Cell,
      plusMove sq (opening :: o1r :: secondMove o1r :: o2r :: tail) =
        plusMove sq' (opening :: o1b :: secondMove o1r :: o2b :: tail) := by
  intro tail
  have habs := abstractOf_eq (x2 := secondMove o1r) tail h1 h2 hkey
  have habs4 := abstractOf_eq (x2 := secondMove o1r) [] h1 h2 hkey
  have g1r : (opening :: o1r :: secondMove o1r :: o2r :: tail)[1]? = some o1r := rfl
  have g1b : (opening :: o1b :: secondMove o1r :: o2b :: tail)[1]? = some o1b := rfl
  have t4r : (opening :: o1r :: secondMove o1r :: o2r :: tail).take 4 =
      [opening, o1r, secondMove o1r, o2r] := rfl
  have t4b : (opening :: o1b :: secondMove o1r :: o2b :: tail).take 4 =
      [opening, o1b, secondMove o1r, o2b] := rfl
  simp only [plusMove, g1r, g1b, t4r, t4b, habs, habs4, List.isEmpty_cons,
    Option.bind_eq_bind, Option.bind_some, hx2]

/-! ## The wrapper's stand-ins and anchors qualify -/

theorem onBoard_base_false {c : Cell} (h : c ∉ board 17) : onBoard base c = false := by
  rw [mem_board] at h
  apply Bool.eq_false_iff.mpr
  intro h'
  simp only [onBoard, base, Bool.and_eq_true] at h'
  exact h ⟨of_decide_eq_true h'.1, of_decide_eq_true h'.2⟩

theorem slotSame_far {b r : Cell} (hb : b ∉ board 17) (hr : r ∉ board 17) : SlotSame b r :=
  Or.inr ⟨onBoard_base_false hb, onBoard_base_false hr⟩

theorem farmKey_eq_none {o1 o2 : Cell}
    (h : ∀ hc : Cell, farmKey box o1 o2 = some (.farm hc) → False) :
    farmKey box o1 o2 = none := by
  rcases hk : farmKey box o1 o2 with _ | k
  · rfl
  · obtain ⟨hc, rfl⟩ := farmKey_farm hk
    exact (h hc hk).elim

/-- A near first reply farms nothing with the stand-in for a far second. -/
theorem farmKey_standin_snd {o1 : Cell} (h : o1 ∈ board 17) :
    farmKey box o1 (22, 21) = none := by
  rw [mem_board] at h
  refine farmKey_eq_none fun hc hk => ?_
  obtain ⟨-, -, hcase | hcase⟩ := farmKey_spec hk <;>
    rcases farmCase_spec hcase with hf | hf | hf <;> simp only [box] at hf <;> omega

/-- The stand-in for a far first reply farms nothing with a near second. -/
theorem farmKey_standin_fst {o2 : Cell} (h : o2 ∈ board 17) :
    farmKey box (22, 22) o2 = none := by
  rw [mem_board] at h
  refine farmKey_eq_none fun hc hk => ?_
  obtain ⟨-, -, hcase | hcase⟩ := farmKey_spec hk <;>
    rcases farmCase_spec hcase with hf | hf | hf <;> simp only [box] at hf <;> omega

/-- The two stand-ins farm nothing together. -/
theorem farmKey_standins : farmKey box (22, 22) (22, 21) = none := by decide

end SquareAchievement.Plus
