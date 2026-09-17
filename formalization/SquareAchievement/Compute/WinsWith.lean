import SquareAchievement.Compute.Uniform
import SquareAchievement.Compute.CheckerSound

/-!
# Winning by following a strategy

`P1CanWin` says a winning strategy tree exists. `WinsWith σ n hist`
says more: the tree in which the first player plays `σ`'s move at
every node, from the position after `hist`, is winning. Its
derivations are exactly the strategy's own play, so a theorem
`WinsWith σ n []` is the statement "following `σ` wins", not merely
"a win exists and `σ` generates one such tree".

Two supporting notions. `TakesWinsOn σ box n root` says that on every
history extending `root`, with the first player's stones inside the
box, `σ` takes a completion whenever the board offers one; the forced
checker needs this to cover the replies it does not visit, where a
standing threat wins at once.
-/

namespace SquareAchievement

/-- The first player, playing `σ` at every node, forces a win from the
position after `hist` (first player to move). -/
inductive WinsWith (σ : Strategy) (n : ℕ) : List Cell → Prop
  /-- `σ`'s move completes a square right now. -/
  | now {hist : List Cell} (m : Cell) (hσ : σ (squaresList n) hist = some m)
      (hm : m ∈ empties n (stonesOf true hist).toFinset (stonesOf false hist).toFinset)
      (hwin : HasSquare (insert m (stonesOf true hist).toFinset)) :
      WinsWith σ n hist
  /-- `σ` plays `m`; every reply completes nothing and leaves a position
  from which `σ` still wins. -/
  | step {hist : List Cell} (m : Cell) (hσ : σ (squaresList n) hist = some m)
      (hm : m ∈ empties n (stonesOf true hist).toFinset (stonesOf false hist).toFinset)
      (hne : (empties n (insert m (stonesOf true hist).toFinset)
        (stonesOf false hist).toFinset).Nonempty)
      (hsafe : ∀ r ∈ empties n (insert m (stonesOf true hist).toFinset)
        (stonesOf false hist).toFinset, ¬ HasSquare (insert r (stonesOf false hist).toFinset))
      (hwins : ∀ r ∈ empties n (insert m (stonesOf true hist).toFinset)
        (stonesOf false hist).toFinset, WinsWith σ n ((hist ++ [m]) ++ [r])) :
      WinsWith σ n hist

/-- Forgetting which moves: a strategy's winning tree is a winning tree. -/
theorem WinsWith.p1CanWin {σ : Strategy} {n : ℕ} : ∀ {hist : List Cell},
    WinsWith σ n hist → hist.length % 2 = 0 →
    P1CanWin n (stonesOf true hist).toFinset (stonesOf false hist).toFinset := by
  intro hist h
  induction h with
  | now m _ hm hwin => intro _; exact P1CanWin.now m hm hwin
  | @step hist m _ hm hne hsafe _ ih =>
    intro hEven
    refine P1CanWin.step m hm hne hsafe ?_
    intro r hr
    have hlen' : (hist ++ [m]).length % 2 = 1 := by
      rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
    have hlen'' : ((hist ++ [m]) ++ [r]).length % 2 = 0 := by
      simp [List.length_append]; omega
    have hs1 : stonesOf true ((hist ++ [m]) ++ [r]) = stonesOf true hist ++ [m] := by
      rw [stonesOf_snoc_odd_true hlen', stonesOf_snoc_even_true hEven]
    have hs2 : stonesOf false ((hist ++ [m]) ++ [r]) = stonesOf false hist ++ [r] := by
      rw [stonesOf_snoc_odd_false hlen', stonesOf_snoc_even_false hEven]
    have hp1 : (stonesOf true hist ++ [m]).toFinset = insert m (stonesOf true hist).toFinset := by
      ext x; simp [List.toFinset_append]
    have hp2 : (stonesOf false hist ++ [r]).toFinset = insert r (stonesOf false hist).toFinset := by
      ext x; simp [List.toFinset_append]
    have := ih r hr hlen''
    rwa [hs1, hs2, hp1, hp2] at this

/-- On every history extending `root`, with the first player's stones
in the box, `σ` takes a completion whenever there is one. -/
def TakesWinsOn (σ : Strategy) (box n : ℕ) (root : List Cell) : Prop :=
  ∀ tail : List Cell,
    (root ++ tail).length % 2 = 0 →
    (∀ x ∈ stonesOf true (root ++ tail), inBox box x = true) →
    (∀ x ∈ root ++ tail, x ∈ board n) →
    threatsL (squaresList n) (stonesOf true (root ++ tail)) (root ++ tail) ≠ [] →
    ∃ z, σ (squaresList n) (root ++ tail) = some z ∧
      z ∈ threatsL (squaresList n) (stonesOf true (root ++ tail)) (root ++ tail)

theorem TakesWinsOn.extend {σ : Strategy} {box n : ℕ} {root : List Cell}
    (h : TakesWinsOn σ box n root) (more : List Cell) :
    TakesWinsOn σ box n (root ++ more) := by
  intro tail
  rw [List.append_assoc]
  exact h (more ++ tail)

end SquareAchievement
