import SquareAchievement.Compute.CheckerSound
import SquareAchievement.Data.TableGen

/-!
# The arbitrary-`n` step

The final theorem quantifies over every board size; computation can
only reach finitely many. This file carries the bridge:

* `check_sound` turns one successful checker run into a `P1CanWin`
  proof tree (the certificate step);
* `subsumption` lifts the run at the saturation bound `N₀` to every
  larger board.

`N₀` is provisional until the activity-radius instrumentation fixes it;
the subsumption hypotheses are executable predicates on the table so
each is later discharged by evaluation. The list is expected to grow
as the argument is formalized (class completeness, activity radius);
stating it now pins the proof's shape.
-/

namespace SquareAchievement

/-- Provisional saturation bound. -/
def N₀ : ℕ := 13

mutual
  /-- Every cell an entry can ever play lies inside the given box. -/
  def entryConfined (box : ℕ) : Entry → Bool
    | .plan cells => cells.all (onBoard box)
    | .quiet move branches => onBoard box move && branchesConfined box branches

  def branchesConfined (box : ℕ) : List (Key × Entry) → Bool
    | [] => true
    | (_, e) :: rest => entryConfined box e && branchesConfined box rest
end

/-- P1's plan never leaves the corner box: the opening, every second
move, and every cell any entry can play lie inside `board t.box`. -/
def planConfined (t : Table) : Bool :=
  onBoard t.box t.opening &&
  (t.x2.all fun e => onBoard t.box e.2) &&
  t.scripts.all fun e => e.2.all fun e2 => entryConfined t.box e2.2

/-- Subsumption: past the saturation bound, larger boards add cells but
no behaviorally new cells. Every extra cell is, relative to this
strategy, equivalent to its alignment-class representative on the `N₀`
board, so the one verified game tree covers them all. -/
theorem subsumption {n : ℕ} (hn : N₀ ≤ n)
    (hconf : planConfined genTable = true)
    (hchk : check genTable N₀ = true) :
    P1CanWin n ∅ ∅ := by
  sorry

end SquareAchievement
