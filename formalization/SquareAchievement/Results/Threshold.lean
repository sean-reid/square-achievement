import SquareAchievement.Compute.Refute
import SquareAchievement.Game.Outcome
import SquareAchievement.Results.Uniform
import SquareAchievement.Data.Table5

/-!
# The threshold theorems

The headline results. `small_board_no_win` rests on the refutation
certificates. `p1_wins_of_five_le` assembles from three ingredients:

* `n = 5`: its own certificate (the exact-solver table with quiet
  forks, replayed by the enumerating checker);
* `6 ≤ n < 17`: one forced-tree run per size;
* `17 ≤ n`: the run at the base board, lifted by
  `check_sound_uniform`.

`p1_wins_iff` states the theorem as an equivalence, and `outcome`
adds the draws: strategy stealing rules out a second-player win on
every board, determinacy turns the refutations into drawing
strategies, and the boards up to `4` are drawn in the full sense,
each player able to secure at least a draw.
-/

set_option linter.style.nativeDecide false

namespace SquareAchievement

theorem refute_one : refute 1 = true := by native_decide
theorem refute_two : refute 2 = true := by native_decide
theorem refute_three : refute 3 = true := by native_decide
theorem refute_four : refute 4 = true := by native_decide

theorem small_board_no_win {n : ℕ} (h : n ≤ 4) : ¬ P1CanWin n ∅ ∅ := by
  rcases n with _ | _ | _ | _ | _ | n
  · exact not_p1CanWin_zero
  · exact refute_sound refute_one
  · exact refute_sound refute_two
  · exact refute_sound refute_three
  · exact refute_sound refute_four
  · omega

/-- The `n = 5` case, from its own certificate: the exact-solver table
with quiet forks, replayed exhaustively inside Lean. -/
theorem p1_wins_five : P1CanWin 5 ∅ ∅ :=
  check_sound (t := fiveTable) (by native_decide)

/-- The forced-tree runs at every size from 6 below the base board,
one evaluation. -/
theorem forced_below_seventeen :
    ((List.range' 6 11).all fun n => checkForced genTable n) = true := by
  native_decide

theorem p1_wins_of_five_le {n : ℕ} (h : 5 ≤ n) : P1CanWin n ∅ ∅ := by
  rcases eq_or_lt_of_le h with h5 | h6
  · exact h5 ▸ p1_wins_five
  · rcases Nat.lt_or_ge n 17 with hlt | hge
    · refine checkForced_sound (t := genTable) ?_
      have hmem : n ∈ List.range' 6 11 := by
        rw [List.mem_range']
        exact ⟨n - 6, by omega, by omega⟩
      exact (List.all_eq_true.mp forced_below_seventeen) n hmem
    · exact check_sound_uniform hge rfl plan_confined forced_seventeen
        far_farm_safe_gen exact_farm_safe_gen far_near_farm_safe_gen
        x2_sane_gen

/-- Strategy stealing: the second player never forces a win. -/
theorem second_player_no_win (n : ℕ) : ¬ P2CanWin n ∅ ∅ :=
  fun h => (P1CanWin.of_p2CanWin h).not_p2CanWin h

/-- The main theorem: the first player forces a win exactly on the
boards of size at least five. -/
theorem p1_wins_iff {n : ℕ} : P1CanWin n ∅ ∅ ↔ 5 ≤ n :=
  ⟨fun h => by
    by_contra hlt
    exact small_board_no_win (by omega) h,
   p1_wins_of_five_le⟩

/-- Every board up to `4 × 4` is drawn under optimal play: each player
can secure at least a draw. -/
theorem small_board_drawn {n : ℕ} (h : n ≤ 4) :
    P1CanDraw n ∅ ∅ ∧ P2CanDraw n ∅ ∅ :=
  ⟨P1CanDraw.of_not_p2CanWin (second_player_no_win n),
   P2CanDraw.of_not_p1CanWin (small_board_no_win h)⟩

/-- The outcome of the game on every board: a first-player win from
size five up, a draw below. -/
theorem outcome (n : ℕ) :
    (P1CanWin n ∅ ∅ ↔ 5 ≤ n) ∧
      ((P1CanDraw n ∅ ∅ ∧ P2CanDraw n ∅ ∅) ↔ n ≤ 4) := by
  refine ⟨p1_wins_iff, fun ⟨_, h2⟩ => ?_, small_board_drawn⟩
  by_contra hlt
  exact (p1_wins_of_five_le (by omega)).not_p2CanDraw h2

end SquareAchievement
