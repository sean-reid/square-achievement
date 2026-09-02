import SquareAchievement.Game.Rules

/-!
# Outcomes

`P1CanWin n A B` reads as "the player to move, holding `A` against
`B`, forces a win", so the other outcomes are built from it by
swapping roles after a move. `P2CanWin` says the opponent of the
player to move forces a win; `P1CanDraw` says the player to move can
secure at least a draw, its derivations being strategy trees whose
branches end in a win for the mover or a full board; `P2CanDraw` is
the same for the opponent.

Two general facts connect them. Strategy stealing: whenever the second
player forces a win from the empty board, so does the first, hence the
second player never does. Determinacy: from every position, either the
player to move forces a win or the opponent can secure a draw. With
the refutations on the boards up to `4`, these make "drawn under
optimal play" a theorem rather than a remark.

Positions in which a player already holds a square are unreachable
from the empty board, since a game ends at its first square, so all
four predicates are read on square-free positions; there `P1CanWin`
and its derivatives coincide with the usual game-theoretic notions.
-/

theorem empties_comm {n : ℕ} {A B : Finset Cell} :
    empties n A B = empties n B A := by
  simp [empties, Finset.union_comm]

theorem empties_insert_left_eq {n : ℕ} {A B : Finset Cell} {x : Cell} :
    empties n (insert x A) B = empties n A (insert x B) := by
  simp [empties, Finset.insert_union, Finset.union_insert]

theorem empties_anti_left {n : ℕ} {A A' B : Finset Cell} (h : A ⊆ A') :
    empties n A' B ⊆ empties n A B := by
  intro y hy
  rw [mem_empties] at hy ⊢
  exact ⟨hy.1, fun hyA => hy.2.1 (h hyA), hy.2.2⟩

/-- The opponent of the player to move forces a win: there is a move,
and every move completes nothing and leaves the opponent a winning
position. -/
def P2CanWin (n : ℕ) (A B : Finset Cell) : Prop :=
  (empties n A B).Nonempty ∧
    ∀ m ∈ empties n A B, ¬ HasSquare (insert m A) ∧ P1CanWin n B (insert m A)

/-- The player to move can secure at least a draw. -/
inductive P1CanDraw (n : ℕ) : Finset Cell → Finset Cell → Prop
  /-- No move is left; the game is over. -/
  | full {A B : Finset Cell} (h : empties n A B = ∅) : P1CanDraw n A B
  /-- The mover completes a square right now. -/
  | now {A B : Finset Cell} (m : Cell) (hm : m ∈ empties n A B)
      (hwin : HasSquare (insert m A)) : P1CanDraw n A B
  /-- The mover plays `m`; every reply completes nothing and leaves a
  position the mover still holds. -/
  | step {A B : Finset Cell} (m : Cell) (hm : m ∈ empties n A B)
      (hsafe : ∀ r ∈ empties n (insert m A) B, ¬ HasSquare (insert r B))
      (hnext : ∀ r ∈ empties n (insert m A) B,
        P1CanDraw n (insert m A) (insert r B)) :
      P1CanDraw n A B

/-- The opponent of the player to move can secure at least a draw. -/
def P2CanDraw (n : ℕ) (A B : Finset Cell) : Prop :=
  ∀ m ∈ empties n A B, ¬ HasSquare (insert m A) ∧ P1CanDraw n B (insert m A)

/-- Surplus stones never hurt: a winning mover still wins with one
more stone, unless that stone already completes a square. When the
strategy calls for the occupied cell, any move stands in for it. -/
theorem P1CanWin.insert_left {n : ℕ} : ∀ {A B : Finset Cell},
    P1CanWin n A B → ∀ {x : Cell}, x ∉ B →
      HasSquare (insert x A) ∨ P1CanWin n (insert x A) B := by
  intro A B h
  induction h with
  | now m hm hwin =>
    intro x hx
    by_cases hxm : x = m
    · exact Or.inl (hxm ▸ hwin)
    · right
      refine P1CanWin.now m ?_
        (hwin.mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      rw [mem_empties] at hm ⊢
      refine ⟨hm.1, ?_, hm.2.2⟩
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hxm h.symm, hm.2.1⟩
  | @step A B m hm hne hsafe hwins ih =>
    intro x hx
    right
    by_cases hxm : x = m
    · subst hxm
      obtain ⟨m', hm'⟩ := hne
      by_cases hw : HasSquare (insert m' (insert x A))
      · exact P1CanWin.now m' hm' hw
      · refine P1CanWin.step m' hm' ?_ ?_ ?_
        · have := (hwins m' hm').nonempty_empties
          rwa [← empties_insert_left_eq] at this
        · intro r hr
          exact hsafe r (empties_anti_left (Finset.subset_insert _ _) hr)
        · intro r hr
          have hr' : r ∈ empties n (insert x A) B :=
            empties_anti_left (Finset.subset_insert _ _) hr
          have hm'r : m' ∉ insert r B := by
            rw [Finset.mem_insert, not_or]
            refine ⟨fun h => ?_, (mem_empties.mp hm').2.2⟩
            subst h
            exact (mem_empties.mp hr).2.1 (Finset.mem_insert_self _ _)
          rcases ih r hr' hm'r with h | h
          · exact absurd h hw
          · exact h
    · have hm' : m ∈ empties n (insert x A) B := by
        rw [mem_empties] at hm ⊢
        refine ⟨hm.1, ?_, hm.2.2⟩
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => hxm h.symm, hm.2.1⟩
      by_cases hw : HasSquare (insert m (insert x A))
      · exact P1CanWin.now m hm' hw
      · refine P1CanWin.step m hm' ?_ ?_ ?_
        · by_cases hxe : x ∈ empties n (insert m A) B
          · have := (hwins x hxe).nonempty_empties
            rwa [← empties_insert_left_eq, Finset.insert_comm] at this
          · obtain ⟨y, hy⟩ := hne
            refine ⟨y, ?_⟩
            have hyx : y ≠ x := fun hyx => hxe (by rw [← hyx]; exact hy)
            rw [mem_empties] at hy ⊢
            refine ⟨hy.1, ?_, hy.2.2⟩
            intro hmem
            rw [Finset.mem_insert, Finset.mem_insert] at hmem
            rcases hmem with hym | hyx' | hyA
            · exact hy.2.1 (hym ▸ Finset.mem_insert_self _ _)
            · exact hyx hyx'
            · exact hy.2.1 (Finset.mem_insert_of_mem hyA)
        · intro r hr
          exact hsafe r (empties_anti_left
            (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hr)
        · intro r hr
          have hr' : r ∈ empties n (insert m A) B :=
            empties_anti_left
              (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hr
          have hxr : x ∉ insert r B := by
            rw [Finset.mem_insert, not_or]
            refine ⟨fun h => ?_, hx⟩
            subst h
            exact (mem_empties.mp hr).2.1
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          rcases ih r hr' hxr with h | h
          · rw [Finset.insert_comm] at h
            exact absurd h hw
          · rw [Finset.insert_comm] at h
            exact h

/-- Strategy stealing: a second-player win from the empty board hands
the first player one. The first player opens anywhere and then plays
the second player's strategy against the reply, the extra stone never
hurting by `P1CanWin.insert_left`. -/
theorem P1CanWin.of_p2CanWin {n : ℕ} (h : P2CanWin n ∅ ∅) : P1CanWin n ∅ ∅ := by
  obtain ⟨⟨m0, hm0⟩, hall⟩ := h
  have hone : ∀ c : Cell, ¬ HasSquare (insert c ∅) := fun c =>
    not_hasSquare_of_card_lt (by simp)
  refine P1CanWin.step m0 hm0 ?_ (fun r _ => hone r) ?_
  · have := (hall m0 hm0).2.nonempty_empties
    rwa [empties_comm] at this
  · intro r hr
    have hr' : r ∈ empties n ∅ ∅ :=
      empties_anti_left (Finset.empty_subset _) hr
    have hm0r : m0 ∉ insert r (∅ : Finset Cell) := by
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => ?_, Finset.notMem_empty _⟩
      subst h
      exact (mem_empties.mp hr).2.1 (Finset.mem_insert_self _ _)
    rcases (hall r hr').2.insert_left hm0r with h | h
    · exact absurd h (hone m0)
    · exact h

/-- Both players cannot force a win from one position. -/
theorem P1CanWin.not_p2CanWin {n : ℕ} {A B : Finset Cell}
    (h : P1CanWin n A B) : ¬ P2CanWin n A B := by
  induction h with
  | now m hm hwin =>
    rintro ⟨-, hall⟩
    exact (hall m hm).1 hwin
  | step m hm hne hsafe hwins ih =>
    rintro ⟨-, hall⟩
    obtain ⟨-, hopp⟩ := hall m hm
    cases hopp with
    | now r hr hw =>
      rw [empties_comm] at hr
      exact hsafe r hr hw
    | step r hr hne' hsafe' hwins' =>
      rw [empties_comm] at hr hne'
      refine ih r hr ⟨hne', fun m' hm' => ?_⟩
      rw [empties_comm] at hm'
      exact ⟨hsafe' m' hm', hwins' m' hm'⟩

/-- A player who forces a win denies the opponent even a draw. -/
theorem P1CanWin.not_p2CanDraw {n : ℕ} {A B : Finset Cell}
    (h : P1CanWin n A B) : ¬ P2CanDraw n A B := by
  induction h with
  | now m hm hwin =>
    intro hall
    exact (hall m hm).1 hwin
  | step m hm hne hsafe hwins ih =>
    intro hall
    obtain ⟨-, hd⟩ := hall m hm
    cases hd with
    | full hfull =>
      rw [empties_comm] at hfull
      exact hne.ne_empty hfull
    | now r hr hw =>
      rw [empties_comm] at hr
      exact hsafe r hr hw
    | step r hr hsafe' hnext =>
      rw [empties_comm] at hr
      refine ih r hr fun m' hm' => ?_
      rw [empties_comm] at hm'
      exact ⟨hsafe' m' hm', hnext m' hm'⟩

/-- Determinacy: from every position, the player to move forces a win
or the opponent can secure a draw. Induction on the number of empty
cells, classical in the case split. -/
theorem P1CanWin.or_p2CanDraw {n : ℕ} (A B : Finset Cell) :
    P1CanWin n A B ∨ P2CanDraw n A B := by
  generalize hk : (empties n A B).card = k
  induction k using Nat.strong_induction_on generalizing A B with
  | _ k ih =>
  by_cases hwin : P1CanWin n A B
  · exact Or.inl hwin
  right
  intro m hm
  have hnot : ¬ HasSquare (insert m A) := fun hw => hwin (.now m hm hw)
  refine ⟨hnot, ?_⟩
  by_cases hfull : empties n (insert m A) B = ∅
  · rw [empties_comm] at hfull
    exact .full hfull
  have hne : (empties n (insert m A) B).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hfull
  by_cases hsafe : ∀ r ∈ empties n (insert m A) B, ¬ HasSquare (insert r B)
  · have hex : ∃ r ∈ empties n (insert m A) B,
        ¬ P1CanWin n (insert m A) (insert r B) := by
      by_contra hcon
      exact hwin (.step m hm hne hsafe fun r hr =>
        Classical.byContradiction fun hnr => hcon ⟨r, hr, hnr⟩)
    obtain ⟨r, hr, hnr⟩ := hex
    have hcard : (empties n (insert m A) (insert r B)).card < k := by
      rw [← hk]
      exact (card_empties_insert_right_lt hr).trans
        (card_empties_insert_left_lt hm)
    rcases ih _ hcard (insert m A) (insert r B) rfl with h | h
    · exact absurd h hnr
    · rw [empties_comm] at hr
      refine .step r hr (fun m' hm' => ?_) (fun m' hm' => ?_)
      · rw [empties_comm] at hm'
        exact (h m' hm').1
      · rw [empties_comm] at hm'
        exact (h m' hm').2
  · have hex : ∃ r ∈ empties n (insert m A) B, HasSquare (insert r B) := by
      by_contra hcon
      exact hsafe fun r hr hw => hcon ⟨r, hr, hw⟩
    obtain ⟨r, hr, hw⟩ := hex
    rw [empties_comm] at hr
    exact .now r hr hw

/-- The opponent of a player who cannot force a win can secure a
draw. -/
theorem P2CanDraw.of_not_p1CanWin {n : ℕ} {A B : Finset Cell}
    (h : ¬ P1CanWin n A B) : P2CanDraw n A B :=
  (P1CanWin.or_p2CanDraw A B).resolve_left h

/-- A player whose opponent cannot force a win can secure a draw. -/
theorem P1CanDraw.of_not_p2CanWin {n : ℕ} {A B : Finset Cell}
    (h : ¬ P2CanWin n A B) : P1CanDraw n A B := by
  by_cases hfull : empties n A B = ∅
  · exact .full hfull
  have hne : (empties n A B).Nonempty := Finset.nonempty_iff_ne_empty.mpr hfull
  have hex : ∃ m ∈ empties n A B,
      ¬ (¬ HasSquare (insert m A) ∧ P1CanWin n B (insert m A)) := by
    by_contra hcon
    exact h ⟨hne, fun m hm =>
      Classical.byContradiction fun hk => hcon ⟨m, hm, hk⟩⟩
  obtain ⟨m, hm, hmk⟩ := hex
  by_cases hw : HasSquare (insert m A)
  · exact .now m hm hw
  have hnw : ¬ P1CanWin n B (insert m A) := fun h' => hmk ⟨hw, h'⟩
  have hd := P2CanDraw.of_not_p1CanWin hnw
  refine .step m hm (fun r hr => ?_) (fun r hr => ?_)
  · rw [empties_comm] at hr
    exact (hd r hr).1
  · rw [empties_comm] at hr
    exact (hd r hr).2
