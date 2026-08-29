import SquareAchievement.Compute.Checker

/-!
# Executable properties for the uniform theorem

The strengthened soundness argument at the generation board needs
facts about the verification tree beyond winning. First, after the
opening and the second move, every strategy move either wins or
creates a threat, so the opponent's only unforced replies are the
first two; that is what keeps far play down to the two reply stones
and rules out voluntary grabs of a farm cell mid-plan. Second, branch
subtrees can be re-verified from preset openings on larger boards,
which anchors the farm entries that no run at the generation board
exercises. Both are checker variants, decided by evaluation.
-/

namespace SquareAchievement

/-- `go`, additionally demanding that every strategy move past the
second either wins or creates a threat. -/
def goForcing (t : Table) (squares : List (List Cell)) (n : ℕ) :
    ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match strategyMove t squares hist with
    | none => false
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then false
      else if hasSquareL squares (m :: p1) then true
      else if 2 < hist.length
          && (minThreat squares (m :: p1) ((m :: p1) ++ p2)).isNone then
        false
      else
        let hist' := hist ++ [m]
        let replies := (allCells n).filter fun c => !(hist'.contains c)
        if replies.isEmpty then false
        else replies.all fun r =>
          !completesL squares p2 r && goForcing t squares n fuel (hist' ++ [r])

/-- Every strategy move past the second wins or threatens, over the
whole verification tree of the `n` board. -/
def forcingComplete (t : Table) (n : ℕ) : Bool :=
  goForcing t (squaresList n) n (n * n + 1) []

/-- The checker from a preset history, for anchoring branch subtrees
on boards larger than the generation board. -/
def checkFrom (t : Table) (n : ℕ) (opening : List Cell) : Bool :=
  go t (squaresList n) n (n * n + 1) opening

/-- Every cell where `mine` would complete a square, unblocked, one
entry per square. -/
def threatsL (squares : List (List Cell)) (mine occupied : List Cell) :
    List Cell :=
  squares.filterMap fun sq =>
    match sq.filter (fun x => !mine.contains x) with
    | [m] => if occupied.contains m then none else some m
    | _ => none

/-- `goForcing` that additionally refuses any node where the opponent
is forced onto `hot`: with `hot` the only available block, the block
would complete three corners of the pair's farm square. A node where
`hot` is one block among several is safe, because a second threat
means the win reflex finishes before the farm matters. -/
def goFarmSafe (t : Table) (squares : List (List Cell)) (n : ℕ)
    (hot : Cell) : ℕ → List Cell → Bool
  | 0, _ => false
  | fuel + 1, hist =>
    let p1 := stonesOf true hist
    let p2 := stonesOf false hist
    match strategyMove t squares hist with
    | none => false
    | some m =>
      if !onBoard n m || p1.contains m || p2.contains m then false
      else if hasSquareL squares (m :: p1) then true
      else
        let ths := threatsL squares (m :: p1) ((m :: p1) ++ p2)
        if 2 < hist.length && ths.isEmpty then false
        else if !ths.isEmpty && ths.all (· == hot) then false
        else
          let hist' := hist ++ [m]
          let replies := (allCells n).filter fun c => !(hist'.contains c)
          if replies.isEmpty then false
          else replies.all fun r =>
            !completesL squares p2 r &&
              goFarmSafe t squares n hot fuel (hist' ++ [r])

/-- The board every anchor pair fits on. -/
def anchorBoard : ℕ := 23

/-- A concrete far pair whose farm cell is `hot`, in the branch keyed
`k`, placed just past the exact keys so lookup resolves through the
branch and the farm entry. A generic exact first reply gets no
anchor: no abstract partner farms with it, since the aligned member
of a farming pair would land on the generation board, so the farm
keys its aliased table carries are unreachable under that branch. -/
def anchorPair (k : Key) (hot : Cell) : Option (Cell × Cell) :=
  match k with
  | .row a => some ((a, 16), (a + 16 - hot.2, 16))
  | .col b => some ((16, b), (16, b + 16 - hot.1))
  | .dflt => some ((hot.1 + 17 - hot.2, 17), (hot.1 + 17 - hot.2, hot.2))
  | .cell c =>
    if c.1 < 6 then some (c, (c.1 + c.2 - hot.2, c.2))
    else if c.2 < 6 then some (c, (c.1, c.2 + c.1 - hot.1))
    else none
  | .farm _ => none

/-- Every anchor pair reproduces its farm cell through `farmKey`; a
formula error here fails the evaluation rather than anchoring the
wrong entry. -/
def anchorsValid (t : Table) : Bool :=
  t.scripts.all fun kt =>
    kt.2.all fun e =>
      match e.1 with
      | .farm hot =>
        match anchorPair kt.1 hot with
        | none => true
        | some (o1, o2) => farmKey t.box o1 o2 == some (.farm hot)
      | _ => true

/-- Every farm entry, anchored by a concrete far pair on the anchor
board, wins its subtree without ever forcing the opponent onto the
farm cell. -/
def farmSafe (t : Table) : Bool :=
  let n := anchorBoard
  let squares := squaresList n
  t.scripts.all fun kt =>
    kt.2.all fun e =>
      match e.1 with
      | .farm hot =>
        match anchorPair kt.1 hot with
        | none => true
        | some (o1, o2) =>
          farmKey t.box o1 o2 == some (.farm hot) &&
            (match lookup t.box t.x2 o1 with
             | none => false
             | some x2 =>
               goFarmSafe t squares n hot (n * n + 1)
                 [t.opening, o1, x2, o2])
      | _ => true

end SquareAchievement
