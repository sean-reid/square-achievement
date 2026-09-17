import SquareAchievement.Compute.Checker
import SquareAchievement.Compute.Refute
import SquareAchievement.Compute.Uniform
import SquareAchievement.Five.Table5
import SquareAchievement.Plus.Anchors

/-! Command-line entry. `lake exe checker <n>` runs the certificate for
the `n` board: the refuter below 5, the exhaustive check of the `5 × 5`
table at 5, and the forced-tree checker on the plus rule from 6 up.
`lake exe checker anchors` runs the rule's three anchored far-pair
families, `lake exe checker lines` prints the line the rule commits to
after every reply pair of the `6 × 6` board and at every anchored
position, and `lake exe checker 5 trace` prints the first failing line
of the `5 × 5` table instead of a verdict. -/

open SquareAchievement

/-- The plus rule's three anchored families, iterated from `lo`
instead of `0` so that the compiler evaluates them at the call rather
than at program start; `lo = 0` is the certificate. -/
def plusAnchors (lo : Nat) : Bool :=
  let cells := (List.range Plus.box).drop lo
  (cells.all fun h1 => cells.all fun h2 =>
    Plus.anchorRun (h1 + 17, h2 + 17) (h1 + 17, h2) (h1, h2)) &&
  (cells.all fun a => (List.range 17).all fun w => cells.all fun h =>
    if 2 * Plus.box ≤ w && 17 ≤ a + w - h then
      Plus.anchorRun (a, w) (a + w - h, w) (a, h) &&
        Plus.anchorRun (w, a) (w, a + w - h) (h, a) &&
        Plus.anchorRun (a + w - h, w) (a, w) (a, h) &&
        Plus.anchorRun (w, a + w - h) (w, a) (h, a)
    else true)

/-- A line as `r c r c ...`, or `none`. -/
def lineText : Option (List Cell) → String
  | none => "none"
  | some line => " ".intercalate (line.map fun c => s!"{c.1} {c.2}")

/-- The position after the reply pair `o1`, `o2` and the line the rule
commits to on its abstraction: `tag o1r o1c o2r o2c x2r x2c : line`,
where `tag` is `6` for a pair of the `6 × 6` board and `anchor h1 h2`
for an anchored position with hidden corner `(h1, h2)`. -/
def positionLine (anchored : Bool) (o1 o2 : Cell) : String :=
  let x2 := Plus.secondMove o1
  let a := Plus.abstractOf [Plus.opening, o1, x2, o2]
  let tag := if anchored then
      match a.hot with
      | some h => s!"anchor {h.1} {h.2}"
      | none => "anchor - -"
    else "6"
  s!"{tag} {o1.1} {o1.2} {o2.1} {o2.2} {x2.1} {x2.2} : {lineText (Plus.lineOf a)}"

/-- Every reply pair of the `6 × 6` board in cell order, then the
anchored positions in the order `plusAnchors` visits them. -/
def linePositions : List (Bool × Cell × Cell) :=
  let cells := allCells 6
  let pairs := cells.flatMap fun o1 =>
    if o1 = Plus.opening then []
    else
      let x2 := Plus.secondMove o1
      cells.filterMap fun o2 =>
        if o2 = Plus.opening ∨ o2 = o1 ∨ o2 = x2 then none else some (false, o1, o2)
  let box := List.range Plus.box
  let far := box.flatMap fun h1 => box.map fun h2 =>
    (true, (h1 + 17, h2 + 17), (h1 + 17, h2))
  let aligned := box.flatMap fun a => (List.range 17).flatMap fun w => box.flatMap fun h =>
    if 2 * Plus.box ≤ w && 17 ≤ a + w - h then
      [(true, (a, w), (a + w - h, w)), (true, (w, a), (w, a + w - h)),
        (true, (a + w - h, w), (a, w)), (true, (w, a + w - h), (w, a))]
    else []
  pairs ++ far ++ aligned

def main (args : List String) : IO Unit := do
  let start ← IO.monoMsNow
  if args.contains "lines" then
    for (anchored, o1, o2) in linePositions do
      IO.println (positionLine anchored o1 o2)
    return
  if args.contains "anchors" then
    let lo := args.length - args.length
    let ok ← IO.lazyPure fun _ => plusAnchors lo
    let ms := (← IO.monoMsNow) - start
    let verdict := if ok then "SAFE" else "UNSAFE"
    IO.println s!"plus rule, anchored pairs: {verdict} ({ms}ms)"
    return
  let n := (args.head?.bind String.toNat?).getD 6
  if n ≤ 4 then
    let ok ← IO.lazyPure fun _ => refute n
    let ms := (← IO.monoMsNow) - start
    IO.println s!"n={n}: {if ok then "NO P1 WIN" else "unrefuted"} ({ms}ms)"
  else if n == 5 then
    if args.contains "trace" then
      let line ← IO.lazyPure fun _ => trace fiveTable 5
      let ms := (← IO.monoMsNow) - start
      match line with
      | none => IO.println s!"n=5: PROVEN ({ms}ms)"
      | some hist => IO.println s!"n=5: REFUTED ({ms}ms)\nline: {repr hist}"
    else
      let ok ← IO.lazyPure fun _ => check fiveTable 5
      let ms := (← IO.monoMsNow) - start
      IO.println s!"n=5: {if ok then "PROVEN" else "REFUTED"} ({ms}ms, 5 × 5 table)"
  else
    let ok ← IO.lazyPure fun _ => checkForcedS Plus.plusMove Plus.box n
    let ms := (← IO.monoMsNow) - start
    let verdict := if ok then "FORCED-PROVEN" else "FORCED-REFUTED"
    IO.println s!"n={n}: {verdict} ({ms}ms, plus rule)"
