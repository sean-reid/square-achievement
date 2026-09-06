import SquareAchievement.Compute.Checker
import SquareAchievement.Compute.Refute
import SquareAchievement.Compute.Uniform
import SquareAchievement.Five.Table5
import SquareAchievement.Plus.Anchors

/-! Command-line entry. `lake exe checker <n>` runs the certificate for
the `n` board: the refuter below 5, the exhaustive check of the `5 × 5`
table at 5, and the forced-tree checker on the plus rule from 6 up.
`lake exe checker anchors` runs the rule's three anchored far-pair
families, and `lake exe checker 5 trace` prints the first failing line
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

def main (args : List String) : IO Unit := do
  let start ← IO.monoMsNow
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
