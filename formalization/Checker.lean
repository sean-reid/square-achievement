import SquareAchievement.Compute.Checker
import SquareAchievement.Compute.Refute
import SquareAchievement.Compute.Uniform
import SquareAchievement.Compute.ExactFarm
import SquareAchievement.Compute.Fast
import SquareAchievement.Data.TableGen
import SquareAchievement.Data.Table5

/-! Command-line entry: `lake exe checker <n> [five] [trace]` runs the
exhaustive verification of a generated table on the `n` board, or
extracts the first failing line. -/

open SquareAchievement

def main (args : List String) : IO Unit := do
  let n := (args.head?.bind String.toNat?).getD 6
  let table := if args.contains "five" then fiveTable else genTable
  let start ← IO.monoMsNow
  if args.contains "farmsafe" then
    let ok ← IO.lazyPure fun _ => anchorsValid table && farmSafe table
    let ms := (← IO.monoMsNow) - start
    IO.println s!"farm entries: {if ok then "SAFE" else "UNSAFE"} ({ms}ms)"
  else if args.contains "exactfarm" then
    let ok ← IO.lazyPure fun _ => exactFarmSafe table && classFarmSafe table
    let ms := (← IO.monoMsNow) - start
    IO.println s!"exact and class keys: {if ok then "FARM-SAFE" else "FARM-UNSAFE"} ({ms}ms)"
  else if args.contains "forced" then
    let ok ← IO.lazyPure fun _ => checkForced table n
    let ms := (← IO.monoMsNow) - start
    IO.println s!"n={n}: {if ok then "FORCED-PROVEN" else "FORCED-REFUTED"} ({ms}ms)"
  else if args.contains "refute" then
    let ok ← IO.lazyPure fun _ => refute n
    let ms := (← IO.monoMsNow) - start
    IO.println s!"n={n}: {if ok then "NO P1 WIN" else "unrefuted"} ({ms}ms)"
  else if args.contains "trace" then
    let fast := !(args.contains "slow" || args.contains "five")
    let line ← IO.lazyPure fun _ =>
      if fast then traceFast table n else trace table n
    let ms := (← IO.monoMsNow) - start
    match line with
    | none => IO.println s!"n={n}: PROVEN ({ms}ms)"
    | some hist => IO.println s!"n={n}: REFUTED ({ms}ms)\nline: {repr hist}"
  else
    -- the fast checker is fork-free; the five table has quiet forks
    let slow := args.contains "slow" || args.contains "five"
    let ok ← IO.lazyPure fun _ =>
      if slow then check table n else checkFast table n
    let ms := (← IO.monoMsNow) - start
    IO.println s!"n={n}: {if ok then "PROVEN" else "REFUTED"} ({ms}ms{if slow then ", slow" else ""})"
