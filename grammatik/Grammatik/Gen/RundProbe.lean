import Grammatik.Parser.Elab.UebersetzePipeline
import Std.Data.HashMap
open Gabbro.Grammatik

def main (args : List String) : IO UInt32 := do
  let mut tally : Std.HashMap String Nat := {}
  let mut n := 0
  for d in args do
    for e in (← System.FilePath.readDir d) do
      if e.fileName.endsWith ".gab" then
        n := n + 1
        let s ← IO.FS.readFile e.path
        let r := match uebersetzeAllg s with
          | .ok _ => "ok"
          | .error m => (m.take 70).toString
        tally := tally.insert r (tally.getD r 0 + 1)
  IO.println s!"{n} texts"
  for (k, v) in tally.toList.toArray.qsort (fun a b => a.2 > b.2) do IO.println s!"{v}\t{k}"
  return 0
