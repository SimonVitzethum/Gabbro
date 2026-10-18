/-
  File:      Grammatik/Parser/Cover/DifferenzLauf.lean
  Subject:   The runner of `Differenz.lean` (a script: not imported by `Grammatik.lean`).

  Run (from `grammatik/`, after `lake build Grammatik.Parser.Cover.Differenz`):
    `lake env lean --run Grammatik/Parser/Cover/DifferenzLauf.lean [--komponenten] <dir>`
  prints `NAME<TAB>VERDICT` for every `*.gab` of `<dir>`; with `--komponenten` the ten components of
  `AkzeptiertX` as digits instead (see `Differenz.komponenten`).
-/
import Grammatik.Parser.Cover.Differenz

namespace Gabbro.Grammatik.Parser.Cover.Differenz

def run (args : List String) : IO Unit := do
  let zerlegen := args.headD "" == "--komponenten"
  let args := if zerlegen then args.tail else args
  let dir : System.FilePath := args.headD "."
  let entries ← dir.readDir
  let names := ((entries.map (·.fileName)).filter (·.endsWith ".gab")).qsort (· < ·)
  for n in names do
    let src ← IO.FS.readFile (dir / n)
    IO.println (n ++ "\t" ++ (if zerlegen then zerlegt src else verdict src))

end Gabbro.Grammatik.Parser.Cover.Differenz

def main (args : List String) : IO Unit := Gabbro.Grammatik.Parser.Cover.Differenz.run args
