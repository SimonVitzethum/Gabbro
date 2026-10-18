/-
  File:      Grammatik/Parser/Cover/MitgliederLauf.lean
  Subject:   The runner of `Mitglieder.lean` (a script: not imported by `Grammatik.lean`).

  Run (from `grammatik/`, after `lake build Grammatik.Parser.Cover.Mitglieder`):
    `lake env lean --run Grammatik/Parser/Cover/MitgliederLauf.lean REGISTER.tsv <dir>`
  Every `*.gab` of `<dir>` goes through the pure-Lean pipeline (lex, parse, elaborate, lower); the union of the
  members the lowered programs reach is compared with the coverage register (`dokumente/llvm-modelldeckung.tsv`,
  the members of the term types `Expr`/`Stmt`/`Block`/`Endblock`/`Arms`/`Args`/`Ty`/...). Prints how many sources
  lowered, the members reached with their source counts, and the register members not reached.
-/
import Grammatik.Parser.Cover.Mitglieder

namespace Gabbro.Grammatik.Parser.Cover.Mitglieder

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The members of one source, or `none` when the pipeline does not lower it. -/
def mitgliederVon (src : String) : Option (List String) :=
  match lex src with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u =>
        match lowerAllg u with
        | .error _ => none
        | .ok (P, fs) => some (mitglieder u P fs)

def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def run (args : List String) : IO Unit := do
  let reg ← IO.FS.readFile (args.headD "")
  let dir : System.FilePath := args.getD 1 "."
  let typen := ["Expr", "Stmt", "Block", "Endblock", "Arms", "Args", "Ty", "ErgExpr", "NutzlastExpr", "GrundArms"]
  let mitgl := (reg.splitOn "\n").filterMap fun z =>
    if z.startsWith "#" || z.isEmpty then none
    else match z.splitOn "\t" with
      | m :: _ => if typen.contains (m.splitOn ".").head! then some m else none
      | [] => none
  let entries ← dir.readDir
  let names := ((entries.map (·.fileName)).filter (·.endsWith ".gab")).qsort (· < ·)
  let mut zaehler : Array (String × Nat) := #[]
  let mut gesenkt := 0
  for n in names do
    let src ← IO.FS.readFile (dir / n)
    match mitgliederVon src with
    | none => pure ()
    | some ms =>
      gesenkt := gesenkt + 1
      for m in dedup ms do
        match zaehler.findIdx? (fun p => p.1 == m) with
        | some i => zaehler := zaehler.modify i (fun p => (p.1, p.2 + 1))
        | none => zaehler := zaehler.push (m, 1)
  IO.println s!"sources {names.size}, lowered to a G term {gesenkt}"
  let erreicht := mitgl.filter fun m => zaehler.any (·.1 == m)
  IO.println s!"register members reached: {erreicht.length} of {mitgl.length}"
  for (m, c) in zaehler.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {m}\t{c}"
  IO.println s!"not reached: {", ".intercalate (mitgl.filter fun m => !(zaehler.any (·.1 == m)))}"

end Gabbro.Grammatik.Parser.Cover.Mitglieder

def main (args : List String) : IO Unit := Gabbro.Grammatik.Parser.Cover.Mitglieder.run args
