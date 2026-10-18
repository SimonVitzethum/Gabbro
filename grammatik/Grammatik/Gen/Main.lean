/-
  File:      Grammatik/Gen/Main.lean
  Subject:   Generator, the driver. `lake env lean --run Grammatik/Gen/Main.lean OUT SEED N ZIEL VERSUCHE`
             builds N programs (seeds SEED .. SEED+N-1, frames in turn), writes `OUT/g<seed>.gab` with the
             model's expected result in `OUT/g<seed>.exp` for each program whose model run returns a value,
             and prints the per-constructor census (generated / accepted / in a final program). Constructors
             that were never generated or never accepted are listed: new syntax shows up as a gap, never
             silently.
-/
import Std.Data.HashMap
import Grammatik.Gen.Bau

namespace Gabbro.Grammatik.Gen

open Lean Meta Gabbro.Grammatik.Parser

/-- Number of values (by `Repr`) that mention each constructor. -/
def zaehle (cs : List Name) (vs : List String) : List (String × Nat) :=
  cs.map fun c => (kurzName c, (vs.filter (erwaehnt · c.toString)).length)

def reprs {α : Type} [Repr α] (xs : List α) : List String := xs.map (fun x => (reprStr x))

def lauf (out : String) (seed n ziel versuche : Nat) : MetaM Unit := do
  let k ← baueKontext ``SAnw
  let mut alleCtors : List Name := []
  for t in k.huelle do
    alleCtors := alleCtors ++ (← getConstInfoInduct t).ctors
  IO.FS.createDirAll out
  let mut alleR : List String := []
  let mut genR : List String := []
  let mut finalR : List String := []
  let mut gespeichert := 0
  let mut tries := 0
  let mut taken := 0
  let mut rt := 0
  let mut stop : Std.HashMap String Nat := {}
  for i in [0:n] do
    IO.setRandSeed (seed + i)
    let r := rahmen[i % rahmen.length]!
    let b ← baue k (i % rahmen.length) ziel versuche 100
    tries := tries + b.versuche
    taken := taken + b.stmts.length
    alleR := alleR ++ reprs b.alle
    genR := genR ++ reprs b.genommen
    for a in b.absagen do stop := stop.insert a (stop.getD a 0 + 1)
    match b.ergebnis with
    | .wert v =>
      let name := s!"{out}/g{seed + i}"
      IO.FS.writeFile (name ++ ".gab") (b.text r)
      IO.FS.writeFile (name ++ ".exp") s!"{v}\n"
      gespeichert := gespeichert + 1
      finalR := finalR ++ reprs b.stmts ++ [reprStr b.ender]
      let blk := SAnw.block b.stmts (some (.ret (some b.ender)))
      if rundlaufNormal blk then rt := rt + 1
      else IO.FS.writeFile (name ++ ".rundlauf") (reprStr blk ++ "\n")
    | _ => pure ()
  IO.println s!"programs {gespeichert}/{n}; candidates {tries}, accepted {taken}; print/parse round trip (to normal form) ok {rt}/{gespeichert}"
  IO.println "model refusals (stage message, count):"
  for (m, c) in (stop.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 12 do
    IO.println s!"  {c}\t{m}"
  IO.println "constructor census: name, generated, accepted, in final programs"
  let g := zaehle alleCtors alleR
  let a := zaehle alleCtors genR
  let f := zaehle alleCtors finalR
  for ((c, x), ((_, y), (_, z))) in g.zip (a.zip f) do
    IO.println s!"  {c}\t{x}\t{y}\t{z}"
  let luecken := (a.zip f).filterMap fun ((c, y), (_, z)) => if z == 0 then some (c, y) else none
  IO.println s!"constructors in no final program: {luecken.length} of {alleCtors.length}"


/-- `werte FILE`: the model's verdict on a source text (`refused: stage`, or the value `main` returns). -/
def werte (datei : String) : IO Unit := do
  let s ← IO.FS.readFile datei
  match lex s with
  | .error _ => IO.println "refused: lex"
  | .ok ts =>
    match pruefeLauf 100 (ts.filter fun t => match t with | .ende => false | _ => true) with
    | .error e => IO.println s!"refused: {e}"
    | .ok r => IO.println r.text

end Gabbro.Grammatik.Gen

open Lean Gabbro.Grammatik.Gen in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["werte", datei] => werte datei; return 0
  | [out, seed, n, ziel, versuche] =>
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Grammatik.Gen.Bau }] {} 0
    let x : MetaM Unit := lauf out seed.toNat! n.toNat! ziel.toNat! versuche.toNat!
    let _ ← (x.run' {} {}).toIO { fileName := "<gen>", fileMap := default, maxHeartbeats := 0 } { env := env }
    return 0
  | _ =>
    IO.eprintln "usage: Main.lean OUT SEED N ZIEL VERSUCHE | werte FILE"
    return 2
