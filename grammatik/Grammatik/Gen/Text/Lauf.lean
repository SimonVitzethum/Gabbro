/-
  File:      Grammatik/Gen/Text/Lauf.lean
  Subject:   The driver `gen-text` (untrusted, a measurement): for the members `A ..< B`, every program the generator
             emits up to size `K` (`Spez.erzeugtL` over `tabellenD`), and whether its printed text reads back as a
             program with the same cells and the same verdict (`textCheck`). The failures are counted by their reason,
             so the forms the printer or the front end still lacks are named.

               gen-text A B K NC [NB]   (NB caps the body bound of the members)
-/
import Grammatik.Gen.Text.Pruefung
import Grammatik.Gen.Abdeckung.Satz.ErzeugtMN
import Std.Data.HashMap

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Gen.Text Gabbro.Grammatik.Parser

/-- Why a program's text does not read back: the delaborator's message, the printability check, the front end's
    message, or a difference in cells or verdict. -/
def grund (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) (e : Einsatz) : Option String :=
  match delab z P ws with
  | .error m => some s!"delab: {m}"
  | .ok its =>
    if !itemsGutB its then some "not printable (itemsGutB)"
    else match ausItems its with
      | .error m => some s!"front end: {(m.take 90).toString}"
      | .ok e' =>
        if e'.zellen != e.zellen then some "cells differ"
        else if e'.gueltig != e.gueltig then some "verdict differs"
        else none

def main (args : List String) : IO UInt32 := do
  let a := args[0]!.toNat!; let b := args[1]!.toNat!; let kmax := args[2]!.toNat!; let nc := args[3]!.toNat!
  let nbMax := (args[4]?.bind String.toNat?).getD 1000
  let mut tally : Std.HashMap String Nat := {}
  let mut gesamt := 0
  let mut gut := 0
  for i in List.range' a (b - a) do
    let z := mitglieder.getD i {}
    let tb := z.tabellenD (min (grenzenVon i).1 nbMax)
    for k in List.range (kmax + 1) do
      for x in z.erzeugtL tb nc k do
        let (P, ws, e) := match x with
          | .gut g => (g.prog, g.ws, z.einsatz g.prog g.ws g.ohneAx g.boden)
          | .abgelehnt r => (r.prog, r.ws, z.einsatz r.prog r.ws r.ohneAx r.boden)
        gesamt := gesamt + 1
        match grund z P ws e with
        | none => gut := gut + 1
        | some m => tally := tally.insert m (tally.getD m 0 + 1)
    IO.eprintln s!"member {i}: {gesamt} programs so far, {gut} read back"
    IO.FS.writeFile s!"tally-{a}.txt" (String.intercalate "\n" ((tally.toList.toArray.qsort (fun x y => x.2 > y.2)).toList.map fun (m, n) => s!"{n}\t{m}") ++ s!"\n# {gesamt} {gut}\n")
  IO.println s!"{gesamt} programs, {gut} read back with the same cells and verdict"
  for (m, n) in tally.toList.toArray.qsort (fun x y => x.2 > y.2) do IO.println s!"{n}\t{m}"
  return 0
