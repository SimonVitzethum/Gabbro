/-
  File:      Grammatik/Gen/Abdeckung/ZellenEins.lean
  Subject:   The driver for ONE member per process:

               gen-zelle anzahl          -- prints the number of members
               gen-zelle I DIR           -- sweeps member I and writes DIR/m<I>.txt

             The bounds of a member are `grenzenVon` (here, not on the command line); `LAUF_VERTRAG=NC` sets the size of
             the contract variants (default 0), `LAUF_MODELL=1` the model-wide body tables. The members are run one
             after the other by a loop around this program; `gen-zellen-sammeln DIR` (`ZellenSammeln.lean`) reads the
             records. Printed sources go to DIR (single-fault programs) and DIR/kand (valid candidates).

             Record lines (tab separated): `Z valid single errors`, `G cell witness`, `B cell witness`, `X cell n`
             (masked), `S cell file` (printed single-fault), `Q file class`, `K stem cells ok|reason`, `R reason n`,
             `F form n`. Exit code 1 on a transcription error.
-/
import Grammatik.Gen.Abdeckung.ZellenBefund

namespace Gabbro.Grammatik.Gen

/-- The record of one member's sweep. -/
def Befund.zeilen (b : Befund) : List String :=
  let zeuge := fun (w : Nat × Nat × Nat) => s!"{w.1}:{w.2.1}:{w.2.2}"
  [s!"Z\t{b.gutProgramme}\t{b.schlechtProgramme}\t{b.falsch}"] ++
  b.gut.toList.map (fun (x, w) => s!"G\t{x.text}\t{zeuge w}") ++
  b.schlecht.toList.map (fun (x, w) => s!"B\t{x.text}\t{zeuge w}") ++
  b.maskiert.toList.map (fun (x, n) => s!"X\t{x.text}\t{n}") ++
  b.schlGedruckt.toList.map (fun (x, f) => s!"S\t{x.text}\t{f}") ++
  b.quellen.toList.map (fun (f, k, _) => s!"Q\t{f}\t{k}") ++
  b.kand.toList.map (fun (key, st, _, r, _) =>
    s!"K\t{st}\t{key}\t{match r with | .ok _ => "ok" | .error m => m}") ++
  b.grund.toList.map (fun (m, n) => s!"R\t{m}\t{n}") ++
  b.formen.toList.map (fun (m, n) => s!"F\t{m}\t{n}") ++
  b.lean.toList.map (fun (st, zs, r) =>
    s!"LG\t{st}\t{String.intercalate ";" (zs.map Zelle.text)}\t{match r with | .ok _ => "ok" | .error m => m}") ++
  b.leanN.toList.map (fun (x, st, r) => s!"LB\t{st}\t{x.text}\t{match r with | .ok _ => "ok" | .error m => m}")

end Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Gen

def main (args : List String) : IO UInt32 := do
  match args with
  | ["anzahl"] => IO.println mitglieder.length; return 0
  | [i, dir] =>
    let i := i.toNat!
    let z := mitglieder.getD i {}
    let (nb, kmax) := grenzenVon i
    let nc : Nat := ((← IO.getEnv "LAUF_VERTRAG").bind String.toNat?).getD 0
    let tbls := z.tabellenD nb (treu := (← IO.getEnv "LAUF_MODELL").isNone)
    let mut b : Befund := {}
    let t := ← IO.monoMsNow
    IO.FS.createDirAll (dir ++ "/kand")
    -- the record is rewritten after every size, so a run stopped by its time limit keeps what it found
    for k in List.range (kmax + 1) do
      if k ≥ 1 then
        b := z.sammle tbls i nb k nc b
        for (datei, _, text) in b.quellen do IO.FS.writeFile (dir ++ "/" ++ datei) text
        for (_, st, _, r, _) in b.kand.toList do
          match r with
          | .ok text => IO.FS.writeFile (dir ++ "/kand/" ++ st ++ ".gab") text
          | .error _ => pure ()
        IO.FS.createDirAll (dir ++ "/lean")
        for (st, _, r) in b.lean do
          match r with
          | .ok text => IO.FS.writeFile (dir ++ "/lean/" ++ st ++ ".lean") text
          | .error _ => pure ()
        for (_, st, r) in b.leanN.toList do
          match r with
          | .ok text => IO.FS.writeFile (dir ++ "/lean/" ++ st ++ ".lean") text
          | .error _ => pure ()
        IO.FS.writeFile (dir ++ s!"/m{i}.txt") (String.intercalate "\n" (b.zeilen ++ [s!"K-size\t{k}"]) ++ "\n")
    IO.println s!"member {i} ({nb}:{kmax}, contracts {nc}): valid {b.gutProgramme}, single-fault {b.schlechtProgramme}, good cells {b.gut.size}, isolated bad cells {b.schlecht.size}, errors {b.falsch} ({(← IO.monoMsNow) - t} ms)"
    return (if b.falsch == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: gen-zelle anzahl | gen-zelle I DIR"
    return 2
