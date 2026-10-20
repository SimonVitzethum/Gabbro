/-
  File:      Grammatik/Gen/Abdeckung/ZellenLauf.lean
  Subject:   The DRIVER that measures the CELLS (`Zellen.lean`) of the programs the PROVEN generator emits:

               gen-zellen NB KMAX [I:NB:KMAX ...]

             For every member of the family (`mitglieder`: the sixteen of `Familie.lean` and those of `ZellFamilie.lean`),
             every size 1 .. `KMAX`, and every lock family and list of starts of `Spez.parameter`, it takes the programs
             of `Spez.erzeuge` (`Waehlen.lean`). That generator emits a program ONLY together with the proof of its class
             -- `Gutes` (the Lean model's Bool accepts it) or `Schlechtes c` (exactly component `c` refuses it) -- so
             validity is established in the generator and nothing is checked afterwards. The only oracle is the Lean
             model's own Bool; no Rust checker is consulted.

             Per cell it keeps the first witness: a GOOD cell (its test holds) needs a `Gutes` program that has it; a BAD
             cell (its test fails) needs a `Schlechtes c` program, `c` the cell's component, that has it. It also runs
             `zellenStimmen` (the transcription of the cells against `komp`) on every program emitted.

             Exit code 1 if `zellenStimmen` is false on any program (a transcription error), 0 otherwise.
-/
import Std.Data.HashMap
import Grammatik.Gen.Abdeckung.Waehlen
import Grammatik.Gen.Druck.Einheit

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- What the sweep has seen. A witness is (member, bodies bound, size). -/
structure Befund where
  /-- good cell -> a VALID program (`Gutes`) that has it -/
  gut : Std.HashMap Zelle (Nat × Nat × Nat) := {}
  /-- bad cell -> a program refused by exactly the cell's component (`Schlechtes`) that has it -/
  schlecht : Std.HashMap Zelle (Nat × Nat × Nat) := {}
  /-- the register members (constructors) the VALID programs use, with the number of programs -/
  formen : Std.HashMap String Nat := {}
  /-- cells with a PRINTED witness (good: a valid program; bad: a program refused by exactly the cell's component) -/
  gutGedruckt : Std.HashMap Zelle String := {}
  schlGedruckt : Std.HashMap Zelle String := {}
  /-- the printed programs: file name, class text, source -/
  quellen : Array (String × String × String) := #[]
  /-- why a program could not be printed, with the number of programs -/
  grund : Std.HashMap String Nat := {}
  gutProgramme : Nat := 0
  schlechtProgramme : Nat := 0
  falsch : Nat := 0
  beispiel : Option String := none

/-- The cells of the program of an emitted value, under its lock family and starts. -/
def Spez.zellenVon (z : Spez) (h : Haut z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) :
    List Zelle :=
  letI : Zahlen := z.zahlen
  (List.finRange 10).flatMap (zellen h.programm S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon h ws))

/-- The self-check of the transcription on one program. -/
def Spez.stimmt (z : Spez) (h : Haut z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) : Bool :=
  letI : Zahlen := z.zahlen
  zellenStimmen h.programm S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon h ws)

/-- Print a program once, record it under `datei` and mark the `neu` cells as printed. -/
def Befund.druck (b : Befund) (z : Spez) (h : Haut z.deklaration) (ws : List z.deklaration.Fn) (datei klasse : String)
    (neu : List Zelle) (gut : Bool) : Befund :=
  match z.quelltext h ws (String.ofList (datei.toList.take (datei.length - 4))) with
  | .ok text =>
    let b := { b with quellen := b.quellen.push (datei, klasse, text) }
    if gut then neu.foldl (fun b x => { b with gutGedruckt := b.gutGedruckt.insert x datei }) b
    else neu.foldl (fun b x => { b with schlGedruckt := b.schlGedruckt.insert x datei }) b
  | .error m => { b with grund := b.grund.insert m (b.grund.getD m 0 + 1) }

/-- Take one emitted program. -/
def Befund.nimm (b : Befund) (i nb k : Nat) (z : Spez) (e : Erzeugt z) : Befund :=
  let (h, S, ws, art) : Haut z.deklaration × SperrInv z.deklaration × List z.deklaration.Fn × Option (Fin 10) :=
    match e with
    | .gut g => (g.haut, g.S, g.ws, none)
    | .schlecht c s => (s.haut, s.S, s.ws, some c)
  let zs := z.zellenVon h S ws
  let b := if z.stimmt h S ws then b else
    { b with falsch := b.falsch + 1, beispiel := b.beispiel.orElse fun _ => some s!"member {i} size {k}" }
  match art with
  | none =>
    let b := (dedupStr (hautM h)).foldl (fun b m => { b with formen := b.formen.insert m (b.formen.getD m 0 + 1) }) b
    let b := zs.foldl (fun b x => if b.gut.contains x then b else { b with gut := b.gut.insert x (i, nb, k) })
      { b with gutProgramme := b.gutProgramme + 1 }
    let neu := zs.filter fun x => !b.gutGedruckt.contains x
    if neu.isEmpty then b else
      b.druck z h ws s!"gut_{i}_{k}_{b.quellen.size}.gab" "valid" neu true
  | some c =>
    let b := zs.foldl (fun b x =>
      if x.schlecht && x.komp == c.val && !b.schlecht.contains x then
        { b with schlecht := b.schlecht.insert x (i, nb, k) } else b)
      { b with schlechtProgramme := b.schlechtProgramme + 1 }
    let neu := zs.filter fun x => x.schlecht && x.komp == c.val && !b.schlGedruckt.contains x
    if neu.isEmpty then b else
      b.druck z h ws s!"schlecht{c.val}_{i}_{k}_{b.quellen.size}.gab" s!"refused-only-by-{c.val}" neu false

/-- The sweep of one member at one size, over all parameters: the stream of skeletons is walked once and every lock
    family and list of starts is asked of each skeleton. -/
def Spez.sammle (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))))
    (i nb k : Nat) (b : Befund) : Befund :=
  letI : Zahlen := z.zahlen
  let par := z.parameter
  (hautT tbls k).foldl
    (fun b h => par.foldl (fun b (S, ws) =>
      match z.erzeugeAus h S ws with
      | some e => b.nimm i nb k z e
      | none => b) b) b

/-- A cell as text. -/
def Zelle.text (z : Zelle) : String :=
  s!"{z.komp}.{z.art}" ++ " " ++ String.intercalate "" (z.atome.map fun a => if a then "1" else "0")

end Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Zielsatz

def sag (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  match args with
  | nb :: kmax :: rest =>
    let ueber : List (Nat × Nat × Nat) := rest.filterMap fun s =>
      match s.splitOn ":" with
      | [i, a, c] => some (i.toNat!, a.toNat!, c.toNat!)
      | _ => none
    let nur : Option (List Nat) := (← IO.getEnv "LAUF_NUR").map fun v => (v.splitOn ",").filterMap String.toNat?
    let mut b : Befund := {}
    for i in List.range mitglieder.length do
      let z := mitglieder.getD i {}
      let gewaehlt := match nur with | some l => l.contains i | none => true
      if !gewaehlt then continue
      let (nbI, kmaxI) := match ueber.find? (·.1 == i) with | some (_, a, c) => (a, c) | none => (nb.toNat!, kmax.toNat!)
      let tbls := z.tabellenD nbI
      for k in List.range (kmaxI + 1) do
        if k ≥ 1 then
          let t := ← IO.monoMsNow
          b := z.sammle tbls i nbI k b
          sag s!"member {i} size {k}: valid programs {b.gutProgramme}, single-fault programs {b.schlechtProgramme}, valid-witness {b.gut.size}, refused-witness {b.schlecht.size}, transcription errors {b.falsch}  ({(← IO.monoMsNow) - t} ms)"
    IO.println "kind\tcells\tbad-cells\tgood-witnessed\tbad-witnessed"
    for c in List.range 10 do
      let alle := zellAlle.filter fun x => x.komp == c
      for a in (alle.map (·.art)).eraseDups do
        let m := alle.filter fun x => x.art == a
        let sch := m.filter (·.schlecht)
        IO.println s!"{c}.{a}\t{m.length}\t{sch.length}\t{(m.filter fun x => !x.schlecht && b.gut.contains x).length}\t{(sch.filter fun x => b.schlecht.contains x).length}"
    let gutAlle := zellAlle.filter fun x => !x.schlecht
    let schAlle := zellAlle.filter (·.schlecht)
    IO.println s!"universe: {zellAlle.length} cells ({gutAlle.length} good, {schAlle.length} bad)"
    IO.println s!"good cells with a VALID program: {(gutAlle.filter fun x => b.gut.contains x).length} of {gutAlle.length}"
    IO.println s!"bad cells with a program refused by exactly its component: {(schAlle.filter fun x => b.schlecht.contains x).length} of {schAlle.length}"
    IO.println "-- not witnessed (kind atoms; G = good cell without a valid program, B = bad cell without a single-fault program)"
    for x in gutAlle.filter (fun x => !b.gut.contains x) do IO.println s!"{x.text}\tG"
    for x in schAlle.filter (fun x => !b.schlecht.contains x) do IO.println s!"{x.text}\tB"
    IO.println s!"valid programs: {b.gutProgramme}; single-fault programs: {b.schlechtProgramme}; transcription errors: {b.falsch}"
    IO.println s!"PRINTED: {b.quellen.size} programs; good cells with a printed valid program {(gutAlle.filter fun x => b.gutGedruckt.contains x).length} of {gutAlle.length}; bad cells with a printed single-fault program {(schAlle.filter fun x => b.schlGedruckt.contains x).length} of {schAlle.length}"
    IO.println "-- not printable (reason, programs)"
    for p in b.grund.toList.toArray.qsort (fun x y => x.2 > y.2) do IO.println s!"{p.1}\t{p.2}"
    IO.println "-- forms (register members) used by the valid programs: member, programs"
    for p in b.formen.toList.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{p.1}\t{p.2}"
    match b.beispiel with
    | some s => IO.eprintln s!"first transcription error at: {s}"
    | none => pure ()
    match (← IO.getEnv "LAUF_QUELLEN") with
    | some dir =>
      IO.FS.createDirAll dir
      let mut index := "file\tclass\n"
      for (datei, klasse, text) in b.quellen do
        IO.FS.writeFile (dir ++ "/" ++ datei) text
        index := index ++ s!"{datei}\t{klasse}\n"
      IO.FS.writeFile (dir ++ "/index.tsv") index
      IO.println s!"sources written: {b.quellen.size} files in {dir}"
    | none => pure ()
    return (if b.falsch == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: gen-zellen NB KMAX [I:NB:KMAX ...]"
    return 2
