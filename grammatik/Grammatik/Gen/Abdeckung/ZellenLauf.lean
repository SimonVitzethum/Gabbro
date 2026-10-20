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

/-- A cell as text. -/
def Zelle.text (z : Zelle) : String :=
  s!"{z.komp}.{z.art}" ++ " " ++ String.intercalate "" (z.atome.map fun a => if a then "1" else "0")

/-- The set of cells as a key: the sorted, distinct texts. -/
def zellSchluessel (zs : List Zelle) : String :=
  String.intercalate ";" ((dedupStr (zs.map Zelle.text)))

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
  /-- the valid programs by their SET of cells (one per distinct set): cells, the printed source or the reason it
      could not be printed, member -/
  kand : Std.HashMap String (String × List Zelle × Except String String × Nat) := {}
  /-- bad cells seen only in programs that have another bad cell (never alone), with the number of programs -/
  maskiert : Std.HashMap Zelle Nat := {}
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
    let key := zellSchluessel zs
    if b.kand.contains key then b else
      let stamm := s!"M{b.kand.size}"
      let r := z.quelltext h ws stamm
      let b := match r with
        | .error m => { b with grund := b.grund.insert m (b.grund.getD m 0 + 1) }
        | .ok _ => b
      { b with kand := b.kand.insert key (stamm, zs, r, i) }
  | some c =>
    -- a bad cell is ISOLATED in a program when it is the only bad cell of the whole program (`schlecht_noetig`)
    let schlechte := (dedupStr (zs.filter (·.schlecht) |>.map Zelle.text)).length
    let b := { b with schlechtProgramme := b.schlechtProgramme + 1 }
    let b := zs.foldl (fun b x =>
      if x.schlecht && x.komp == c.val then
        if schlechte == 1 then
          if b.schlecht.contains x then b else { b with schlecht := b.schlecht.insert x (i, nb, k) }
        else { b with maskiert := b.maskiert.insert x (b.maskiert.getD x 0 + 1) }
      else b) b
    let neu := if schlechte == 1 then zs.filter fun x => x.schlecht && x.komp == c.val && !b.schlGedruckt.contains x else []
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


/-- The cover of the good cells by printable valid programs (Stage 1 of `dokumente/PLAN-TEST-SET.md`). -/
structure Ueberdeckung where
  /-- the good cells that occur in some valid program -/
  erreichbar : List Zelle
  /-- the good cells that occur in some PRINTABLE valid program -/
  druckbar : List Zelle
  /-- the chosen programs: stem, cells, source -/
  gewaehlt : List (String × List Zelle × String)
  /-- the size of a set of good cells that never occur together in one valid program: a lower bound for ANY cover by
      valid programs (`deckung_schranke`) -/
  schranke : Nat

/-- A greedy cover of the printable-reachable good cells, then every program whose cells the others cover is dropped;
    and the lower bound from a greedy set of cells that never co-occur. -/
def ueberdeckung (kand : List (String × List Zelle × Except String String × Nat)) : Ueberdeckung := Id.run do
  let gut := zellAlle.filter fun x => !x.schlecht
  let alle := kand.map (·.2.1)
  let erreichbar := gut.filter fun x => alle.any (·.contains x)
  let druck : Array (String × List Zelle × String) := (kand.filterMap fun (st, zs, r, _) =>
    match r with | .ok t => some (st, zs, t) | .error _ => none).toArray
  let druckbar := gut.filter fun x => druck.any (·.2.1.contains x)
  -- greedy
  let mut unbed := druckbar
  let mut gew : List Nat := []
  for _ in List.range (druck.size + 1) do
    if unbed.isEmpty then break
    let mut best : Option (Nat × Nat) := none
    for i in List.range druck.size do
      let gewinn := (unbed.filter fun x => (druck[i]!.2.1).contains x).length
      if gewinn > 0 && (best.map (·.2) |>.getD 0) < gewinn then best := some (i, gewinn)
    match best with
    | none => break
    | some (i, _) =>
      gew := gew ++ [i]
      unbed := unbed.filter fun x => !(druck[i]!.2.1).contains x
  -- drop the programs the others cover
  for i in gew.reverse do
    let rest := gew.filter (· != i)
    if druckbar.all (fun x => rest.any fun j => (druck[j]!.2.1).contains x) then gew := rest
  -- lower bound: cells that never occur together
  let mut a : List Zelle := []
  for x in erreichbar do
    if a.all (fun y => !alle.any (fun zs => zs.contains x && zs.contains y)) then a := a ++ [x]
  return { erreichbar, druckbar, gewaehlt := gew.map (fun i => druck[i]!), schranke := a.length }

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
      let tbls := z.tabellenD nbI (treu := (← IO.getEnv "LAUF_MODELL").isNone)
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
    let u := ueberdeckung (b.kand.toList.map (·.2))
    let gutAlle' := zellAlle.filter fun x => !x.schlecht
    IO.println s!"COVER (valid programs): good cells reachable by a valid program {u.erreichbar.length} of {gutAlle'.length}; by a printable one {u.druckbar.length}; chosen cover {u.gewaehlt.length} programs; lower bound {u.schranke} (cells that never occur together); distinct cell sets seen {b.kand.size}"
    let nurMask := schAlle.filter fun x => !b.schlecht.contains x && b.maskiert.contains x
    -- Stage 4.1: which skipped form keeps which good cell from having a printed witness
    let verloren := u.erreichbar.filter fun x => !u.druckbar.contains x
    IO.println s!"-- good cells reachable only by programs the printer skips: {verloren.length}; per cell the reasons"
    for x in verloren do
      let gruende := dedupStr ((b.kand.toList.map (·.2)).filterMap fun (_, zs, r, _) =>
        match r with | .error m => if zs.contains x then some m else none | .ok _ => none)
      IO.println s!"{x.text}\t{String.intercalate " | " gruende}"
    IO.println s!"ISOLATED bad cells (the only bad cell of a program refused by exactly its component): {(schAlle.filter fun x => b.schlecht.contains x).length} of {schAlle.length}; seen only masked by another bad cell: {nurMask.length} ({String.intercalate ", " (nurMask.map Zelle.text)})"
    IO.println s!"PRINTED single-fault programs: {b.quellen.size}; bad cells with a printed single-fault program {(schAlle.filter fun x => b.schlGedruckt.contains x).length} of {schAlle.length}"
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
      let mut manifest := "file\tclass\tcells\n"
      for (stamm, zs, text) in u.gewaehlt do
        IO.FS.writeFile (dir ++ "/" ++ stamm ++ ".gab") text
        index := index ++ s!"{stamm}.gab\tvalid\n"
        manifest := manifest ++ s!"{stamm}.gab\tvalid\t{String.intercalate ";" (dedupStr (zs.map Zelle.text))}\n"
      for (datei, klasse, text) in b.quellen do
        IO.FS.writeFile (dir ++ "/" ++ datei) text
        index := index ++ s!"{datei}\t{klasse}\n"
        manifest := manifest ++ s!"{datei}\t{klasse}\t\n"
      IO.FS.writeFile (dir ++ "/index.tsv") index
      IO.FS.writeFile (dir ++ "/manifest.tsv") manifest
      IO.println s!"sources written: {u.gewaehlt.length + b.quellen.size} files in {dir}"
    | none => pure ()
    return (if b.falsch == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: gen-zellen NB KMAX [I:NB:KMAX ...]"
    return 2
