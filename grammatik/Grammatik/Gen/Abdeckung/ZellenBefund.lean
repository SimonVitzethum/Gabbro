/-
  File:      Grammatik/Gen/Abdeckung/ZellenBefund.lean
  Subject:   WHAT ONE SWEEP OF THE PROVEN GENERATOR SEES, per cell (`Zellen.lean`): the library of the two drivers
             `gen-zelle` (`ZellenEins.lean`, ONE member per process) and `gen-zellen-sammeln` (`ZellenSammeln.lean`, the
             union of the per-member records). The generator (`Spez.erzeugeF`, `Waehlen.lean`) emits a program ONLY with
             the proof of its class -- `Gutes` (the Lean model's Bool accepts it) or `Schlechtes c` (exactly component `c`
             refuses it) -- one program after the other; the only oracle is the Lean model's own Bool.

             Per cell the first witness is kept: a GOOD cell needs a `Gutes` program that has it; a BAD cell needs a
             `Schlechtes c` program, `c` the cell's component, in which it is the only bad cell. `zellenStimmen` (the
             transcription of the cells against `komp`) runs on every program emitted.
-/
import Std.Data.HashMap
import Grammatik.Gen.Abdeckung.Waehlen
import Grammatik.Gen.Druck.Einheit
import Grammatik.Gen.Druck.LeanZeuge

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
  /-- the Lean witness files: of every valid candidate (stem, cells, text or reason) and of the first program in which
      a bad cell is the only one (stem, cell, text or reason) -/
  lean : Array (String × List Zelle × Except String String) := #[]
  leanN : Std.HashMap Zelle (String × Except String String) := {}
  gutProgramme : Nat := 0
  schlechtProgramme : Nat := 0
  falsch : Nat := 0
  beispiel : Option String := none

/-- The cells of the program of an emitted value, under its lock family and starts. -/
def Spez.zellenVon (z : Spez) (h : Programm z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) :
    List Zelle :=
  letI : Zahlen := z.zahlen
  (List.finRange 10).flatMap (zellen h S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon h ws))

/-- The self-check of the transcription on one program. -/
def Spez.stimmt (z : Spez) (h : Programm z.deklaration) (S : SperrInv z.deklaration) (ws : List z.deklaration.Fn) : Bool :=
  letI : Zahlen := z.zahlen
  zellenStimmen h S z.fnListe z.lockListe z.traegerListe (z.wurzelnVon h ws)

/-- Print a program once, record it under `datei` and mark the `neu` cells as printed. -/
def Befund.druck (b : Befund) (z : Spez) (h : Programm z.deklaration) (art : Sperrart) (ws : List z.deklaration.Fn)
    (datei klasse : String) (neu : List Zelle) (gut : Bool) : Befund :=
  match z.quelltext h art ws (String.ofList (datei.toList.take (datei.length - 4))) with
  | .ok text =>
    let b := { b with quellen := b.quellen.push (datei, klasse, text) }
    if gut then neu.foldl (fun b x => { b with gutGedruckt := b.gutGedruckt.insert x datei }) b
    else neu.foldl (fun b x => { b with schlGedruckt := b.schlGedruckt.insert x datei }) b
  | .error m => { b with grund := b.grund.insert m (b.grund.getD m 0 + 1) }

/-- Take one emitted program. -/
def Befund.nimm (b : Befund) (i nb k nc : Nat) (z : Spez) (e : Erzeugt z) : Befund :=
  let (h, sa, ws, art) : Programm z.deklaration × Sperrart × List z.deklaration.Fn × Option (Fin 10) :=
    match e with
    | .gut g => (g.prog, g.art, g.ws, none)
    | .schlecht c s => (s.prog, s.art, s.ws, some c)
  let S := z.familie sa
  let zs := z.zellenVon h S ws
  let b := if z.stimmt h S ws then b else
    { b with falsch := b.falsch + 1, beispiel := b.beispiel.orElse fun _ => some s!"member {i} size {k}" }
  match art with
  | none =>
    let b := (dedupStr (hautM h.haut)).foldl (fun b m => { b with formen := b.formen.insert m (b.formen.getD m 0 + 1) }) b
    let b := zs.foldl (fun b x => if b.gut.contains x then b else { b with gut := b.gut.insert x (i, nb, k) })
      { b with gutProgramme := b.gutProgramme + 1 }
    let key := zellSchluessel zs
    if b.kand.contains key then b else
      let stamm := s!"M{i}_{b.kand.size}"
      let r := z.quelltext h sa ws stamm
      let b := match r with
        | .error m => { b with grund := b.grund.insert m (b.grund.getD m 0 + 1) }
        | .ok _ => b
      let zsD := zs.foldl (fun a x => if a.contains x then a else a ++ [x]) []
      { b with kand := b.kand.insert key (stamm, zs, r, i),
               lean := b.lean.push (stamm, zsD, z.leanZeuge i nc stamm h sa ws (zsD.filter (!·.schlecht)) none) }
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
    let b := if schlechte == 1 then
      (zs.filter fun x => x.schlecht && x.komp == c.val).foldl (fun b x =>
        if b.leanN.contains x then b else
          let st := s!"N{i}_{b.leanN.size}"
          { b with leanN := b.leanN.insert x (st, z.leanZeuge i nc st h sa ws [x] (some c)) }) b
      else b
    let neu := if schlechte == 1 then zs.filter fun x => x.schlecht && x.komp == c.val && !b.schlGedruckt.contains x else []
    if neu.isEmpty then b else
      b.druck z h sa ws s!"schlecht{c.val}_{i}_{k}_{b.quellen.size}.gab" s!"refused-only-by-{c.val}" neu false

/-- The sweep of one member at one size: the generator hands over one program at a time. -/
def Spez.sammle (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))))
    (i nb k nc : Nat) (b : Befund) : Befund :=
  z.erzeugeF tbls nc Befund k b fun b e => b.nimm i nb k nc z e


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
