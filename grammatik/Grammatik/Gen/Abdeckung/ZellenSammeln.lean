/-
  File:      Grammatik/Gen/Abdeckung/ZellenSammeln.lean
  Subject:   The union of the per-member records of `gen-zelle` (`ZellenEins.lean`):

               gen-zellen-sammeln DIR

             reads every DIR/m<I>.txt, reports per kind of cell how many good cells have a valid witness and how many
             bad cells an isolated one, the cells without, the cover of the good cells by printed valid programs with
             its lower bound (`deckung_schranke`), the printer's skip reasons and the forms used. It writes the chosen
             cover to DIR (`<stem>.gab`), `index.tsv` and `manifest.tsv`, and deletes the unchosen candidates (DIR/kand).
             A cell text that names no cell of `zellAlle` stops the run (exit 1): the records belong to another model.
-/
import Grammatik.Gen.Abdeckung.ZellenBefund
import Grammatik.Gen.Abdeckung.ZellenSchluss

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- The cell of a text, from the universe. -/
def zelleAus (t : String) : Option Zelle := zellAlle.find? (·.text == t)

/-- What the records of all members say together. -/
structure Summe where
  zahlen : Nat × Nat × Nat := (0, 0, 0)
  gut : List Zelle := []
  schlecht : List Zelle := []
  maskiert : List Zelle := []
  schlGedruckt : List Zelle := []
  quellen : List (String × String) := []
  kand : List (String × List Zelle × Except String Unit) := []
  grund : Std.HashMap String Nat := {}
  formen : Std.HashMap String Nat := {}
  fremd : List String := []
  /-- Lean witness files: of valid programs (stem, cells, printed) and of isolated bad cells (stem, cell, printed) -/
  leanG : List (String × List Zelle × Bool) := []
  leanB : List (String × List Zelle × List Zelle × Bool) := []

/-- One record line. -/
def Summe.zeile (s : Summe) (l : String) : Summe :=
  let zelle := fun t => match zelleAus t with | some x => (some x, s) | none => (none, { s with fremd := s.fremd ++ [t] })
  let neu := fun (xs : List Zelle) (x : Zelle) => if xs.contains x then xs else xs ++ [x]
  match l.splitOn "\t" with
  | ["Z", a, b, c] => let (x, y, w) := s.zahlen; { s with zahlen := (x + a.toNat!, y + b.toNat!, w + c.toNat!) }
  | ["G", t, _] => match zelle t with | (some x, s) => { s with gut := neu s.gut x } | (none, s) => s
  | ["B", t, _] => match zelle t with | (some x, s) => { s with schlecht := neu s.schlecht x } | (none, s) => s
  | ["X", t, _] => match zelle t with | (some x, s) => { s with maskiert := neu s.maskiert x } | (none, s) => s
  | ["S", t, _] => match zelle t with | (some x, s) => { s with schlGedruckt := neu s.schlGedruckt x } | (none, s) => s
  | ["Q", f, k] => { s with quellen := s.quellen ++ [(f, k)] }
  | ["K", st, key, r] =>
    let ts := if key.isEmpty then [] else key.splitOn ";"
    let zs := ts.filterMap zelleAus
    let s := if zs.length == ts.length then s else { s with fremd := s.fremd ++ ts.filter (zelleAus · |>.isNone) }
    { s with kand := s.kand ++ [(st, zs, if r == "ok" then .ok () else .error r)] }
  | ["LG", st, key, r] =>
    let zs := (if key.isEmpty then [] else key.splitOn ";").filterMap zelleAus
    { s with leanG := s.leanG ++ [(st, zs, r == "ok")] }
  | ["LB", st, bad, key, r] =>
    let bs := (if bad.isEmpty then [] else bad.splitOn ";").filterMap zelleAus
    let zs := (if key.isEmpty then [] else key.splitOn ";").filterMap zelleAus
    { s with leanB := s.leanB ++ [(st, bs, zs, r == "ok")] }
  | ["R", m, n] => { s with grund := s.grund.insert m (s.grund.getD m 0 + n.toNat!) }
  | ["F", m, n] => { s with formen := s.formen.insert m (s.formen.getD m 0 + n.toNat!) }
  | _ => s

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] =>
    let mut s : Summe := {}
    let mut dateien := 0
    for e in (← System.FilePath.readDir dir) do
      if e.fileName.startsWith "m" && e.fileName.endsWith ".txt" then
        dateien := dateien + 1
        for l in (← IO.FS.readFile e.path).splitOn "\n" do s := s.zeile l
    if !s.fremd.isEmpty then
      IO.eprintln s!"cells that are not in the universe: {s.fremd.take 5}"
      return 1
    IO.println s!"records: {dateien}"
    IO.println "kind\tcells\tbad-cells\tgood-witnessed\tbad-witnessed"
    for c in List.range 10 do
      let alle := zellAlle.filter fun x => x.komp == c
      for a in (alle.map (·.art)).eraseDups do
        let m := alle.filter fun x => x.art == a
        let sch := m.filter (·.schlecht)
        IO.println s!"{c}.{a}\t{m.length}\t{sch.length}\t{(m.filter fun x => !x.schlecht && s.gut.contains x).length}\t{(sch.filter s.schlecht.contains).length}"
    let gutAlle := zellAlle.filter fun x => !x.schlecht
    let schAlle := zellAlle.filter (·.schlecht)
    let (anzG, anzS, anzF) := s.zahlen
    IO.println s!"universe: {zellAlle.length} cells ({gutAlle.length} good, {schAlle.length} bad)"
    IO.println s!"good cells with a VALID program: {(gutAlle.filter s.gut.contains).length} of {gutAlle.length}"
    IO.println s!"ISOLATED bad cells: {(schAlle.filter s.schlecht.contains).length} of {schAlle.length}; printed {(schAlle.filter s.schlGedruckt.contains).length}"
    IO.println s!"valid programs: {anzG}; single-fault programs: {anzS}; transcription errors: {anzF}"
    IO.println "-- not witnessed (G = good cell without a valid program, B = bad cell without an isolated program, M = seen only masked)"
    for x in gutAlle.filter (!s.gut.contains ·) do IO.println s!"{x.text}\tG"
    for x in schAlle.filter (!s.schlecht.contains ·) do
      IO.println s!"{x.text}\t{if s.maskiert.contains x then "M" else "B"}"
    -- the cover: the sources of the printable candidates are read back from DIR/kand
    let mut kand : List (String × List Zelle × Except String String × Nat) := []
    for (st, zs, r) in s.kand do
      match r with
      | .ok () =>
        let f := s!"{dir}/kand/{st}.gab"
        if ← System.FilePath.pathExists f then kand := kand ++ [(st, zs, .ok (← IO.FS.readFile f), 0)]
        else kand := kand ++ [(st, zs, .error "source file missing", 0)]
      | .error m => kand := kand ++ [(st, zs, .error m, 0)]
    let u := ueberdeckung kand
    IO.println s!"COVER: good cells reachable {u.erreichbar.length} of {gutAlle.length}; printable {u.druckbar.length}; chosen {u.gewaehlt.length} programs; lower bound {u.schranke}"
    for x in u.erreichbar.filter (!u.druckbar.contains ·) do
      let gruende := dedupStr (kand.filterMap fun (_, zs, r, _) =>
        match r with | .error m => if zs.contains x then some m else none | .ok _ => none)
      IO.println s!"{x.text}\tnot printed: {String.intercalate " | " gruende}"
    IO.println "-- not printable (reason, programs)"
    for p in s.grund.toList.toArray.qsort (fun x y => x.2 > y.2) do IO.println s!"{p.1}\t{p.2}"
    IO.println "-- forms used by the valid programs (member, programs)"
    for p in s.formen.toList.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{p.1}\t{p.2}"
    let mut index := "file\tclass\n"
    let mut manifest := "file\tclass\tcells\n"
    for (st, zs, text) in u.gewaehlt do
      IO.FS.writeFile s!"{dir}/{st}.gab" text
      index := index ++ s!"{st}.gab\tvalid\n"
      manifest := manifest ++ s!"{st}.gab\tvalid\t{String.intercalate ";" (dedupStr (zs.map Zelle.text))}\n"
    for (f, k) in s.quellen do
      index := index ++ s!"{f}\t{k}\n"
      manifest := manifest ++ s!"{f}\t{k}\t\n"
    IO.FS.writeFile s!"{dir}/index.tsv" index
    IO.FS.writeFile s!"{dir}/manifest.tsv" manifest
    -- the Lean witnesses: a greedy cover of the good cells by printed valid programs, one program per isolated bad cell
    let gutAlle := zellAlle.filter fun x => !x.schlecht
    let lg := s.leanG.filter (·.2.2)
    let mut offen := gutAlle.filter fun x => lg.any (·.2.1.contains x)
    let mut wahl : List String := []
    for _ in List.range (lg.length + 1) do
      if offen.isEmpty then break
      let best := lg.foldl (fun (b : Option (String × Nat)) (st, zs, _) =>
        let n := (offen.filter zs.contains).length
        if n > 0 && (b.map (·.2) |>.getD 0) < n then some (st, n) else b) none
      match best with
      | none => break
      | some (st, _) =>
        wahl := wahl ++ [st]
        let zs := ((lg.find? (·.1 == st)).map (·.2.1)).getD []
        offen := offen.filter (!zs.contains ·)
    IO.FS.createDirAll s!"{dir}/zeugen"
    let gutL := gutAlle.filter fun x => lg.any (·.2.1.contains x)
    -- the tests of N: per bad cell a printed refused program whose needed cells (`bnoetig`: its cells that are not
    -- witnessed good cells) are the cell itself, or for a root or pool cell the cell and its partner
    let bnoetig := fun (all : List Zelle) => all.filter fun w => w.schlecht || !gutL.contains w
    let findN := fun (erlaubt : List Zelle) => (s.leanB.find? fun (_, _, all, ok) =>
      ok && !(bnoetig all).isEmpty && (bnoetig all).all erlaubt.contains).map (·.1)
    let schlW : Zelle → Option NGrund := fun x =>
      match findN [x] with
      | some st => some (.einfach st)
      | none =>
        match x.komp, x.art with
        | 5, 0 =>
          match NGrund.partner x false, NGrund.partner x true with
          | some p0, some p1 =>
            match findN [x, p0], findN [x, p1] with
            | some s0, some s1 => some (.wurzel s0 s1)
            | _, _ => none
          | _, _ => none
        | 6, 0 => (NGrund.partner x true).bind fun p => (findN [x, p]).map .pool
        | _, _ => none
    let nWahl := dedupStr (schAlle.flatMap fun x => match schlW x with
      | some (.einfach st) => [st] | some (.wurzel s0 s1) => [s0, s1] | some (.pool st) => [st] | none => [])
    let mut ohneText : List String := []
    for st in wahl ++ nWahl do
      if ← System.FilePath.pathExists s!"{dir}/lean/{st}.lean" then
        IO.FS.writeFile s!"{dir}/zeugen/{st}.lean" (← IO.FS.readFile s!"{dir}/lean/{st}.lean")
      -- the Gabbro source of the same program: valid candidates in kand/, single-fault programs beside the records
      let quelle := if st.startsWith "M" then s!"{dir}/kand/{st}.gab" else s!"{dir}/{st}.gab"
      if ← System.FilePath.pathExists quelle then
        IO.FS.writeFile s!"{dir}/zeugen/{st}.gab" (← IO.FS.readFile quelle)
      else ohneText := ohneText ++ [st]
    IO.println s!"GABBRO SOURCES of the witnesses: {(wahl ++ nWahl).length - ohneText.length} of {(wahl ++ nWahl).length}; without source: {ohneText}"
    -- the good cells the chosen witnesses cover: the list N may draw its good cells from (`nGen … er`)
    IO.FS.writeFile s!"{dir}/zeugen/Erreicht.lean" (s!"/-\n  File:      Grammatik/Gen/Zeugen/Erreicht.lean\n  Subject:   GENERATED (`gen-zellen-sammeln`): the good cells the M witnesses cover; N keeps only programs whose\n             good cells outside it are needed cells of a test (`bnoetig`). Do not edit.\n-/\nimport Grammatik.Gen.Abdeckung.Satz.Raum\n\nnamespace Gabbro.Grammatik.Gen.Zeugen\n\nopen Gabbro.Grammatik.Gen\n\ndef erreicht : List Zelle := [\n  " ++ String.intercalate ",\n  " (gutL.map Zelle.lean) ++ "]\n\nend Gabbro.Grammatik.Gen.Zeugen\n")
    let schL := schAlle.filter fun x => (schlW x).isSome
    -- the closing file: every cell with its reason, or the open cells
    let gutW := fun (x : Zelle) => wahl.find? fun st => ((lg.find? (·.1 == st)).map (·.2.1.contains x)).getD false
    let mods := "Grammatik.Gen.Zeugen.Erreicht" :: (wahl.map (s!"Grammatik.Gen.Zeugen.M.{·}")) ++ nWahl.map (s!"Grammatik.Gen.Zeugen.N.{·}")
    match schlussText gutW schlW mods with
    | .ok text =>
      IO.FS.writeFile s!"{dir}/zeugen/Schluss.lean" text
      IO.println "CLOSING FILE written: every cell has its reason"
    | .error ohne =>
      IO.println s!"OPEN CELLS (no witness, no theorem): {ohne.length}"
      for x in ohne do IO.println s!"{x.text}\t{if x.schlecht then "B" else "G"}\topen"
    IO.println s!"LEAN WITNESSES: good cells {gutL.length} of {gutAlle.length} by {wahl.length} programs; bad cells with N tests {schL.length} of {schAlle.length}; files in {dir}/zeugen"
    for x in gutAlle.filter (fun x => s.gut.contains x && !gutL.contains x) do IO.println s!"{x.text}\tvalid program found, no Lean print"
    if ← System.FilePath.pathExists s!"{dir}/kand" then IO.FS.removeDirAll s!"{dir}/kand"
    IO.println s!"sources: {u.gewaehlt.length} valid + {s.quellen.length} single-fault in {dir}"
    return (if anzF == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: gen-zellen-sammeln DIR"
    return 2
