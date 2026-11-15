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
module
public import Grammatik.Gen.Abdeckung.Records
public import Grammatik.Gen.Abdeckung.ZellenSchluss
@[expose] public section


open Gabbro.Grammatik Gabbro.Grammatik.Gen

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
    for c in List.range 11 do
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
    let gaps := s.leanGap.filter (·.2.2)
    let gWahl := gaps.map (·.1)
    for (st, zs, _) in gaps do
      index := index ++ s!"Gap/{st}.gab\tgap\n"
      manifest := manifest ++ s!"Gap/{st}.gab\tgap\t{String.intercalate ";" (dedupStr (zs.map Zelle.text))}\n"
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
    IO.FS.createDirAll s!"{dir}/zeugen/Gap"
    let mut ohneText : List String := []
    for st in wahl ++ nWahl ++ gWahl.map ("Gap/" ++ ·) do
      if ← System.FilePath.pathExists s!"{dir}/lean/{st}.lean" then
        IO.FS.writeFile s!"{dir}/zeugen/{st}.lean" (← IO.FS.readFile s!"{dir}/lean/{st}.lean")
      -- the Gabbro source of the same program: valid candidates in kand/, single-fault programs beside the records
      let quelle := if wahl.contains st || st.startsWith "Gap/" then s!"{dir}/kand/{st}.gab" else s!"{dir}/{st}.gab"
      if ← System.FilePath.pathExists quelle then
        IO.FS.writeFile s!"{dir}/zeugen/{st}.gab" (← IO.FS.readFile quelle)
      else ohneText := ohneText ++ [st]
    for st in gWahl do
      let source := s!"{dir}/kand/Gap/{st}.gab"
      if ← System.FilePath.pathExists source then
        IO.FS.createDirAll s!"{dir}/Gap"
        IO.FS.writeFile s!"{dir}/Gap/{st}.gab" (← IO.FS.readFile source)
    IO.println s!"GABBRO SOURCES of the witnesses: {(wahl ++ nWahl ++ gWahl).length - ohneText.length} of {(wahl ++ nWahl ++ gWahl).length}; without source: {ohneText}"
    -- the good cells the chosen witnesses cover: the list N may draw its good cells from (`nGen … er`)
    IO.FS.writeFile s!"{dir}/zeugen/Erreicht.lean" (s!"/-\n  File:      Grammatik/Gen/Zeugen/Erreicht.lean\n  Subject:   GENERATED (`gen-zellen-sammeln`): the good cells the M witnesses cover; N keeps only programs whose\n             good cells outside it are needed cells of a test (`bnoetig`). Do not edit.\n-/\nmodule\npublic import Grammatik.Gen.Abdeckung.Satz.Raum\n\n@[expose] public section\n\nnamespace Gabbro.Grammatik.Gen.Zeugen\n\nopen Gabbro.Grammatik.Gen\n\ndef erreicht : List Zelle := [\n  " ++ String.intercalate ",\n  " (gutL.map Zelle.lean) ++ "]\n\nend Gabbro.Grammatik.Gen.Zeugen\n")
    let schL := schAlle.filter fun x => (schlW x).isSome
    -- the closing file: every cell with its reason, or the open cells
    let gutW := fun (x : Zelle) => wahl.find? fun st => ((lg.find? (·.1 == st)).map (·.2.1.contains x)).getD false
    let mods := "Grammatik.Gen.Zeugen.Erreicht" :: (wahl.map (s!"Grammatik.Gen.Zeugen.M.{·}")) ++ nWahl.map (s!"Grammatik.Gen.Zeugen.N.{·}") ++ gWahl.map (s!"Grammatik.Gen.Zeugen.Gap.{·}")
    match schlussTextExplicit gutW schlW wahl nWahl (gWahl.map ("Gap." ++ ·)) mods with
    | .ok text =>
      IO.FS.writeFile s!"{dir}/zeugen/Schluss.lean" text
      IO.println "CLOSING FILE written: every cell has its reason"
    | .error ohne =>
      IO.println s!"OPEN CELLS (no witness, no theorem): {ohne.length}"
      for x in ohne do IO.println s!"{x.text}\t{if x.schlecht then "B" else "G"}\topen"
    IO.println s!"LEAN WITNESSES: good cells {gutL.length} of {gutAlle.length} by {wahl.length} programs; bad cells with N tests {schL.length} of {schAlle.length}; files in {dir}/zeugen"
    for x in gutAlle.filter (fun x => s.gut.contains x && !gutL.contains x) do IO.println s!"{x.text}\tvalid program found, no Lean print"
    if ← System.FilePath.pathExists s!"{dir}/kand" then IO.FS.removeDirAll s!"{dir}/kand"
    IO.println s!"sources: {u.gewaehlt.length} valid + {s.quellen.length} single-fault + {gWahl.length} fragment-gap in {dir}"
    return (if anzF == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: gen-zellen-sammeln DIR"
    return 2
