/- GabbroV's generator: from a Gabbro source text to the Lean modules of its duties. -/
module
public import Bruecke.Vorlage
-- Load transitive compiler IR for `lean --run`; retain the runtime import and native main.
meta import Bruecke.Vorlage
@[expose] public section

namespace Gabbro.Bruecke.Vorlage

/-- The Lake package of a generated unit (written once, kept when present): `lean_lib MODULE` on top of GabbroV
    (`bruecke`, by path), on GabbroV's toolchain and manifest, with the packages shared with
    `grammatik/.lake/packages` (no second Mathlib). `lake build` then checks again only what a change
    touched; a changed body touches only its own function's duty. -/
def paketDateien (ziel modul : String) : IO Unit := do
  let app ← IO.appPath
  let some root := app.parent >>= (·.parent) >>= (·.parent) >>= (·.parent) | return
  let root ← IO.FS.realPath root
  let repo ← IO.FS.realPath (root / ".." / "..")
  let abs := repo.toString ++ "/"
  let schreib (name text : String) : IO Unit := do
    let p : System.FilePath := System.FilePath.mk ziel / name
    unless ← p.pathExists do IO.FS.writeFile p text
  let man ← IO.FS.readFile (root / "lake-manifest.json")
  let bruecke := "{\"type\": \"path\",\n   \"scope\": \"\",\n   \"name\": \"bruecke\",\n" ++
    "   \"manifestFile\": \"lake-manifest.json\",\n   \"inherited\": false,\n   \"dir\": \"" ++ root.toString ++
    "\",\n   \"copy\": false,\n   \"configFile\": \"lakefile.toml\"},\n  "
  let man := ((((man.replace "\"dir\": \"../../" ("\"dir\": \"" ++ abs)).replace
      "\"packagesDir\": \"../../" ("\"packagesDir\": \"" ++ abs)).replace
      "\"inherited\": false" "\"inherited\": true").replace
      "\"packages\":\n [" ("\"packages\":\n [" ++ bruecke)).replace
      "\"name\": \"bruecke\",\n \"lakeDir\"" ("\"name\": \"" ++ modul ++ "\",\n \"lakeDir\"")
  schreib "lake-manifest.json" man
  schreib "lean-toolchain" (← IO.FS.readFile (root / "lean-toolchain"))
  schreib "lakefile.toml" <|
    "name = \"" ++ modul ++ "\"\n" ++
    "packagesDir = \"" ++ abs ++ "grammatik/.lake/packages\"\n" ++
    "weakLeanArgs = [\"-DmaxHeartbeats=400000\"]\n" ++
    "defaultTargets = [\"" ++ modul ++ "\"]\n\n" ++
    "# A Gabbro unit's duties, written by `gabbrov` (GabbroV). `lake build` checks them; your proofs are\n" ++
    "# `" ++ modul.replace "." "/" ++ "/Beweis/F<i>.lean`.\n\n" ++
    "[[require]]\nname = \"bruecke\"\npath = \"" ++ root.toString ++ "\"\n\n" ++
    "[[lean_lib]]\nname = \"" ++ modul ++ "\"\n"

/-- `gabbrov MODULE FILE.gab OUTDIR`: write the duty modules of the unit of `FILE.gab` under the
    module prefix `MODULE` (for example `Proofs.Lexer`) below `OUTDIR`. Generated files are
    replaced on every run; your proof files `MODULE/Beweis/F<i>.lean` are written once and never
    replaced. Exit 0: premise (b) is stated (prove the `beweis<i>` goals); 1: premise (b) is not
    stated (see the top file); 2: wrong arguments, unreadable file, or Stage 0 refuses the source. -/
def haupt (args : List String) : IO UInt32 := do
  -- `--ein`: the guardian's form, one module `MODULE/Ein.lean` (`einDatei`)
  let (ein, args) := match args with
    | "--ein" :: rest => (true, rest)
    | _ => (false, args)
  let [modul, pfad, ziel] := args | do
    IO.eprintln "usage: gabbrov [--ein] MODULE FILE.gab OUTDIR"
    return 2
  let src ← try IO.FS.readFile pfad catch e => do
    IO.eprintln s!"gabbrov: cannot read {pfad}: {e}"
    return 2
  match dateien modul src with
  | .error e =>
    IO.eprintln s!"gabbrov: {e}"
    return 2
  | .ok ds =>
    let ds := if ein then [einDatei modul ds] else ds
    let mut neu := 0
    let mut behalten := 0
    for d in ds do
      let datei : System.FilePath := System.FilePath.mk ziel / (d.pfad ++ ".lean")
      if !d.ersetzen && (← datei.pathExists) then
        behalten := behalten + 1
      else
        if let some dir := datei.parent then IO.FS.createDirAll dir
        IO.FS.writeFile datei d.text
        neu := neu + 1
    unless ein do paketDateien ziel modul
    let abgelehnt := ds.any fun d => (d.text.splitOn "REFUSED").length > 1
    IO.println s!"gabbrov: {neu} files written, {behalten} proof files kept, under {ziel}/{modul.replace "." "/"}"
    if abgelehnt then
      IO.println s!"gabbrov: REFUSED -- see {modul.replace "." "/"}.lean"
      return 1
    return 0

end Gabbro.Bruecke.Vorlage

def main (args : List String) : IO UInt32 := Gabbro.Bruecke.Vorlage.haupt args
