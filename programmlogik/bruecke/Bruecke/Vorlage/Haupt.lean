/- GabbroV's generator: from a Gabbro source text to the Lean modules of its duties. -/
module
public import Bruecke.Vorlage
-- Load transitive compiler IR for `lean --run`; retain the runtime import and native main.
meta import Bruecke.Vorlage
@[expose] public section

namespace Gabbro.Bruecke.Vorlage

/-- `gabbrov MODULE FILE.gab OUTDIR`: write the duty modules of the unit of `FILE.gab` under the
    module prefix `MODULE` (for example `Proofs.Lexer`) below `OUTDIR`. Generated files are
    replaced on every run; your proof files `MODULE/Beweis/F<i>.lean` are written once and never
    replaced. Exit 0: premise (b) is stated (prove the `beweis<i>` goals); 1: the files name at
    least one refusal; 2: wrong arguments, unreadable file, or Stage 0 refuses the source. -/
def haupt (args : List String) : IO UInt32 := do
  let [modul, pfad, ziel] := args | do
    IO.eprintln "usage: gabbrov MODULE FILE.gab OUTDIR"
    return 2
  let src ← try IO.FS.readFile pfad catch e => do
    IO.eprintln s!"gabbrov: cannot read {pfad}: {e}"
    return 2
  match dateien modul src with
  | .error e =>
    IO.eprintln s!"gabbrov: {e}"
    return 2
  | .ok ds =>
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
    let abgelehnt := ds.any fun d => (d.text.splitOn "REFUSED").length > 1
    IO.println s!"gabbrov: {neu} files written, {behalten} proof files kept, under {ziel}/{modul.replace "." "/"}"
    if abgelehnt then
      IO.println s!"gabbrov: REFUSED -- see {modul.replace "." "/"}.lean for the forms and checks outside the bridge"
      return 1
    return 0

end Gabbro.Bruecke.Vorlage

def main (args : List String) : IO UInt32 := Gabbro.Bruecke.Vorlage.haupt args
