/-
  File:      stage0/Stage0/IRBild.lean
  Subject:   `stage0 --ir PROGRAM.gab IMAGE`: the program checked by the goal theorem's checker Bool, lowered to G
             (`lowerAllg`), every function lowered to `S0IR` (`Senke/`), laid out as an image the runner loads.
-/
import Stage0.Bindung
import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.GabbroV.GvStartPflicht
import Stage0.Senke.Bild
import Stage0.Senke.Welt.Anordnung
import Stage0.Senke.Ausdruck.Old.Source

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The stack of an image, in slots (4 MiB); the world lies above it (`Senke.layU`). -/
def irStapel : Nat := 2 ^ 19

/-- Per-loop environment fuel compiled into the image; independent of call depth. -/
def irDurchlaeufe : Nat := 2 ^ 20

def irBild (src : String) (K : Nat := irStapel) : Except String (List Runner.B) := do
  let toks ← (lex src).mapError fun _ => "lex"
  let items ← parseTopTief toks
  let members := uMembers (pre108 items)
  let u ← elabU (members.map OldSource.normalizeItem)
  let main ← fnIdx u.fns "main"
  let (P, _) ← lowerAllg u
  let P ← OldSource.restore members u P
  if (← OldSource.accepts u P) = false then throw "refused by the checker (AkzeptiertX)"
  let tore ← toreVon (uMembers (pre108 items))
  let tor : (declOf u).Ax → Option Senke.TorB := fun a =>
    (tore.find? (·.name == (uaxAt u a).name)).map fun t => ⟨t.nummer, t.regs, t.fehler⟩
  let rs ← (uOhneDoppelte (u.roots ++ u.gestartet)).mapM (fnIdx u.fns)
  let roots := rs.filter (· != main)
  let b ← Senke.bild irDurchlaeufe P (Senke.layU u tor) (List.finRange u.fns.length) Fin.val
    (fun g => (u.fns[g.val]?.map (·.name)).getD "?") main roots K
  pure b.bytes

end Gabbro.Stage0
