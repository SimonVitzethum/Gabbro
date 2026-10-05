/-
  File:      Grammatik/X86/PipelineUnit.lean
  Subject:   Source-computed units and duties feeding the pipeline (lane 1177).

  The pipeline (`Pipeline.lean`, `PipelineImage.lean`, `PipelineEntry.lean`)
  takes the program as Lean data (a `Block`). This file connects it to the
  source-computed unit and its duties: the generic T3 lowering
  (`Parser/UebersetzeAllg2.lean`: `UProg` elaboration, `lowerFnAt` per
  function, `lowerAllg` for the whole unit with `List.finRange` coverage)
  produces a `Programm` whose bodies are `Endblock`s; the projection
  `rumpfBlock` carries the pipeline-admissible prefix (straight-line
  `assignSlot` chains, the T3 body language without calls) to a pipeline
  `Block`, and the closing Bool `einheitSchluss` conjoins the pipeline
  checks (`validate`, `imageOk`, `weltOk`, `prologImageOk`,
  `eintrittZulassung`) with the entry duty (`requires` at the actual
  arguments). Duties at call sites are carried through the accepted
  `ContractSites` producers (`callSite_vorOk`, `rufAt_ok_gibt_ens`).

  Reused, not duplicated: everything from `Pipeline.lean`,
  `PipelineImage.lean`, `PipelineEntry.lean`, `ContractSites.lean` and the
  T3 lowering. No second interpreter, no per-program rule, no new executor.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.ContractSites
import Grammatik.Parser.UebersetzeAllg2

namespace Gabbro.Grammatik.X86.PipelineUnit

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineEntry
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Body prefix projection: straight-line `assignSlot` chains (the T3 body
    language without calls) become the pipeline `Block`; every tail form
    (`ret`, `retGrund`, `leave`, `next`) ends the block with `.nil`.
    Everything else (calls, control, binders, locks) is REFUSED (`none`). -/
def rumpfBlock : Endblock D V l Γ Λ → Option (Block D V l Γ Λ Λ)
  | .cons (.assignSlot t f i e hw hL) rest =>
    match rumpfBlock rest with
    | some b => some (.cons (.assignSlot t f i e hw hL) b)
    | none => none
  | .cons _ _ => none
  | .ret _ _ => some .nil
  | .retGrund _ _ => some .nil
  | .leave _ => some .nil
  | .next _ => some .nil
  | _ => none

/- CUTS (exactly what is NOT proved here):
    Skeleton only: the projection above, nothing else yet.
-/

#print axioms rumpfBlock

end Gabbro.Grammatik.X86.PipelineUnit
