/-
  File:      Grammatik/X86/PipelineWorkBranches.lean
  Subject:   Pipeline work bounds for branches and loops (lane 1233).

  Follow-up of lane 1165 (`PipelineWork.lean`: shallow assignment chunks
  only). Worst-case retired-instruction bounds for if/else (max of the
  branches plus the compare/jump, over the accepted `iteCode` shape of
  `Pipeline.lean`) and for bounded loops (the source iteration budget
  transfers to the target step budget `schleifeSchritte` of
  `PipelineLoops.lean`); unbounded loops (`retry`/`forever` at the
  `senkBlock` level) stay refused. A small validator (`pruefeZweig`)
  recomputes the bound from the lowered list, and the main correctness
  theorem is in the style of `pipeline_arbeit_korrekt` (source
  `execBlock` related to the fetched-byte run, plus retired-work and
  named-time bounds). Reused unchanged: `senkBlock`/`senkBlock_korrektC`/
  `iteCode`/`Entspricht`/`CodeAt`, `pipeSummary`/`pipeSummary_expand`,
  `decodiertZu`/`arbeit_decodiert`, `Deckung`/
  `budgetAusfuehrung_transfer`, `schleifeSchritte`, the `pd`/`pw`
  witness packages. No second IR, no second interpreter, no optimiser
  edit. Rust is out of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineLoops
import Grammatik.X86.PipelineImageWitnesses
import Grammatik.X86.BudgetExecution
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.HardwareAssumptions

namespace Gabbro.Grammatik.X86.PipeWorkBranches

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineImageWitnesses

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Branch worst-case bound over the accepted `iteCode` shape. -/

/-- Worst-case retired instructions of an if/else: the compare code,
    one taken jump, the LONGER branch, one end jump. -/
def iteSchranke (codeLen tLen eLen : Nat) : Nat :=
  codeLen + 1 + Nat.max tLen eLen + 1

/-- Static length of the accepted ite code shape (both branches). -/
theorem iteCode_laenge (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) :
    (iteCode code j pt pe).length = code.length + 1 + pt.length + 1 + pe.length := by
  simp [iteCode]
  omega

/- CUTS (skeleton):
    - Proved here: `iteCode_laenge`.
    - OPEN: everything else of the task (validator, main theorem,
      loop transfer, refusals, witnesses).
-/

#print axioms iteCode_laenge

end Gabbro.Grammatik.X86.PipeWorkBranches
