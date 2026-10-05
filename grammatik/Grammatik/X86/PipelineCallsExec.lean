/-
  File:      Grammatik/X86/PipelineCallsExec.lean
  Subject:   Pipeline calls, real source correspondence: a callee whose body
             is one lowered straight-line assignment (`execBlock` of the real
             body, not an abstracted result write), with callee-saved
             register preservation and a memory-changing witness.

  Reused, not duplicated: `PipelineCalls` (`rufOk`, `calleeGerettet`,
  `pipeline_ruf_rahmen`, frame witnesses), `Pipeline` (`senkBlock`,
  `validate`/`validate_sound`, `senkWertT_korrekt`, `assignT_lauf`,
  `worldRep_store`, `lauf_zu_laufBytes`, `Entspricht` vocabulary),
  `PipelineWitnesses` (the concrete declaration `pwD`, contract `pwV`,
  layout `pwL`, values and memories). No second machine, no second
  loader, no source claim beyond the proved fragment.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineCallsExec

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineWitnesses

variable {D : Deklaration}

/-- The proved callee shape: exactly one slot assignment, then `nil`.
    Every other block form is refused, never guessed. -/
def istEinzelZuweisung {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') : Bool :=
  match b with
  | .cons (.assignSlot _ _ _ _ _ _) .nil => true
  | _ => false

/-- THE CALL-EXEC VALIDATOR: the caller frame is admitted (`rufOk`: layout
    fit, exact stack-arg count, six callee-save words, no red zone), the
    callee body has the proved single-assignment shape, and the candidate
    bytes are what the Lean pipeline recomputes from the source
    (`validate` with no optimiser certificates: a certificate could
    rewrite the body away from the proved shape). -/
def rufExecOk (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  rufOk b r nArgs benutztRot && istEinzelZuweisung body &&
    validate c L [] body bytes

/-- Working registers used nowhere near the callee-saved set: every
    callee-saved register differs from `dst` and `adr` and lies off the
    scratch stack `tmp :: frei`. Decided, never assumed. -/
def calleeFremd (c : PipeCfg) : Bool :=
  calleeGerettet.all (fun q => decide (q ≠ c.dst ∧ q ≠ c.adr ∧ q ∉ c.tmp :: c.frei))

end Gabbro.Grammatik.X86.PipelineCallsExec
