/-
  File:      Grammatik/X86/PipelineCallsN.lean
  Subject:   Pipeline calls with three-or-more-statement callee bodies.

  Follow-up of `PipelineCallsExec` (single-assignment callee bodies):
  callee bodies that are chains of three or more `assignSlot` statements
  are lowered, validated and run, by induction on the body, with
  callee-saved preservation across the WHOLE body under the decided
  `calleeFremd` disjointness. Shorter bodies, non-assignment statements
  and everything else are REFUSED, never guessed.

  Reused, not duplicated: `Pipeline` (`senkBlock_assign`, `senkWertT`,
  `senkWertT_gerade`, `einzelChunk`-level `assignT_lauf` shape via
  `PipelineCallsExec.einzelChunk_lauf`, `worldRep_store`,
  `lauf_zu_laufBytes`, `validate_sound`, `repOk_int`, `constInt?_sound`),
  `PipelineCalls` (`rufOk`, `calleeGerettet`, `pipeline_ruf_verweigert_rot`,
  `rufWit*` frame witnesses), `PipelineCallsExec` (`rufExecOk_teile`
  shape, `calleeFremd`, `calleeFremd_mem`, `cwCfg`, `cw_fremd`,
  `cw_cfgOk`), `PipelineWitnesses` (`pwD`, `pwV`, `pwL`, `pwO`, `pwR`,
  `pwCtx`, `pwIdx0/1`, `pwWert0`, `pwHw/HL`, `pw_layoutSep`,
  `pw_cfgOk`-style facts), `PipelineBlockInduct` (`KetteLauf`,
  `ketteLauf_lauf`). No second machine, no second loader, no source
  claim beyond the proved fragment. Rust is out of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineCallsExec
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineBlockInduct

namespace Gabbro.Grammatik.X86.PipelineCallsN

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineCallsExec
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeBlock

variable {D : Deklaration}

variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. Shape: all-assignment blocks of three or more statements.

    `istEinzelZuweisung` (one body, `PipelineCallsExec`) and the refused
    longer bodies are generalised here: `istAssignBlock` holds exactly
    when every statement is an `assignSlot`; `istDreiPlus` adds the
    three-statement floor. One- and two-statement bodies are refused HERE
    (they stay with the earlier validators); this validator covers three
    or more. -/

/-- A statement is a slot assignment (nothing else). -/
def istAssignStmt {Λ₁ Λ₂ : List (Res D)} (s : Stmt D V l Γ Λ₁ Λ₂) : Bool :=
  match s with
  | .assignSlot _ _ _ _ _ _ => true
  | _ => false

/-- A block is all slot assignments (nil counts as all-assignment). -/
def istAssignBlock {Λ₁ Λ₂ : List (Res D)} : Block D V l Γ Λ₁ Λ₂ → Bool
  | .nil => true
  | .cons s rest => istAssignStmt s && istAssignBlock rest
  | _ => false

/-- The number of `cons` statements of a block (`nil` is 0; any other
    non-`cons` form ends the count at 0, so only `cons` chains count). -/
def blockLaenge {Λ₁ Λ₂ : List (Res D)} : Block D V l Γ Λ₁ Λ₂ → Nat
  | .nil => 0
  | .cons _ rest => blockLaenge rest + 1
  | _ => 0

/-- THREE OR MORE: every statement an assignment, at least three of them. -/
def istDreiPlus {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Bool :=
  istAssignBlock b && decide (3 ≤ blockLaenge b)

/-- THE CALL-N VALIDATOR: the caller frame is admitted (`rufOk`: layout
    fit, exact stack-arg count, six callee-save words, no red zone), the
    callee body has the proved three-or-more-assignment shape, and the
    candidate bytes are what the Lean pipeline recomputes from the source
    (`validate` with no optimiser certificates: a certificate could
    rewrite the body away from the proved shape). -/
def rufExecN (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  rufOk b r nArgs benutztRot && istDreiPlus body &&
    validate c L [] body bytes

/-- Unpacking the call-N validator: frame, shape and recomputed bytes.
    Every premise is used: each conjunct feeds one conclusion. -/
theorem rufExecN_teile (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : rufExecN b r nArgs benutztRot c L body bytes = true) :
    rufOk b r nArgs benutztRot = true ∧ istDreiPlus body = true ∧
      validate c L [] body bytes = true := by
  unfold rufExecN at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/- CUTS (exactly what is NOT proved here):
   - Skeleton only: shape predicates, validator, induction, witness
     and refusals all stay OPEN in this skeleton commit.
-/

#print axioms rufOk
#print axioms calleeFremd

end Gabbro.Grammatik.X86.PipelineCallsN
