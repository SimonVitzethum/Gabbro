/-
  File:      Grammatik/X86/PipelineSpillSplice.lean
  Subject:   Pipeline spills: splice save/reload at split points,
             callee-saved and argument handling (lane 1257).

  Follow-up of lane 1191 (`PipelineSpill.lean`): the save/reload
  fragments exist there but no bytes are spliced at split points, and
  calls/callee-saved/argument passing are not covered. Here a split
  point names a position in the lowered program with a slot, a
  register and a direction; splicing inserts the 1191 fragment there.
  The closing theorem preserves the source meaning and the privacy of
  the frame; callee-saved/argument handling reuses `PipelineCalls`
  (`rufOk`, `calleeGerettet`, `rufParam_orte`) over the `Stapel`
  layout (`Belegung`: spills at bare indices, callee-saved behind
  them, stack arguments last).

  Reused unchanged: `spillSaveCode`/`spillLoadCode`/`spillSave_lauf`/
  `spillLoad_lauf`/`spillPlanOk` and its legs/`spill_schlitze_getrennt`/
  `spill_haelt_bedeutung`, `pipeline_correct`, `rufOk`/`rufOk_teile`/
  `rufParam_orte`/`calleeGerettet`/`rufOk_argSchranke`/`rufOk_getrennt`,
  `spill_gerettet_getrennt`/`bereich_getrennt`, `lauf_anhang`.
  No second IR, no second source interpreter, no optimiser edit.
-/
import Grammatik.X86.PipelineSpill
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineCalls

namespace Gabbro.Grammatik.X86.PipeSpillSplice

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.PipelineCalls

/-- Splice direction: save the register into the slot, or reload the
    slot into the register. -/
inductive SpleissRichtung where
  | sichern | laden
  deriving DecidableEq, Repr

/-- A split point: position in the lowered program, spill slot,
    register saved/reloaded, direction. -/
structure SpleissPunkt where
  pos : Nat
  schlitz : Nat
  reg : Register
  richtung : SpleissRichtung
  deriving DecidableEq, Repr

/-- The fragment spliced at a split point: lane 1191's save/reload
    code for the point's slot and register. -/
def spleissFrag (c : PipeCfg) (r : Rahmen) (p : SpleissPunkt) : List Befehl :=
  match p.richtung with
  | .sichern => spillSaveCode c r p.schlitz p.reg
  | .laden => spillLoadCode c r p.schlitz p.reg

/- CUTS:
     - Skeleton only: split-point type and fragment selection over the
       accepted 1191 fragments. Run lemmas, multi-splice, validator,
       closing, call handling, refusals, probes and witnesses OPEN.
-/

#print axioms SpleissPunkt
#print axioms spleissFrag

end Gabbro.Grammatik.X86.PipeSpillSplice
