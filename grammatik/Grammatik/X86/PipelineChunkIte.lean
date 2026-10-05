/-
  File:      Grammatik/X86/PipelineChunkIte.lean
  Subject:   Per-chunk runs and coverage DERIVED for if/else and checks
             (lane 1263, follow-up of lane 1219 `PipelineChunkDerive`).

  Lane 1219 derives per-chunk runs/coverage only for `assignSlot`
  chains; `ite`, checks, loops and calls are refused there. Here the
  chunk run/coverage premises for `ite` and bound checks
  (`Block.pruefung`) are derived from the lowering alone: the accepted
  `senkBlock` of a closed single-ite / single-check chunk IS the
  condition code plus the accepted branch lowerings with the decided
  jump layout (`iteCode`, `sprungOk`) resp. the reason-exit jump with
  its address equation (`senkPruef`), and the fetched-byte run plus
  coverage follow from the admitted layout/representation. Loops
  (`traverse`) and calls (`call`, `bindCall`) stay refused with named
  theorems and firing poison probes. No second IR, no second
  interpreter, no optimiser edit, no existing-file edit. Rust is out
  of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineChunkDerive
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineWorkBranches
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.BudgetExecution

namespace Gabbro.Grammatik.X86.PipeChunkIte

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeChunkDerive
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipeWorkBranches
open Gabbro.Grammatik.X86.PipeBlock

variable {D : Deklaration} {V : Vertrag D}

/-- The validator: recompute the closed-chunk lowering and accept the
    candidate bytes only if they are its encoding. -/
def iteCheckValidate (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  match senkBlock c L 0 b with
  | some prog => decide (bytes = encodeAll prog)
  | none => false

/- CUTS:
    - Skeleton only: the validator shape; inversions, derived runs,
      coverage, jump-layout facts, closings and refusals follow.
    - OPEN: everything listed in the module header.
-/

#print axioms iteCheckValidate

end Gabbro.Grammatik.X86.PipeChunkIte
