/-
  File:      Grammatik/X86/PipelineRegAlloc.lean
  Subject:   Pipeline-level register allocation validation (lane 1167).

  A checked register allocator result (untrusted candidate, decided
  validator) for the end-to-end pipeline (`Pipeline.lean`): whole-block
  live ranges from the source block structure (context variables are never
  redefined, so every variable is live throughout), interference-free
  assignment, spill reserves in a private frame region disjoint from every
  source table (`spillSlot` vocabulary of `SpillPrivate.lean`), and
  calling-convention constraints (`rsp`/`rbp` reserved). A validated
  allocation yields a lowering configuration the pipeline validator
  accepts with source meaning preserved (`pipeline_correct`); a
  clobbering allocation is refused (poison probes).

  Reused unchanged: `PipeCfg`/`cfgOk`/`abbOf`, `validate`/`validate_sound`,
  `pipeline_correct`, `Layout`/`LayoutSep`/`WorldRep`/`EnvRepr`, `spillSlot`,
  `Rahmen.schlitzNat`/`schlitzNat_schranke`. No second IR, no second source
  interpreter, no optimiser edit. Spilling a live variable is REFUSED
  (the lowering has no spill code); spill slots are validated as private
  reserves only.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.SpillPrivate
import Grammatik.X86.Stapel

namespace Gabbro.Grammatik.X86.PipeRegAlloc

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline

/-- An untrusted register allocator result for one block: one entry per
    source variable (`some r` = register home, `none` = spilled), one
    spill-slot reserve per variable, and the frame holding the slots. -/
structure PipeRegAlloc where
  belegung : List (Option Register)
  spillVon : List Nat
  rahmen : Rahmen
  deriving DecidableEq, Repr

/-- The positional register list: a spilled variable reads as `rsp`
    (which the validator refuses loudly). -/
def pipeAllocRegs (A : PipeRegAlloc) : List Register :=
  A.belegung.map (fun o => o.getD .rsp)

/-- The lowering configuration under the allocation. -/
def pipeAllocCfg (A : PipeRegAlloc) (c : PipeCfg) : PipeCfg :=
  { c with regs := pipeAllocRegs A }

end Gabbro.Grammatik.X86.PipeRegAlloc
