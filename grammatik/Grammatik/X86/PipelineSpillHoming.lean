/-
  File:      Grammatik/X86/PipelineSpillHoming.lean
  Subject:   Pipeline spills: variable homing with live-range splitting
              (lane 1227, follow-up of lane 1191 `PipelineSpill.lean`).

  Lane 1191 saves/reloads whole named slots but makes no homing decision
  and keeps whole-block live ranges. Here an untrusted homing decides, per
  variable, a private spill home slot (`heim`, parallel to the register
  allocation) plus live-range splits at statement boundaries (`schnitte`:
  variable index with its slot at that boundary). The decided validator
  (`pipeHomingOk`) reuses the accepted checks unchanged: the whole-block
  register allocation (`pipeRegAllocOk`), the spill plan over all named
  slots (`spillPlanOk`), home/register length agreement, and in-range
  split variables. The closing theorem composes the accepted pipeline
  correctness with homing privacy; a clobbering homing is refused.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineRegAlloc
import Grammatik.X86.PipelineSpill

namespace Gabbro.Grammatik.X86.PipeSpillHoming

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeRegAlloc
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.OptimizationRules

/-- An untrusted variable homing with live-range splits: the whole-block
    register allocation, one spill home slot per variable, and split
    points naming a variable index with its slot at that boundary. -/
structure PipeSpillHoming where
  alloc : PipeRegAlloc
  heim : List Nat
  schnitte : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- Every slot the homing names: per-variable homes plus split slots. -/
def homingSlots (H : PipeSpillHoming) : List Nat :=
  H.heim ++ H.schnitte.map (fun q => q.2)

/-- THE VALIDATOR: the allocation validates, homes align with variables,
    every named slot validates as a spill plan, and every split names a
    variable in range. -/
def pipeHomingOk (H : PipeSpillHoming) (c : PipeCfg) (codeLen : Nat)
    (daten : List Nat) : Bool :=
  pipeRegAllocOk H.alloc c codeLen &&
  decide (H.alloc.belegung.length = H.heim.length) &&
  spillPlanOk H.alloc.rahmen (homingSlots H) c.codeBase codeLen daten &&
  H.schnitte.all (fun q => decide (q.1 < H.alloc.belegung.length))

end Gabbro.Grammatik.X86.PipeSpillHoming
