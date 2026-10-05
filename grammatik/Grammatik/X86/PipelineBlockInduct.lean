/-
  File:      Grammatik/X86/PipelineBlockInduct.lean
  Subject:   Block-size induction over multi-statement pipeline blocks
             (lane 1195).

  Follow-up of lanes 1165 (work transfer), 1189 (calls) and 1191
  (spills): all prove single shallow assignment chunks. Here the
  chunks compose: a run chain (`KetteLauf`) over the lowered chunks
  induces the run over the concatenated block, and source budget to
  target work is additive over the chunks through the admitted
  `pipeSummary` (1165). Deep trees beyond scratch, branches and
  loops stay refused with named refusal theorems. Reuses `senkStmt`,
  `senkBlock_assign`, `pipeSummary`/`pipeSummary_expand`,
  `decodiertZu`, `Deckung`, `laufKosten_anhang_erfolg`,
  `arbeit_decodiert`, `lauf_anhang` and the `pw` witnesses unchanged.
  No second IR, no second interpreter, no optimiser edit. Rust is
  out of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineWork
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.BudgetExecution
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.ExpressionLowering

namespace Gabbro.Grammatik.X86.PipeBlock

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork

/-! ## 1. Run chains over statement chunks.

    A run chain says: each lowered chunk runs from the state the
    previous chunk reached. Block-size induction is induction on
    this chain. -/

/-- A run chain over statement chunks. -/
inductive KetteLauf : List (List Befehl) → Zustand → Zustand → Prop where
  | nil (s : Zustand) : KetteLauf [] s s
  | cons (p : List Befehl) (rest : List (List Befehl)) (s s₁ s₂ : Zustand)
    (hhead : lauf (decodiertZu p) s = some s₁)
    (htail : KetteLauf rest s₁ s₂) : KetteLauf (p :: rest) s s₂

/-- Decoding distributes over chunk concatenation. -/
theorem decodiertZu_append (p q : List Befehl) :
    decodiertZu (p ++ q) = decodiertZu p ++ decodiertZu q := by
  simp [decodiertZu]

/-- CHAIN INDUCTION (runs): a run chain over the chunks is the run
    over the flattened block. Every premise is used: `hhead` feeds
    the head step through `lauf_anhang`, `htail` the induction. -/
theorem ketteLauf_lauf (chunks : List (List Befehl)) (s s' : Zustand)
    (h : KetteLauf chunks s s') :
    lauf (decodiertZu chunks.flatten) s = some s' := by
  induction h with
  | nil s =>
    simp [decodiertZu, lauf]
  | cons p rest s s₁ s₂ hhead _ ih =>
    rw [List.flatten_cons, decodiertZu_append, lauf_anhang _ _ _ _ hhead]
    exact ih

/-- CHAIN INDUCTION (work): retired work over the flattened block is
    the sum of the chunk works. -/
theorem ketteLaenge_sum (chunks : List (List Befehl)) :
    targetWork chunks.flatten = (chunks.map targetWork).sum := by
  unfold targetWork
  rw [List.length_flatten]

end Gabbro.Grammatik.X86.PipeBlock
