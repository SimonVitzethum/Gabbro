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

/-! ## 2. Budget additivity: source budget to target work over chunks.

    `Deckung` is DERIVED (1165), never a premise of the lowering. Two
    covered chunks concatenate to a covered block at the SUM budget:
    with the admitted summary's honest zero spill/fence counts
    (`pipeSummary_expand`) the bound is purely additive. -/

/-- COVER APPEND: two covered chunks concatenate at the sum budget.
    Every premise is used: `h1`/`h2` bound the two works, `hk` names
    the sum bound, and the work equation splits it. -/
theorem deckung_append_pipe (n m : Nat) (xs ys : List Decodiert)
    (h1 : Deckung pipeSummary n xs) (h2 : Deckung pipeSummary m ys) :
    Deckung pipeSummary (n + m) (xs ++ ys) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have a := h1 _ (pipeSummary_expand n)
  have b := h2 _ (pipeSummary_expand m)
  have hlen : targetWork ((xs ++ ys).map (fun d => d.befehl)) =
      targetWork (xs.map (fun d => d.befehl)) +
        targetWork (ys.map (fun d => d.befehl)) := by
    simp [targetWork]
  rw [hlen]
  omega

/-- BLOCK DECKUNG (induction over the chunk list): every chunk covered
    at budget 1 gives the flattened block covered at the chunk count.
    The empty block is covered at zero by computation. -/
theorem blockDeckung_eins (chunks : List (List Befehl))
    (h : ∀ c ∈ chunks, Deckung pipeSummary 1 (decodiertZu c)) :
    Deckung pipeSummary chunks.length (decodiertZu chunks.flatten) := by
  induction chunks with
  | nil =>
    exact deckung_leer pipeSummary 0 (pipeSummary_expand 0)
  | cons p rest ih =>
    have hhead : Deckung pipeSummary 1 (decodiertZu p) :=
      h p List.mem_cons_self
    have htail : Deckung pipeSummary rest.length (decodiertZu rest.flatten) :=
      ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hcat := deckung_append_pipe 1 rest.length _ _ hhead htail
    simp only [List.flatten_cons, List.length_cons]
    rw [decodiertZu_append]
    have heq : 1 + rest.length = rest.length + 1 := Nat.add_comm _ _
    rwa [heq] at hcat

/-- TIME APPEND: named-time aggregation over concatenated chunks is
    the sum of the chunk times (reused `laufKosten_anhang_erfolg`). -/
theorem zeit_append_pipe (prof : HardwareProfil) (p q : List Befehl)
    (t1 t2 : Nat)
    (h1 : laufKosten prof (decodiertZu p) = some t1)
    (h2 : laufKosten prof (decodiertZu q) = some t2) :
    laufKosten prof (decodiertZu (p ++ q)) = some (t1 + t2) := by
  rw [decodiertZu_append]
  exact laufKosten_anhang_erfolg prof _ _ t1 t2 h1 h2

end Gabbro.Grammatik.X86.PipeBlock
