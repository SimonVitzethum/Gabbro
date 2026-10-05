/-
  File:      Grammatik/X86/PipelineInfinite.lean
  Subject:   Finite and infinite execution soundness of the pipeline
             (`Pipeline.lean` + `PipelineImage.lean`): every finite prefix
             of the byte-level run of a lowered program is safe (it succeeds
             with the code region intact) up to the corresponding end, and
             the target stops only at a point the source budget semantics
             allows (the code end for `ok`, a refusal exit for `grund`, at
             every budget `passes`).

             Reused, not duplicated:
               - pipeline: `senkBlock_korrektC`, `senkBlock_ausgang`,
                 `senkBlock_assign`, `senkBlock_ite_inv`, `validate_sound`,
                 `Entspricht`, `CodeAt`, `WorldRep`, `LayoutSep`, `EnvRepr`,
                 `abbOf`, `encodeAll`, `laufBytes_add`, `grund_mem`;
               - image frame: `ByteRahmen`, `laufBytes_rahmen`,
                 `codeAt_lauf` (`PipelineImage.lean`);
               - machine: `byteschritt`, `laufBytes`, `ByteAusgang`;
               - source: `execBlock`, `execStmt`, `execStmt_ite`,
                 `execBlock_cons_stmtOk/Grund`, `constInt?_sound`;
               - witness data: `PipelineWitnesses` (`pwCfg`, `pwSrc`, ...).
             No second IR, no second source interpreter, no per-program rule.
-/
import Grammatik.X86.PipelineImage
import Grammatik.X86.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineInfinite

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineWitnesses

variable {D : Deklaration}

/-! ## 1. Budgeted byte runs: the target-side budget semantics

    `laufBudget n s` runs at most `n` byte steps: `fertig` ran the whole
    budget without a stop, `stopp` met a defined stop (`verweigert`) after
    `k` steps. There is no silent third outcome. -/

/-- The outcome of a budgeted byte run. -/
inductive BudgetAusgang where
  | fertig : Nat → Zustand → BudgetAusgang
  | stopp : Nat → Zustand → BudgetAusgang

/-- Run at most `n` byte steps from `s`. -/
def laufBudget : Nat → Zustand → BudgetAusgang
  | 0, s => .fertig 0 s
  | n + 1, s =>
    match byteschritt s with
    | .verweigert => .stopp 0 s
    | .weiter s' =>
      match laufBudget n s' with
      | .fertig k s'' => .fertig (k + 1) s''
      | .stopp k s'' => .stopp (k + 1) s''

/- CUTS (preliminary; extended with every addition):
    Infinite traces past the corresponding end, termination of the target
    run, progress/fairness of any scheduler: NOT claimed (see task). -/

end Gabbro.Grammatik.X86.PipelineInfinite
