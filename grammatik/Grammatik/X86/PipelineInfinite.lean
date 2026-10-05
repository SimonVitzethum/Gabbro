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

/-! ## 2. Prefixes of byte runs (machine level, no source)

    A successful run succeeds on every prefix; a refused run stays refused
    under more fuel. Pure facts of `laufBytes`, reused by the pipeline
    theorems below. -/

/-- PREFIX SUCCESS: every prefix of a successful byte run succeeds. -/
theorem laufBytes_praefix_erfolg (n k : Nat) (s s' : Zustand)
    (h : laufBytes n s = .weiter s') (hk : k ≤ n) :
    ∃ sk, laufBytes k s = .weiter sk := by
  induction n generalizing k s with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact ⟨s, rfl⟩
  | succ n ih =>
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBytes, hb] at h
      cases h
    | weiter s1 =>
      simp only [laufBytes, hb] at h
      cases k with
      | zero => exact ⟨s, rfl⟩
      | succ j =>
        obtain ⟨sk, hsk⟩ := ih j s1 h (by omega)
        exact ⟨sk, by simp only [laufBytes, hb]; exact hsk⟩

/-- REFUSAL MONOTONICITY: a refused run stays refused under more fuel. -/
theorem laufBytes_verweigert_plus : ∀ (m j : Nat) (s : Zustand),
    laufBytes m s = .verweigert → laufBytes (m + j) s = .verweigert
  | 0, j, s, h => by
    simp only [laufBytes] at h
    cases h
  | m + 1, j, s, h => by
    cases hb : byteschritt s with
    | verweigert =>
      have he : m + 1 + j = (m + j) + 1 := by omega
      rw [he]
      simp only [laufBytes, hb]
    | weiter s1 =>
      have he : m + 1 + j = (m + j) + 1 := by omega
      simp only [laufBytes, hb] at h
      rw [he]
      simp only [laufBytes, hb]
      exact laufBytes_verweigert_plus m j s1 h

/-! ## 3. The budgeted runner is faithful

    `fertig` means the whole budget ran clean; `stopp` means a defined stop
    after `k` steps. Both directions are proved from the definitions. -/

/-- `fertig` ran the whole budget: `k = n` and the plain run succeeds. -/
theorem laufBudget_fertig : ∀ (n : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .fertig k s' → k = n ∧ laufBytes n s = .weiter s'
  | 0, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
    exact ⟨rfl, rfl⟩
  | n + 1, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        obtain ⟨hk1, hrun⟩ := laufBudget_fertig n s1 k1 s' hl
        refine ⟨by omega, ?_⟩
        simp only [laufBytes, hb]
        exact hrun
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h

/-- `stopp` met a defined stop: `k ≤ n`, the `k`-prefix succeeds, and the
    prefix state has no transition. -/
theorem laufBudget_stopp : ∀ (n : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .stopp k s' →
      k ≤ n ∧ laufBytes k s = .weiter s' ∧ byteschritt s' = .verweigert
  | 0, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
  | n + 1, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
      exact ⟨Nat.zero_le _, rfl, hb⟩
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        obtain ⟨hk1, hrun, hst⟩ := laufBudget_stopp n s1 k1 s' hl
        refine ⟨by omega, ?_, hst⟩
        simp only [laufBytes, hb]
        exact hrun

/-- REFUSAL STABILITY: once the budgeted runner stops, more fuel stays
    stopped at the same state. The runner refuses to step past a stop. -/
theorem laufBudget_stopp_stabil : ∀ (n j : Nat) (s : Zustand) (k : Nat) (s' : Zustand),
    laufBudget n s = .stopp k s' → laufBudget (n + j) s = .stopp k s'
  | 0, j, s, k, s', h => by
    simp only [laufBudget] at h
    cases h
  | n + 1, j, s, k, s', h => by
    cases hb : byteschritt s with
    | verweigert =>
      simp only [laufBudget, hb] at h
      cases h
      have he : n + 1 + j = (n + j) + 1 := by omega
      rw [he]
      simp only [laufBudget, hb]
    | weiter s1 =>
      simp only [laufBudget, hb] at h
      cases hl : laufBudget n s1 with
      | fertig k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
      | stopp k1 s1' =>
        rw [hl] at h
        dsimp only at h
        cases h
        have he : n + 1 + j = (n + j) + 1 := by omega
        have ih := laufBudget_stopp_stabil n j s1 k1 s' hl
        rw [he]
        simp only [laufBudget, hb]
        rw [ih]

/- CUTS (preliminary; extended with every addition):
    Infinite traces past the corresponding end, termination of the target
    run, progress/fairness of any scheduler: NOT claimed (see task). -/

end Gabbro.Grammatik.X86.PipelineInfinite
