module

public import Grammatik.Logik.Vertraege.Pruefer.Auxiliary
public import Grammatik.Logik.Invarianten.Pruefer.Unit

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Pruefer Vertraege.Pruefer

variable {D : Deklaration} [DecidableEq D.Fn]

/-- Every field is produced by a checker procedure below. Reification fields
    in Einheit describe syntax correspondence only; they carry no contract,
    invariant, decrease or interface-refinement proof. -/
structure CheckedUnitLogic (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock) where
  contracts : ∀ f ∈ functions, ContractDuties E.P E.S f
  lockLocal : ∀ lock ∈ locks, ∀ s s', (∀ c ∈ E.S.orte lock, TraegerGleich s s' c) →
    E.S.inv lock s = E.S.inv lock s'
  lockInitial : ∀ lock ∈ locks, E.S.inv lock E.sp0 = true
  axiomLocal : AxEnsLokal E.Q
  pointers : ∀ f ∈ functions, ∀ n (target : D.passt f n = true), PtrZielVerfeinert E.P f n target
  starts : ∀ start ∈ E.starts ++ E.gestartet, ReqAmEintritt E.P start.1 (E.sp0.welt []) start.2
  decreases : ∀ f ∈ functions, ∀ passes Q shared,
    (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
    MassPflicht E.P passes Q E.S shared E.measure (zykS E.P functions) f

def checkUnitLock (E : Einheit D) (lock : D.Lock) :
    Except Refusal (PLift ((∀ s s', (∀ c ∈ E.S.orte lock, TraegerGleich s s' c) →
      E.S.inv lock s = E.S.inv lock s') ∧ E.S.inv lock E.sp0 = true)) := do
  let local ← checkLockLocal E.S E.lockFormulas lock
  let formula ← lockFormula E.S E.lockFormulas lock
  if initial : formula.formula.eval (assignment (E.sp0.welt [])) = true then
    return ⟨local.down, (formula.correct _).mp ((qf_eval _ _).mp initial)⟩
  else .error (.unsupported "lock invariant is false in the initial memory")

def checkStartRequires (E : Einheit D) (start : Σ f : D.Fn, Env D (D.params f)) :
    Except Refusal (PLift (ReqAmEintritt E.P start.1 (E.sp0.welt []) start.2)) := do
  let encoded ← translate (E.P.requires start.1) start.2
  if checked : (lower encoded.payload).eval (assignment (E.sp0.welt [])) = true then
    return ⟨(encoded.bool_iff _).mpr ((lower_denote _ _).mp ((qf_eval _ _).mp checked))⟩
  else .error (.unsupported "declared start does not satisfy its requires")

/-- Whole-unit checking discharges all former user logic. Missing source
    representations and unsupported fragments are explicit refusals. -/
def checkUnitLogic (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Except Refusal (CheckedUnitLogic E functions locks) := do
  let contracts ← checkContracts E.P E.S functions E.lockFormulas budget E.loopHints
  let lockChecks ← collect locks _ (checkUnitLock E)
  let some axiomSources := E.axiomSources
    | .error (.unsupported "oracle predicates are missing their elaborated source expressions")
  let axioms ← collect axiomSources.items _ (checkAxiomLocal E.Q axiomSources)
  let some pointerSignatures := E.pointerSignatures
    | .error (.unsupported "function-pointer interfaces are missing their finite source table")
  let pointers ← checkPointers E.P functions pointerSignatures budget
  let starts ← collect (E.starts ++ E.gestartet) _ (checkStartRequires E)
  let decreases ← collect functions _ (fun f => do
    let hint ← loopHint E.loopHints f
    checkMeasure E.P E.S E.lockFormulas budget hint E.measure (zykS E.P functions) (E.sp0.welt []) f)
  return { contracts := contracts.down
      lockLocal := fun lock member => (lockChecks.down lock member).1
      lockInitial := fun lock member => (lockChecks.down lock member).2
      axiomLocal := fun a => axioms.down a (axiomSources.complete a)
      pointers := pointers.down
      starts := starts.down
      decreases := decreases.down }

def nutzerPflichtGeprueftB (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Bool :=
  (checkUnitLogic E functions locks budget).toOption.isSome

def NutzerPflichtGeprueft (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Prop :=
  ∃ certificate, checkUnitLogic E functions locks budget = .ok certificate

theorem nutzerPflichtGeprueftB_iff (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget) : nutzerPflichtGeprueftB E functions locks budget = true ↔
      NutzerPflichtGeprueft E functions locks budget := by
  unfold nutzerPflichtGeprueftB NutzerPflichtGeprueft
  cases checkUnitLogic E functions locks budget <;> simp

/-- All of premise (b) follows from a true checker result. No user logic
    premise and no proof of a source assertion is an argument. -/
theorem nutzerPflicht_of_geprueft {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {budget : VCBudget} (functionComplete : ∀ f, f ∈ functions) (lockComplete : ∀ lock, lock ∈ locks)
    (accepted : nutzerPflichtGeprueftB E functions locks budget = true) : NutzerPflichtA E := by
  obtain ⟨certificate, computed⟩ := (nutzerPflichtGeprueftB_iff E functions locks budget).mp accepted
  exact
    { logik := ⟨fun passes f => certificate.contracts f (functionComplete f) passes E.Q
        (GeteiltA E.P E.ws) (fun _ shared => shared.1),
        fun lock => certificate.lockLocal lock (lockComplete lock), certificate.axiomLocal,
        fun f => certificate.pointers f (functionComplete f)⟩
      start := ⟨fun lock => certificate.lockInitial lock (lockComplete lock), certificate.starts⟩ }

theorem massPflicht_of_geprueft {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {budget : VCBudget} (complete : ∀ f, f ∈ functions)
    (accepted : nutzerPflichtGeprueftB E functions locks budget = true)
    (passes : Nat) (f : D.Fn) :
    MassPflicht E.P passes E.Q E.S (GeteiltA E.P E.ws) E.measure (zykS E.P functions) f := by
  obtain ⟨certificate, computed⟩ := (nutzerPflichtGeprueftB_iff E functions locks budget).mp accepted
  exact certificate.decreases f (complete f) passes E.Q (GeteiltA E.P E.ws) (fun _ shared => shared.1)

/-- The final, data-dependent gate runs on the actual initial memory and
    start arguments. Program acceptance alone cannot establish this Bool. -/
def unitStartGeprueftB (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock) : Bool :=
  invariantenGeprueftB E functions locks && nutzerPflichtGeprueftB E functions locks

end Gabbro.Grammatik.Zielsatz
