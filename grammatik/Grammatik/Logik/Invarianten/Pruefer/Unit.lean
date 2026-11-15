module

public import Grammatik.Zielsatz.Kern.Spec.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt
open Invarianten.VC Invarianten.Modell Invarianten.Pruefer

variable {D : Deklaration}

/-- Start checks concern every declared table/group/global invariant, even
    when no function writes it. Only reified lock predicates are checked here;
    arbitrary semantic lock predicates retain their start duty in (b). -/
structure CheckedInvariants (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock) where
  program : CheckedProgram E.P E.S functions
  initial : ∀ item ∈ D.invs, InvHaelt E.P item (E.sp0.welt [])
  lockInitial : ∀ lock ∈ locks, (E.lockFormulas lock).isSome = true → E.S.inv lock E.sp0 = true

def checkLockInitial (E : Einheit D) (lock : D.Lock) :
    Except Frag.Refusal (PLift ((E.lockFormulas lock).isSome = true → E.S.inv lock E.sp0 = true)) := do
  match source : E.lockFormulas lock with
  | none => return ⟨fun impossible => by simp [source] at impossible⟩
  | some _ =>
      let formula ← lockFormula E.S E.lockFormulas lock
      if valid : formula.formula.eval (assignment (E.sp0.welt [])) = true then
        return ⟨fun _ => (formula.correct _).mp ((qf_eval _ _).mp valid)⟩
      else .error (.unsupported "lock invariant is false in the declared initial memory")

def checkInvariants (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Except Frag.Refusal (CheckedInvariants E functions locks) := do
  let program ← checkProgram E.P E.S functions E.lockFormulas budget locks
  if valid : program.invariants.formula.eval (assignment (E.sp0.welt [])) = true then
    let locks ← collect locks
      (fun lock => (E.lockFormulas lock).isSome = true → E.S.inv lock E.sp0 = true)
      (checkLockInitial E)
    return {
        program := program
        initial := (program.invariants.correct _).mp ((qf_eval _ _).mp valid)
        lockInitial := locks.down }
  else .error (.unsupported "declared invariant is false in the declared initial memory")

/-- Every invariant declaration is translated and every writer VC is decided
    by Extended.compileWriter and the verified arithmetic decider. Frag.Refusal
    outside the fragment is intentional: invariants never route to user logic.
    Opaque semantic lock predicates are the explicit exception: absent optional
    reification, their existing user duties are retained. No user proof of invariant truth or
    preservation is an input to this Bool. The optional lock evidence proves
    only expression correspondence; no proof kernel executes in the checker. -/
def invariantenGeprueftB (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Bool :=
  (checkInvariants E functions locks budget).toOption.isSome

def InvariantenGeprueft (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget := {}) : Prop :=
  ∃ checked, checkInvariants E functions locks budget = .ok checked

theorem invariantenGeprueftB_iff (E : Einheit D) (functions : List D.Fn) (locks : List D.Lock)
    (budget : VCBudget) :
    invariantenGeprueftB E functions locks budget = true ↔ InvariantenGeprueft E functions locks budget := by
  unfold invariantenGeprueftB InvariantenGeprueft
  cases result : checkInvariants E functions locks budget with
  | error cause => simp [Except.toOption]
  | ok checked => simp [Except.toOption]

/-- The unit gate includes exactly the program gate used by AkzeptiertX. -/
theorem invariantenGeprueftB_program {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {budget : VCBudget} (accepted : invariantenGeprueftB E functions locks budget = true) :
    programInvariantsB E.P E.S functions E.lockFormulas budget locks = true := by
  unfold programInvariantsB
  cases result : checkProgram E.P E.S functions E.lockFormulas budget locks with
  | error cause =>
      simp [invariantenGeprueftB, checkInvariants, result, Except.bind,
        Except.toOption] at accepted
  | ok checked => rfl

/-- Both value and reason return duties, uniformly in execution budget and
    hardware contracts, now follow from the checker. -/
theorem invGut_of_geprueft [DecidableEq D.Fn] {E : Einheit D}
    {functions : List D.Fn} {locks : List D.Lock} {budget : VCBudget}
    (complete : ∀ f, f ∈ functions) (checked : InvariantenGeprueft E functions locks budget)
    (passes : Nat) (f : D.Fn) :
    InvGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
      InvGutGrundA E.P passes E.Q E.S (GeteiltA E.P E.ws) f := by
  obtain ⟨certificate, result⟩ := checked
  exact certificate.program.writers f (complete f) passes E.Q (GeteiltA E.P E.ws)
    (fun _ shared => shared.1)

end Gabbro.Grammatik.Zielsatz
