module

public import Grammatik.Logik.Vertraege.Pruefer.Duties

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Frag Elim VC

variable {D : Deklaration}

/-- Check declaration syntax and generate the actual bodies' verification
    conditions. The strict contract WP also checks every lock release and
    scoped return; a failing release cannot hide in a permissive error post.
    Requires and ensures are checked by the same traversal, without assuming
    an invariant at entry that the existing semantic duties do not assume. -/
def checkInvariantVC (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {}) :
    Except Frag.Refusal (PLift (∀ f ∈ functions, Vertraege.Pruefer.ContractDuties program S f)) := do
  let _ ← invariantFormula program D.invs
  collect functions (Vertraege.Pruefer.ContractDuties program S)
    (Vertraege.Pruefer.checkFunction program S sources budget none)

/-- Missing lock syntax, unsupported expressions, exhausted source expansion
    and false arithmetic VCs all refuse. No semantic truth proof is an input. -/
def invariantVCB (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S := fun _ => none) (budget : VCBudget := {}) : Bool :=
  (checkInvariantVC program S functions sources budget).toOption.isSome

theorem invariantVCB_sound {program : Programm D} {S : SperrInv D}
    {functions : List D.Fn} {sources : LockSources S} {budget : VCBudget}
    (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget = true) :
    ∀ f, Vertraege.Pruefer.ContractDuties program S f := by
  unfold invariantVCB at accepted
  cases result : checkInvariantVC program S functions sources budget with
  | error cause => simp only [result, Except.toOption, Option.isSome_none,
      Bool.false_eq_true] at accepted
  | ok certificate => exact fun f => certificate.down f (complete f)

/-- The public invariant consequence is uniform in runtime budget, named
    oracle contracts and every shared-atomic rely admitted by the model. -/
theorem invariantVCB_invGutA {program : Programm D} {S : SperrInv D}
    {functions : List D.Fn} {sources : LockSources S} {budget : VCBudget}
    (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget = true)
    (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) (f : D.Fn) :
    InvGutSA program passes Q S shared f ∧ InvGutGrundA program passes Q S shared f :=
  (invariantVCB_sound complete accepted f passes Q shared subset).2

end Gabbro.Grammatik.Invarianten.Pruefer
