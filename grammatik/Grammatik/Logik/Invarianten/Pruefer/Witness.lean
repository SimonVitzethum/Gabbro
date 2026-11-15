module

public import Grammatik.Logik.Invarianten.Pruefer.Goal
public import Grammatik.Logik.Invarianten.VC.Witness
import all Batteries.Data.Except

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.Witness

open Frag Elim VC Modell Zielsatz
open VC.Witness

/-- A real unit: a nonempty invariant family, one writer, a declared start
    and initialized len = cap = 4. No invariant proof is stored in the unit. -/
def unit : Einheit declaration where
  P := { program with ptrVertrag := fun _ => { pre := invariant, post := .tru } }
  S := SperrInv.leer declaration
  Q := fun item => nomatch item
  starts := [⟨(), .nil⟩]
  sp0 := counterexampleWorld.speicher
  axiomSources := some
    { items := []
      complete := fun item => nomatch item
      resources := fun item => nomatch item
      expression := fun item => nomatch item
      correct := fun item => nomatch item }
  pointerSignatures := some
    { count := 1
      outside := fun _ n beyond => by
        change decide (0 = n) = false
        simp only [decide_eq_false_iff_not]
        omega }

/-- The bad unit differs only in the writer body. -/
def badUnit : Einheit declaration :=
  { unit with P := { unit.P with rumpf := fun _ => unguarded } }

/-- Evaluation is isolated in this witness module. The lead measures it
    against the few-seconds proof limit; it is not a compiler-path proof. -/
theorem accepted_zeuge : invariantenGeprueftB unit [()] [] = true := by decide +kernel

/-- The complete concrete checker accepts the fixture, not just an isolated
    VC emitter. Structural components are small independent decisions; the
    arithmetic program gate reuses the already established unit decision. -/
theorem checker_accepted_zeuge :
    akzeptiertX_pruefer.akzeptiert unit [()] [] [.inl (), .inr false, .inr true] = true := by
  have programAccepted := invariantenGeprueftB_program accepted_zeuge
  have contracts : Vertraege.Pruefer.KontrakteGeprueftB unit.P unit.S [()] unit.lockFormulas = true := by
    decide +kernel
  have logic : nutzerPflichtGeprueftB unit [()] [] = true := by decide +kernel
  have core : AkzeptiertX unit.P unit.S [()] [] [.inl (), .inr false, .inr true]
      unit.ws [] [] [] [] unit.lockFormulas = true := by
    unfold AkzeptiertX
    rw [programAccepted, contracts]
    simp only [Bool.and_true]
    decide +kernel
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, logic⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, accepted_zeuge⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, Kernzelle.akkuStartB_leer unit⟩
  exact Bool.and_eq_true_iff.mpr ⟨core, besitzB_leer rfl⟩

theorem invariant_duties_zeuge (passes : Nat) :
    InvGutSA unit.P passes unit.Q unit.S (GeteiltA unit.P unit.ws) () ∧
      InvGutGrundA unit.P passes unit.Q unit.S (GeteiltA unit.P unit.ws) () :=
  invGut_of_geprueft (fun f => by cases f; exact List.mem_cons_self)
    ((invariantenGeprueftB_iff unit [()] [] {}).mp accepted_zeuge) passes ()

theorem initial_zeuge : ∀ item ∈ declaration.invs, InvHaelt unit.P item (unit.sp0.welt []) :=
  invariantenStart_of_geprueft ((invariantenGeprueftB_iff unit [()] [] {}).mp accepted_zeuge)

theorem refused_zeuge : invariantenGeprueftB badUnit [()] [] = false := by decide +kernel

/-- A false invariant decision gates the complete checker regardless of the
    other structural components. -/
theorem checker_refused_zeuge :
    akzeptiertX_pruefer.akzeptiert badUnit [()] [] [.inl (), .inr false, .inr true] = false := by
  change ((_ && invariantenGeprueftB badUnit [()] []) && _) = false
  rw [refused_zeuge, Bool.and_false, Bool.false_and]

/-- A concrete typed counterexample accompanies the refused unguarded writer:
    len = cap = 4 initially, then len = 5 and cap = 4 after the writer. -/
theorem counterexample_zeuge :
    eval counterexampleWorld invariant counterexampleWorld .nil = true ∧
    (match execEnd oracle 0 calls unguarded counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false :=
  ⟨counterexample_entry_zeuge, counterexample_step_zeuge⟩

/-- No writer may conceal an unsupported invariant declaration. Even a unit
    with no enumerated functions fails declaration translation first. -/
def nonlinearUnit : Einheit declaration :=
  { unit with
    P := { unit.P with
      invariante := fun _ => .le (.mul lengthValue capacityValue) (.lit 10) } }

theorem outside_fragment_refused_zeuge :
    invariantenGeprueftB nonlinearUnit [] [] = false := by decide +kernel

end Gabbro.Grammatik.Invarianten.Pruefer.Witness
