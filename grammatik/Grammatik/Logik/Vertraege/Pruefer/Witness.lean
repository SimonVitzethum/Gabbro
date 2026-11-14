module

public import Grammatik.Logik.Vertraege.Pruefer.Fixtures

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer Zielsatz

/-- These computations are isolated from the compiler path. The lead must
    measure them against the repository's per-declaration time limit. -/
theorem increment_accepted_zeuge : KontrakteGeprueftB increment (SperrInv.leer declaration) [()] = true := by
  decide

theorem falseEnsures_refused_zeuge : KontrakteGeprueftB falseEnsures (SperrInv.leer declaration) [()] = false := by
  decide

/-- The false ensures has a concrete, typed counterexample: x=4 and result=5. -/
theorem falseEnsures_counterexample_zeuge :
    ReqAmEintritt falseEnsures () world arguments ∧
    ¬ EnsAmRueck falseEnsures () world world arguments ⟨5, by decide, by decide⟩ := by
  constructor
  · decide
  · decide

theorem unit_logic_accepted_zeuge : nutzerPflichtGeprueftB unit [()] [] = true := by
  decide

theorem invariant_gate_zeuge : invariantenGeprueftB unit [()] [] = true := by
  decide

/-- Full checker acceptance rules out a corollary whose new gate always
    refuses. Structural checks reuse the already established VC decisions. -/
theorem checker_accepted_zeuge :
    akzeptiertX_pruefer.akzeptiert unit [()] [] [.inl (), .inr false, .inr true] = true := by
  have core : AkzeptiertX unit.P unit.S [()] [] [.inl (), .inr false, .inr true] unit.ws = true := by
    unfold AkzeptiertX
    rw [increment_accepted_zeuge]
    simp only [Bool.and_true]
    decide
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨core, rfl⟩, Kernzelle.akkuStartB_leer unit⟩,
      invariant_gate_zeuge⟩, unit_logic_accepted_zeuge⟩

/-- Non-degenerate witness of the entire derived former user obligation. -/
theorem nutzerPflicht_of_akzeptiert_zeuge : NutzerPflichtA unit :=
  nutzerPflicht_of_akzeptiert ⟨[()], fun f => by cases f; exact List.mem_cons_self⟩
    ⟨[], fun lock => nomatch lock⟩ checker_accepted_zeuge

/-- The strengthened concrete checker refuses a wrong postcondition. -/
theorem checker_falseEnsures_refused_zeuge :
    akzeptiertX_pruefer.akzeptiert falseUnit [()] [] [.inl (), .inr false, .inr true] = false := by
  have refused : nutzerPflichtGeprueftB falseUnit [()] [] = false := by decide
  change (_ && nutzerPflichtGeprueftB falseUnit [()] []) = false
  rw [refused, Bool.and_false]

/-- An actually conforming pointer target, with a nontrivial interface pre
    and result-dependent post. This exercises both refinement directions. -/
def pointerDeclaration : Deklaration :=
  { declaration with
    passt := fun _ n => decide (n = 0)
    passt_ok := fun _ _ _ => SigPasst.refl _ _ }

def pointerProgram : Programm pointerDeclaration where
  invariante := fun item => nomatch item
  requires := fun _ => .lt (.var .here) (.lit 10)
  ensures := fun _ => .eq (.var .here) (.add (.var (.there .here)) (.lit 1))
  rumpf := fun _ => .ret (.val (.add (.var .here) (.lit 1))) (List.Perm.refl _)
  ptrVertrag := fun _ =>
    { pre := .lt (.var .here) (.lit 10)
      post := .eq (.var .here) (.add (.var (.there .here)) (.lit 1)) }

def pointerLayout : PointerSignatures pointerDeclaration where
  count := 1
  outside := fun _ n beyond => by
    change decide (n = 0) = false
    simp only [decide_eq_false_iff_not]
    omega

theorem pointer_refinement_accepted_zeuge :
    (checkPointers pointerProgram [()] pointerLayout).toOption.isSome = true := by decide

theorem pointer_target_present_zeuge : pointerDeclaration.passt () 0 = true := by decide

end Gabbro.Grammatik.Vertraege.Pruefer.Witness
