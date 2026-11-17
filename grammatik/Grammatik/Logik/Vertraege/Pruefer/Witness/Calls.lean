module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control

@[expose] public section

set_option maxHeartbeats 10000
set_option maxRecDepth 256

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

/-- Two distinct functions retain a real memory read and a discarded u32
    result. The caller must use the strict control compiler, since Basic
    intentionally quantifies over arbitrary, potentially failing handlers. -/
abbrev sharedDeclaration : Deklaration :=
  { u32Declaration with
    Fn := Bool
    sig := fun _ => 0
    sigNr := fun _ =>
      { params := [], erg := some (.int 0 (2 ^ 32 - 1)), gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun _ => false
        konsumiert := [], produziert := [] }
    passt := fun _ _ => false
    passt_ok := fun _ _ impossible => by cases impossible
    rzusage := fun item => nomatch item }

def sharedFits : RufPasst sharedDeclaration (vertragVon sharedDeclaration true)
    (sharedDeclaration.signatur false) [] where
  hw := fun _ impossible => by cases impossible
  hg := fun _ impossible => by cases impossible
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun _ impossible => nomatch impossible

def sharedProgram : Programm sharedDeclaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun branch => match branch with
    | false => .ret (.val (.widen (by decide) (by decide)
        (.glob false (fun _ member => (List.not_mem_nil member).elim)))) (List.Perm.refl _)
    | true => .cons (.call false .nil sharedFits rfl)
        (.ret (.val (.widen (by decide) (by decide) (.lit 7))) (List.Perm.refl _))

open Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic Symbolic SelectionWitness

abbrev sharedBudget : VCBudget := { depth := 8, expansion := 0, specializations := 4 }
abbrev sharedSymbols : SymEnv sharedDeclaration Nat (sharedDeclaration.params true) := .nil

theorem sharedBounded : sharedSymbols.Bounded 0 := trivial

def sharedInvariants : InvariantFormula sharedProgram (sharedDeclaration.invs.filter (schuldet true)) :=
  (invariantFormula sharedProgram []).toOption.get (by rfl)

def sharedCompiled := ending (requiresPolicy sharedProgram (entryContext sharedSymbols sharedBounded))
  (S := SperrInv.leer sharedDeclaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer sharedDeclaration) (fun _ => none)) sharedBudget none 8
  (sharedProgram.rumpf true) sharedSymbols sharedBounded (contractGoals sharedProgram true sharedSymbols sharedBounded sharedInvariants)

def sharedFormula : Frag.LProp (Key sharedDeclaration Nat) :=
  .and .tru (.and (.imp .tru (.and .tru .tru)) .tru)

theorem sharedCompiled_shape : sharedCompiled.map Certificate.formula = .ok sharedFormula := by
  unfold sharedCompiled
  simp only [sharedProgram]
  rw [ending.eq_6]
  rw [statement.eq_def]
  simp only [ending.eq_2]
  rfl

theorem sharedCompiled_present : sharedCompiled.toOption.isSome = true := by
  have shape := sharedCompiled_shape
  cases result : sharedCompiled with
  | error cause => rw [result] at shape; cases shape
  | ok value => rfl

def sharedCertificate := sharedCompiled.toOption.get sharedCompiled_present

theorem sharedCompiled_result : sharedCompiled = .ok sharedCertificate := by
  have present := sharedCompiled_present
  cases result : sharedCompiled with
  | error cause => rw [result] at present; cases present
  | ok value => simp only [sharedCertificate, result, Except.toOption, Option.get_some]

theorem sharedCompiled_valid (values : Assignment (Key sharedDeclaration Nat)) :
    sharedCertificate.formula.denote values := by
  have shape := sharedCompiled_shape
  rw [sharedCompiled_result] at shape
  have same := Except.ok.inj shape
  change sharedCertificate.formula = sharedFormula at same
  rw [same]
  exact ⟨trivial, ⟨fun _ => ⟨trivial, trivial⟩, trivial⟩⟩

attribute [local irreducible] entryVC sharedCertificate

theorem shared_decided :
    decideB (close (lower (entryVC sharedSymbols .tru sharedCertificate.formula)))
      (close_closed _) = true := by
  apply (close_decide_true_iff (lower (entryVC sharedSymbols .tru sharedCertificate.formula))).mpr
  intro values
  apply (lower_denote (entryVC sharedSymbols .tru sharedCertificate.formula) values).mpr
  unfold entryVC
  intro _ _ _
  exact sharedCompiled_valid values

theorem environment_success_of_valid_zeuge :
    (checkEnvironment sharedProgram (SperrInv.leer sharedDeclaration) sharedSymbols sharedBounded
      (requiresPolicy sharedProgram _) (fun _ => none) sharedBudget none sharedInvariants).toOption.isSome = true := by
  let requirement := (Invarianten.Frag.Symbolic.translate (sharedProgram.requires true) sharedSymbols).toOption.get (by rfl)
  exact environment_success_of_valid (D := sharedDeclaration) (f := true) (next := 0)
    sharedProgram (SperrInv.leer sharedDeclaration) sharedSymbols sharedBounded (requiresPolicy sharedProgram _)
    (fun _ => none) sharedBudget none sharedInvariants (by rfl) requirement (by rfl)
    sharedCertificate sharedCompiled_result (by
      intro values
      unfold entryVC
      intro _ _ _
      exact sharedCompiled_valid values)

/-- The actual program contract gate accepts both functions at zero domain
    expansion and a four-case work budget, including the strict caller. -/
theorem uniform_wide_program_zeuge :
    KontrakteGeprueftB sharedProgram (SperrInv.leer sharedDeclaration) [false, true]
      (fun _ => none) sharedBudget = true := by
  with_unfolding_all
    apply contracts_success sharedProgram (SperrInv.leer sharedDeclaration) (fun _ => none) sharedBudget [false, true]
    intro f
    cases f with
    | false => rfl
    | true =>
      apply function_success sharedProgram (SperrInv.leer sharedDeclaration) (fun _ => none) sharedBudget none true
      · rfl
      · rfl
      · apply execution_success sharedProgram (SperrInv.leer sharedDeclaration) (fun _ => none) sharedBudget none true
          (by rfl) sharedInvariants (by rfl)
          ((parameters (D := sharedDeclaration) 0 0 []).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
        · change 2 ≤ 4
          decide
        · intro entry
          rcases entry with ⟨selected, member⟩
          cases selected
          let requirement := (Invarianten.Frag.Symbolic.translate (sharedProgram.requires true) sharedSymbols).toOption.get (by rfl)
          exact environment_success (D := sharedDeclaration) (f := true) (next := 0) sharedProgram (SperrInv.leer sharedDeclaration) sharedSymbols sharedBounded
            (requiresPolicy sharedProgram _) (fun _ => none) sharedBudget none sharedInvariants (by rfl)
            requirement (by rfl) sharedCertificate sharedCompiled_result shared_decided

end Gabbro.Grammatik.Vertraege.Pruefer.Witness
