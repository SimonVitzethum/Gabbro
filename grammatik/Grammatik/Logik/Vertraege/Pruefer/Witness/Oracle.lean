module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.SymbolicBinding
public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.Block
public import Grammatik.Logik.Vertraege.Pruefer.Control.Oracle.End

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.OracleWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt
open Invarianten.VC
open Invarianten.Frag.Symbolic Pruefer.Symbolic SelectionWitness

attribute [local implicit_reducible] Witness.u32Declaration

abbrev u32 := SymbolicWitness.u32

/-- Full-width oracle answers, two declared reasons and writable memory. -/
abbrev declaration : Deklaration :=
  { Witness.u32Declaration with
    gtyp := fun _ => u32
    sigNr := fun _ =>
      { params := [u32], erg := some u32, gruende := 0, haelt := []
        schreibt := fun _ => false, gschreibt := fun _ => true
        konsumiert := [], produziert := [] }
    invarianten_gehalten := fun _ item => nomatch item
    passt_ok := fun _ _ impossible => by cases impossible
    Ax := Bool
    aparams := fun _ => []
    aerg := fun a => if a then none else some u32
    agruende := fun _ => 2
    aschreibt := fun _ _ => false
    agschreibt := fun _ _ => true
    axHerkunft := fun _ => some .software
    axBeleg := fun _ => none
    anbieter := fun _ => none
    anbieter_passt := fun _ _ impossible => by cases impossible }

abbrev contract := vertragVon declaration ()

theorem access (g : declaration.Glob) : gdarf declaration g [] :=
  fun _ member => (List.not_mem_nil member).elim

def storedReturn {Γ : Ctx} (value : Expr declaration Γ [] u32) :
    Endblock declaration contract false Γ [] :=
  .cons (.assignGlob false value rfl (access false)) (.ret (.val value) (List.Perm.refl _))

def storedBlock {Γ : Ctx} (value : Expr declaration Γ [] u32) :
    Block declaration contract false Γ [] [] :=
  .cons (.assignGlob false value rfl (access false))
    (.cons (.ret (.val value) (List.Perm.refl _)) .nil)

def fits (a : declaration.Ax) : RufPasst declaration contract (declaration.asignatur a) [] where
  hw _ impossible := by cases impossible
  hg _ _ := rfl
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh _ impossible := by cases impossible

/-- All eight scalar/optional, block/end and normal/fallible production forms.
    Optional forms bind void too; the unchanged u32 parameter survives havoc. -/
def body (mode : Nat) : Endblock declaration contract false [u32] [] :=
  match mode with
  | 0 => .bindAxiom false .nil rfl (fun _ impossible => by cases impossible)
      (fun _ _ => rfl) (fun _ impossible => by cases impossible) (fun g _ => access g)
      (storedReturn (.var .here))
  | 1 => .bindAxiomElse false .nil rfl (by decide) (fun _ impossible => by cases impossible)
      (fun _ _ => rfl) (fun _ impossible => by cases impossible) (fun g _ => access g)
      (storedReturn (.var (.there .here))) (storedReturn (.var .here))
  | 2 => .bindAxiomOpt none true .nil rfl (fits true)
      (fun _ impossible => by cases impossible) (fun g _ => access g) (storedReturn (.var .here))
  | 3 => .bindAxiomOptElse (some u32) false .nil rfl (fits false)
      (fun _ impossible => by cases impossible) (fun g _ => access g) (by decide)
      (storedReturn (.var (.there .here))) (storedReturn (.var .here))
  | 4 => .cons (.ite .tru
      (.bindAxiom false .nil rfl (fun _ impossible => by cases impossible)
        (fun _ _ => rfl) (fun _ impossible => by cases impossible) (fun g _ => access g)
        (storedBlock (.var .here))) .nil) (storedReturn (.var .here))
  | 5 => .cons (.ite .tru
      (.bindAxiomElse false .nil rfl (by decide) (fun _ impossible => by cases impossible)
        (fun _ _ => rfl) (fun _ impossible => by cases impossible) (fun g _ => access g)
        (storedReturn (.var (.there .here))) (storedBlock (.var .here))) .nil)
      (storedReturn (.var .here))
  | 6 => .cons (.ite .tru
      (.bindAxiomOpt (some u32) false .nil rfl (fits false)
        (fun _ impossible => by cases impossible) (fun g _ => access g) (storedBlock (.var .here))) .nil)
      (storedReturn (.var .here))
  | _ => .cons (.ite .tru
      (.bindAxiomOptElse none true .nil rfl (fits true)
        (fun _ impossible => by cases impossible) (fun g _ => access g) (by decide)
        (storedReturn (.var (.there .here))) (storedBlock (.var .here))) .nil)
      (storedReturn (.var .here))

def program (mode : Nat) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .eq (.var .here) (.glob false (access false))
  rumpf := fun _ => body mode

def symbols : SymEnv declaration Nat [u32] := .cons (.integer (.var 0)) .nil

theorem bounded_zeuge : symbols.Bounded 1 :=
  ⟨fun key member => by have same := List.mem_singleton.mp member; subst key; decide, trivial⟩

def invariants (mode : Nat) : InvariantFormula (program mode) [] :=
  (invariantFormula (program mode) []).toOption.get (by rfl)

abbrev budget : VC.VCBudget := { expansion := 2, depth := 32 }

def compiled (mode : Nat) := ending
  (requiresPolicy (program mode) (entryContext symbols bounded_zeuge))
  (S := SperrInv.leer declaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none))
  budget none budget.depth (body mode) symbols bounded_zeuge
  (contractGoals (program mode) () symbols bounded_zeuge (invariants mode))

/-- These are the real production compiler certificates, with a nonliteral
    postcondition. The 2^32 answers are represented by one fresh key. -/
theorem production_forms_zeuge :
    (List.range 8).all (fun mode => (compiled mode).toOption.isSome) = true := by
  with_unfolding_all rfl

theorem compiled_present (mode : Fin 8) : (compiled mode.val).toOption.isSome = true :=
  List.all_eq_true.mp production_forms_zeuge mode.val (List.mem_range.mpr mode.isLt)

def certificate (mode : Fin 8) := (compiled mode.val).toOption.get (compiled_present mode)

theorem compiled_result (mode : Fin 8) : compiled mode.val = .ok (certificate mode) := by
  have present := compiled_present mode
  cases result : compiled mode.val with
  | error reason => rw [result] at present; cases present
  | ok value => simp only [certificate, result, Except.toOption, Option.get_some]

/-- Only equivalence-preserving alias simplification is reduced. Cooper's
    correctness theorem below proves the universal decisions mathematically. -/
theorem normalized_forms_zeuge : (List.finRange 8).all (fun mode =>
    decide ((Reduce.normalize 8 (certificate mode).formula).val = .tru)) = true := by
  with_unfolding_all rfl

theorem normalized_zeuge (mode : Fin 8) : (Reduce.normalize 8 (certificate mode).formula).val = .tru :=
  of_decide_eq_true (List.all_eq_true.mp normalized_forms_zeuge mode (List.mem_finRange mode))

theorem oracle_vc_valid (mode : Fin 8) (values : Assignment (Key declaration Nat)) :
    (entryVC symbols .tru (certificate mode).formula).denote values := by
  intro _ _ _
  apply ((Reduce.normalize 8 (certificate mode).formula).property values).mp
  rw [normalized_zeuge]
  trivial

theorem specialization_cost_zeuge : (List.finRange 8).all (fun mode => decide (
    argumentSpecializations budget.specializations (declaration.params ()) *
      endSpecializations (program mode.val) (uniformPost (program mode.val) ()) budget.expansion budget.specializations
        ((program mode.val).rumpf ()) ≤ budget.specializations)) = true := by rfl

attribute [local irreducible] entryVC certificate

/-- The strict production gate accepts all eight forms for all typed u32
    answers and poststates, with a nonliteral result/memory relation. -/
theorem production_oracle_acceptance_zeuge (mode : Fin 8) :
    (checkExecution (program mode.val) (SperrInv.leer declaration) (fun _ => none)
      budget none ()).toOption.isSome = true := by
  with_unfolding_all
    apply execution_success (program mode.val) (SperrInv.leer declaration) (fun _ => none) budget none ()
      (by rfl) (invariants mode.val) (by rfl)
      ((parameters (D := declaration) 2 0 [u32]).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
    · exact of_decide_eq_true (List.all_eq_true.mp specialization_cost_zeuge mode (List.mem_finRange mode))
    · intro entry
      rcases entry with ⟨selected, member⟩
      change selected ∈ [symbols] at member
      have same := List.mem_singleton.mp member
      subst selected
      let requirement := (Invarianten.Frag.Symbolic.translate ((program mode.val).requires ()) symbols).toOption.get (by rfl)
      exact environment_success_of_valid (program mode.val) (SperrInv.leer declaration) symbols bounded_zeuge
        (requiresPolicy (program mode.val) _) (fun _ => none) budget none (invariants mode.val) (by rfl)
        requirement (by rfl) (certificate mode) (compiled_result mode) (oracle_vc_valid mode)

/-- Both present and absent oracle bindings commute with statement outcomes. -/
theorem goals_shrinkResult_zeuge
    (runtime : VC.Runtime SymbolicWitness.program (fun _ => []) (SperrInv.leer SymbolicWitness.declaration)) :
    (SymbolicWitness.goals.shrinkResult (some u32)).holds (l := false) () runtime (fun _ => False)
      (.ok SymbolicWitness.world (.cons SymbolicWitness.seven SymbolicWitness.actual)) ↔
    SymbolicWitness.goals.holds (l := false) () runtime (fun _ => False)
      (.ok SymbolicWitness.world SymbolicWitness.actual) :=
  SymbolicWitness.goals.holds_shrinkResult (some u32) () runtime (fun _ => False) _

theorem goals_void_shrinkResult_zeuge
    (runtime : VC.Runtime SymbolicWitness.program (fun _ => []) (SperrInv.leer SymbolicWitness.declaration)) :
    (SymbolicWitness.goals.shrinkResult none).holds (l := false) () runtime (fun _ => False)
      (.ok SymbolicWitness.world SymbolicWitness.actual) ↔
    SymbolicWitness.goals.holds (l := false) () runtime (fun _ => False)
      (.ok SymbolicWitness.world SymbolicWitness.actual) :=
  SymbolicWitness.goals.holds_shrinkResult none () runtime (fun _ => False) _

theorem goals_end_shrinkResult_zeuge
    (runtime : VC.Runtime SymbolicWitness.program (fun _ => []) (SperrInv.leer SymbolicWitness.declaration)) :
    (SymbolicWitness.goals.shrinkResult (some u32)).endHolds (l := false) () runtime (fun _ => False)
      (.zurueck SymbolicWitness.world SymbolicWitness.seven) ↔
    SymbolicWitness.goals.endHolds (l := false) () runtime (fun _ => False)
      (.zurueck SymbolicWitness.world SymbolicWitness.seven) :=
  SymbolicWitness.goals.endHolds_shrinkResult (some u32) () runtime (fun _ => False) _

theorem goals_end_statement_zeuge
    (runtime : VC.Runtime SymbolicWitness.program (fun _ => []) (SperrInv.leer SymbolicWitness.declaration)) :
    SymbolicWitness.goals.endHolds (l := false) () runtime (fun _ => False)
      (.zurueck SymbolicWitness.world SymbolicWitness.seven) ↔
    SymbolicWitness.goals.holds (l := false) () runtime (fun _ => False)
      (.zurueck SymbolicWitness.world SymbolicWitness.seven) :=
  SymbolicWitness.goals.endHolds_to_statement () runtime (fun _ => False) _

end Gabbro.Grammatik.Vertraege.Pruefer.OracleWitness
