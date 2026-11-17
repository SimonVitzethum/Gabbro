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
    correctness theorem below proves the universal decision mathematically. -/
theorem normalized_scalar_zeuge : (Reduce.normalize 8 (certificate 0).formula).val = .tru := by
  with_unfolding_all rfl

theorem scalar_vc_valid (values : Assignment (Key declaration Nat)) :
    (entryVC symbols .tru (certificate 0).formula).denote values := by
  intro _ _ _
  apply ((Reduce.normalize 8 (certificate 0).formula).property values).mp
  rw [normalized_scalar_zeuge]
  trivial

attribute [local irreducible] entryVC certificate

/-- The strict production gate accepts all u32 oracle answers and poststates,
    with a nonliteral result/memory relation and an enumeration budget of two. -/
theorem production_oracle_acceptance_zeuge :
    (checkExecution (program 0) (SperrInv.leer declaration) (fun _ => none)
      budget none ()).toOption.isSome = true := by
  apply execution_success (program 0) (SperrInv.leer declaration) (fun _ => none) budget none ()
    (by rfl) (invariants 0) (by rfl)
    ((parameters (D := declaration) 2 0 [u32]).toOption.get (by rfl)) (by rfl)
  · change 1 ≤ 16384
    decide
  · intro entry
    rcases entry with ⟨selected, member⟩
    change selected ∈ [symbols] at member
    have same := List.mem_singleton.mp member
    subst selected
    let requirement := (Invarianten.Frag.Symbolic.translate ((program 0).requires ()) symbols).toOption.get (by rfl)
    exact environment_success_of_valid (program 0) (SperrInv.leer declaration) symbols bounded_zeuge
      (requiresPolicy (program 0) _) (fun _ => none) budget none (invariants 0) (by rfl)
      requirement (by rfl) (certificate 0) (compiled_result 0) scalar_vc_valid

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

