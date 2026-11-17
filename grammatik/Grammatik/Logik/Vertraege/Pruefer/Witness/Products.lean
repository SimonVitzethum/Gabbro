module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control
public import Grammatik.Logik.Invarianten.Frag.Symbolic.ProductWitness

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.ProductProductionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Pruefer.Symbolic SelectionWitness

attribute [local implicit_reducible] Witness.u32Declaration

abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev pair : Ty := .prod 0 [u32, u32]
abbrev declaration : Deklaration :=
  { Witness.u32Declaration with
    sigNr := fun _ =>
      { params := [pair], erg := some u32, gruende := 0, haelt := []
        schreibt := fun _ => false, gschreibt := fun _ => false, konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible }

def program : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .eq (.var .here) (.prodGet (.var (.there .here)) .head)
  rumpf := fun _ => .ret (.val (.prodGet (.var .here) .head)) (List.Perm.refl _)

def components : SymEnv declaration Nat [u32, u32] :=
  .cons (.integer (.var 0)) (.cons (.integer (.var 1)) .nil)

def symbols : SymEnv declaration Nat [pair] := components.packProduct 0 [u32, u32]

theorem components_bounded : components.Bounded 2 := by
  refine ⟨?_, ?_, trivial⟩
  · intro key member; have same := List.mem_singleton.mp member; subst key; decide
  · intro key member; have same := List.mem_singleton.mp member; subst key; decide

theorem bounded : symbols.Bounded 2 := components.bounded_packProduct 0 [u32, u32] components_bounded

def invariants : InvariantFormula program [] := (invariantFormula program []).toOption.get (by rfl)
abbrev budget : VCBudget := { expansion := 0, depth := 16 }

def compiled := ending (requiresPolicy program (entryContext symbols bounded))
  (S := SperrInv.leer declaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none))
  budget none budget.depth (program.rumpf ()) symbols bounded (contractGoals program () symbols bounded invariants)

theorem compiled_present_zeuge : compiled.toOption.isSome = true := by with_unfolding_all rfl

def certificate := compiled.toOption.get compiled_present_zeuge

theorem compiled_result : compiled = .ok certificate := by
  have present := compiled_present_zeuge
  cases result : compiled with
  | error reason => rw [result] at present; cases present
  | ok value => simp only [certificate, result, Except.toOption, Option.get_some]

theorem normalized_zeuge : (Reduce.normalize 8 certificate.formula).val = .tru := by
  with_unfolding_all rfl

theorem original_valid_zeuge (values : Assignment (Key declaration Nat)) :
    (entryVC symbols .tru certificate.formula).denote values := by
  intro _ _ _
  apply ((Reduce.normalize 8 certificate.formula).property values).mp
  rw [normalized_zeuge]
  trivial

attribute [local irreducible] entryVC certificate

/-- All 2^64 product inputs satisfy this value-dependent field-return contract.
    No integer range or product of ranges is enumerated. -/
theorem production_parameter_acceptance_zeuge :
    (checkExecution program (SperrInv.leer declaration) (fun _ => none) budget none ()).toOption.isSome = true := by
  apply execution_success program (SperrInv.leer declaration) (fun _ => none) budget none ()
    (by rfl) invariants (by rfl)
    ((parameters (D := declaration) 0 0 [pair]).toOption.get (by with_unfolding_all rfl))
    (by with_unfolding_all rfl)
  · change 1 ≤ 16384
    decide
  · intro entry
    rcases entry with ⟨selected, member⟩
    change selected ∈ [symbols] at member
    have same := List.mem_singleton.mp member
    subst selected
    let requirement := (Invarianten.Frag.Symbolic.translate (program.requires ()) symbols).toOption.get (by rfl)
    exact environment_success_of_valid program (SperrInv.leer declaration) symbols bounded
      (requiresPolicy program _) (fun _ => none) budget none invariants (by with_unfolding_all rfl)
      requirement (by rfl) certificate compiled_result original_valid_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.ProductProductionWitness
