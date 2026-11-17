module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Oracle

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.TraversalWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Pruefer.Symbolic SelectionWitness
open OracleWitness

/-- Each actual index mutates the caller's full-width local. The final
    continuation writes that actual value and proves a result/memory relation. -/
def step : Block declaration contract true [.index 3, u32] [] [] :=
  .cons (.assignVar (.there .here) (.widen (by decide) (by decide) (.var .here))) .nil

def body : Endblock declaration contract false [u32] [] :=
  .cons (.traverse () .tru step) (storedReturn (.var .here))

def program : Programm declaration := { OracleWitness.program 0 with rumpf := fun _ => body }

def invariants : InvariantFormula program [] := (invariantFormula program []).toOption.get (by rfl)

def compiled := ending (requiresPolicy program (entryContext symbols bounded_zeuge))
  (S := SperrInv.leer declaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none))
  budget none budget.depth body symbols bounded_zeuge (contractGoals program () symbols bounded_zeuge invariants)

theorem compiled_present_zeuge : compiled.toOption.isSome = true := by with_unfolding_all rfl

def certificate := compiled.toOption.get compiled_present_zeuge

theorem compiled_result : compiled = .ok certificate := by
  have present := compiled_present_zeuge
  cases result : compiled with
  | error reason => rw [result] at present; cases present
  | ok value => simp only [certificate, result, Except.toOption, Option.get_some]

theorem normalized_zeuge : (Reduce.normalize 8 certificate.formula).val = .tru := by
  with_unfolding_all rfl

theorem original_vc_zeuge (values : Assignment (Key declaration Nat)) :
    (entryVC symbols .tru certificate.formula).denote values := by
  intro _ _ _
  apply ((Reduce.normalize 8 certificate.formula).property values).mp
  rw [normalized_zeuge]
  trivial

attribute [local irreducible] entryVC certificate

/-- The count three exceeds the expansion budget two. Production acceptance
    uses the quantified traversal certificate, including the actual changed local. -/
theorem production_traversal_acceptance_zeuge :
    (checkExecution program (SperrInv.leer declaration) (fun _ => none) budget none ()).toOption.isSome = true := by
  apply execution_success program (SperrInv.leer declaration) (fun _ => none) budget none ()
    (by rfl) invariants (by rfl)
    ((parameters (D := declaration) 2 0 [u32]).toOption.get (by rfl)) (by rfl)
  · change 2 ≤ 16384
    decide
  · intro entry
    rcases entry with ⟨selected, member⟩
    change selected ∈ [symbols] at member
    have same := List.mem_singleton.mp member
    subst selected
    let requirement := (Invarianten.Frag.Symbolic.translate (program.requires ()) symbols).toOption.get (by rfl)
    exact environment_success_of_valid program (SperrInv.leer declaration) symbols bounded_zeuge
      (requiresPolicy program _) (fun _ => none) budget none invariants (by rfl)
      requirement (by rfl) certificate compiled_result original_vc_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.TraversalWitness
