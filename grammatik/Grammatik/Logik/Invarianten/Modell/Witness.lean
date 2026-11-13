module

public import Grammatik.Logik.Invarianten.Modell.World
public import Grammatik.Logik.Invarianten.Korrekt.Witness
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell.Witness

open Frag Elim Elim.Korrekt

/-- P16's false existential is false at every environment; even an empty outer
    prefix must return a concrete environment rather than report no witness. -/
theorem p16_false_assignment_computed_zeuge :
    (counterexample [] Elim.Korrekt.Witness.oddEquation).map (fun values => values 0) = some 0 := by
  rw [counterexample_nil_of_false _ (decideB_complete _ (by rfl)
    Elim.Korrekt.Witness.oddEquation_computed_zeuge (fun _ => 0))]
  rfl

theorem p16_false_assignment_complete_zeuge :
    ∃ values : Assignment Nat,
      counterexample [] Elim.Korrekt.Witness.oddEquation = some values :=
  counterexample_complete [] Elim.Korrekt.Witness.oddEquation
    Elim.Korrekt.Witness.oddEquation_computed_zeuge

/-- Expose the matrix of P16's `2*x=3` fixture. The infinity branch must undo a
    nontrivial coefficient normalization; its returned integer is actually -2. -/
def oddMatrix : LProp Nat := .eq (.scale 2 (.var 0)) (.konst 3)

theorem rescaled_assignment_computed_zeuge :
    (counterexample [0] oddMatrix).map (fun values => values 0) = some (-2) := by
  rw [counterexample_single_of_recovered 0 oddMatrix (-2) (by decide)]
  rfl

theorem rescaled_assignment_falsifies_zeuge :
    ¬ oddMatrix.denote (fun _ => -2) := by decide

/-- The boundary branch, rather than infinity, supplies the smallest even integer
    above 3. This reuses the positive fixture of P16 with reversed polarity. -/
def lowerWitness : LProp Nat :=
  .not (.and (.lt (.konst 3) (.var 0)) (.dvd 2 (.var 0)))

theorem boundary_assignment_computed_zeuge :
    (counterexample [0] lowerWitness).map (fun values => values 0) = some 4 := by
  rw [counterexample_single_of_recovered 0 lowerWitness 4 (by decide)]
  rfl

theorem boundary_assignment_falsifies_zeuge :
    ¬ lowerWitness.denote (fun _ => 4) := by decide

/-- Infinity means a sufficiently negative member of the residue class, rather
    than the small positive representative used in the projected formula. -/
def farLeft : LProp Nat :=
  .not (.and (.lt (.var 0) (.konst (-5))) (.dvd 2 (.var 0)))

theorem negative_infinity_computed_zeuge :
    (counterexample [0] farLeft).map (fun values => values 0) = some (-16) := by
  rw [counterexample_single_of_recovered 0 farLeft (-16) (by decide)]
  rfl

theorem negative_infinity_falsifies_zeuge :
    ¬ farLeft.denote (fun _ => -16) := by decide

/-- Reconstruct x before y, then evaluate y's boundary in the recovered x=4
    environment. A search that evaluated all thresholds at zero would fail here. -/
def dependentVariables : LProp Nat :=
  .not (.and (.eq (.var 0) (.konst 4))
    (.eq (.var 1) (.add (.var 0) (.konst 1))))

theorem backwards_trace_computed_zeuge :
    (counterexample [0, 1] dependentVariables).map (fun values => (values 0, values 1)) =
      some (4, 5) := by
  have rejected : decideB (universalClosure [0, 1] dependentVariables) = false := by
    apply (decideB_false_iff _ (by decide) (fun _ => 0)).mpr
    intro valid
    have impossible := valid 4 5
    exact impossible (by constructor <;> decide)
  obtain ⟨values, selected⟩ := counterexample_complete [0, 1] dependentVariables rejected
  have valid : values 0 = 4 ∧ values 1 = values 0 + 1 := by
    simpa only [dependentVariables, LProp.denote, LTerm.denote, not_not] using
      counterexample_sound [0, 1] dependentVariables values selected
  have atOne : values 1 = 5 := by omega
  simp only [selected, Option.map_some, valid.1, atOne]

theorem counterexample_sound_zeuge (values : Assignment Nat)
    (success : counterexample [0] oddMatrix = some values) : ¬ oddMatrix.denote values :=
  counterexample_sound [0] oddMatrix values success

theorem counterexample_of_exists_zeuge :
    ∃ values : Assignment Nat, counterexample [0] lowerWitness = some values := by
  apply counterexample_of_exists [0] lowerWitness
  apply (decideB_true_iff _ (by decide) (fun _ => 0)).mpr
  refine ⟨4, ?_⟩
  change ¬ ¬ ((3 : Int) < 4 ∧ (2 : Int) ∣ 4)
  exact fun absent => absent ⟨by decide, ⟨2, rfl⟩⟩

theorem valid_formula_has_no_counterexample_zeuge :
    (counterexample [0] (.le (.var 0) (.var 0))).isSome = false := by
  cases selected : counterexample [0] (.le (.var 0) (.var 0)) with
  | none => rfl
  | some values =>
      exact False.elim (counterexample_sound [0] (.le (.var 0) (.var 0)) values selected
        (Int.le_refl _))

def observationValues : Assignment (Observation Frag.Witness.declaration)
  | .glob name => if name = true then 8 else 9
  | .slot _ _ _ => 7

def snippetKeys : List (Observation Frag.Witness.declaration) :=
  [.glob false, .glob true, .slot () () 0]

theorem fields_and_globals_computed_zeuge :
    (reconstructWorld Frag.Witness.initial snippetKeys observationValues).map
      (fun world => (assignment world (.glob false), assignment world (.slot () () 0))) =
        some (9, 7) := by decide

theorem unobserved_field_preserved_zeuge :
    (snippetWorld Frag.Witness.initial snippetKeys observationValues).slots () 1 () =
      Frag.Witness.initial.slots () 1 () := by rfl

theorem snippet_false_invariant_zeuge :
    eval (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      Frag.Witness.boundedLength
      (snippetWorld Frag.Witness.initial snippetKeys observationValues) .nil = false := by
  show wahr? (eval (snippetWorld Frag.Witness.initial snippetKeys observationValues)
    Frag.Witness.boundedLength
    (snippetWorld Frag.Witness.initial snippetKeys observationValues) .nil) = false
  rfl

/-- A one-global end-to-end counterexample; all type bounds are generated by the
    world layer. The returned state has the declared integer value 4. -/
def shortInvariant : Expr Frag.Witness.declaration [] [] .bool :=
  .le (.glob false (Frag.Witness.globalAccess false)) (.lit 3)

def shortFormula : LProp (Observation Frag.Witness.declaration) :=
  .le (.var (.glob false)) (.konst 3)

theorem state_counterexample_computed_zeuge :
    (stateCounterexample Frag.Witness.initial [.glob false] shortFormula).map
      (fun world => assignment world (.glob false)) = some 4 := by
  let values : Assignment (Observation Frag.Witness.declaration) :=
    (fun _ => 0).bind (.glob false) 4
  have selected : counterexample [.glob false] (stateValidity [.glob false] shortFormula) =
      some values :=
    counterexample_single_of_recovered (.glob false) _ 4 (by decide)
  have bounds : (observationBounds [.glob false]).denote values := by decide
  have realized := reconstructWorld_complete Frag.Witness.initial [.glob false] values bounds
  change ((counterexample [.glob false] (stateValidity [.glob false] shortFormula)).bind
    (reconstructWorld Frag.Witness.initial [.glob false])).map _ = _
  rw [selected, Option.bind_some, realized, Option.map_some]
  have agrees := reconstructWorld_sound Frag.Witness.initial [.glob false] values
    (snippetWorld Frag.Witness.initial [.glob false] values) realized (.glob false) (by simp)
  rw [agrees]
  rfl

theorem state_counterexample_complete_zeuge :
    ∃ world : World Frag.Witness.declaration,
      stateCounterexample Frag.Witness.initial [.glob false] shortFormula = some world := by
  apply stateCounterexample_complete
  apply (decideB_false_iff _ (by rfl) (fun _ => 0)).mpr
  intro valid
  have atFour := valid 4
  change (0 ≤ (4 : Int) ∧ (4 : Int) ≤ 10) ∧ True → (4 : Int) ≤ 3 at atFour
  have impossible := atFour ⟨⟨by decide, by decide⟩, trivial⟩
  omega

theorem invariant_counterexample_sound_zeuge (world : World Frag.Witness.declaration)
    (success : stateCounterexample Frag.Witness.initial [.glob false] shortFormula = some world) :
    eval world shortInvariant world .nil = false :=
  invariant_counterexample_sound Frag.Witness.initial [.glob false]
    (Frag.Witness.declaration.traeger ()) shortInvariant shortFormula rfl (by decide) world success

/-- Length reconstruction is concrete (three zero bytes), with no claim about
    contents. Bad lengths and bad bounded integers cannot produce typed states. -/
theorem string_length_computed_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) 3).map
      (fun value => value.val.length) = some 3 := by decide

def stringInitial : World Frag.Witness.stringDeclaration where
  slots := Frag.Witness.initial.slots
  globs := fun name =>
    match name with
    | false => ⟨[], by decide⟩
    | true => ⟨2, by decide, by decide⟩
  spur := []

theorem string_world_false_computed_zeuge :
    (reconstructWorld stringInitial [.glob false] (fun _ => 3)).map
      (fun world => eval world Frag.Witness.stringBound world .nil) = some false := by
  change (reconstructWorld stringInitial [.glob false] (fun _ => 3)).map
    (fun world => wahr? (eval world Frag.Witness.stringBound world .nil)) = some false
  rfl

theorem negative_length_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) (-1)).isSome = false := by decide

theorem overlong_length_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) 6).isSome = false := by decide

theorem out_of_range_integer_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.int 0 10) 11).isSome = false := by decide

end Gabbro.Grammatik.Invarianten.Modell.Witness
