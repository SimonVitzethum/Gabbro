module

public import Grammatik.Logik.Invarianten.Modell.World
public import Grammatik.Logik.Invarianten.Korrekt.Witness
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell.Witness

open Frag Elim Elim.Korrekt

/-! Computed values use the generic soundness theorems or finite one-variable
    recovery calculations. Exact candidate calculations use natural or abstract
    keys, without reducing dependent model declarations or whole worlds.
    The elaborator never runs quantified Cooper elimination here. -/

/-- P16's false existential is false at every environment; even an empty outer
    prefix must return a concrete environment rather than report no witness. -/
theorem p16_false_assignment_computed_zeuge :
    (counterexample [] Elim.Korrekt.Witness.oddEquation).map (fun values => values 0) = some 0 := by
  have selected := counterexample_nil_of_false Elim.Korrekt.Witness.oddEquation
    (Elim.Korrekt.Witness.decideB_complete_zeuge (fun _ => 0))
  exact (congrArg (Option.map fun values : Assignment Nat => values 0) selected).trans rfl

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
  have selected := counterexample_single_of_recovered 0 oddMatrix (-2) (by decide)
  exact (congrArg (Option.map fun values : Assignment Nat => values 0) selected).trans rfl

theorem rescaled_assignment_falsifies_zeuge :
    ¬ oddMatrix.denote (fun _ => -2) := by
  change ¬ (2 * (-2 : Int) = 3)
  omega

/-- The boundary branch, rather than infinity, supplies the smallest even integer
    above 3. This reuses the positive fixture of P16 with reversed polarity. -/
def lowerWitness : LProp Nat :=
  .not (.and (.lt (.konst 3) (.var 0)) (.dvd 2 (.var 0)))

theorem boundary_assignment_computed_zeuge :
    (counterexample [0] lowerWitness).map (fun values => values 0) = some 4 := by
  have selected := counterexample_single_of_recovered 0 lowerWitness 4 (by decide)
  exact (congrArg (Option.map fun values : Assignment Nat => values 0) selected).trans rfl

theorem boundary_assignment_falsifies_zeuge :
    ¬ lowerWitness.denote (fun _ => 4) := by
  change ¬ ¬ ((3 : Int) < 4 ∧ (2 : Int) ∣ 4)
  exact fun absent => absent ⟨by omega, ⟨2, by omega⟩⟩

/-- Infinity means a sufficiently negative member of the residue class, rather
    than the small positive representative used in the projected formula. -/
def farLeft : LProp Nat :=
  .not (.and (.lt (.var 0) (.konst (-5))) (.dvd 2 (.var 0)))

theorem negative_infinity_computed_zeuge :
    (counterexample [0] farLeft).map (fun values => values 0) = some (-16) := by
  have selected := counterexample_single_of_recovered 0 farLeft (-16) (by decide)
  exact (congrArg (Option.map fun values : Assignment Nat => values 0) selected).trans rfl

theorem negative_infinity_falsifies_zeuge :
    ¬ farLeft.denote (fun _ => -16) := by
  change ¬ ¬ ((-16 : Int) < -5 ∧ (2 : Int) ∣ -16)
  exact fun absent => absent ⟨by omega, ⟨-8, by omega⟩⟩

/-- Reconstruct x before y, then evaluate y's boundary in the recovered x=4
    environment. A search that evaluated all thresholds at zero would fail here. -/
def dependentVariables : LProp Nat :=
  .not (.and (.eq (.var 0) (.konst 4))
    (.eq (.var 1) (.add (.var 0) (.konst 1))))

theorem backwards_trace_computed_zeuge :
    (counterexample [0, 1] dependentVariables).map (fun values => (values 0, values 1)) =
      some (4, 5) := by
  have rejected : decideB (universalClosure [0, 1] dependentVariables) = false := by
    apply (decideB_false_iff (universalClosure [0, 1] dependentVariables) (by decide)
      (fun _ => 0)).mpr
    intro valid
    have impossible : ¬ ((4 : Int) = 4 ∧ (5 : Int) = 4 + 1) := valid 4 5
    exact impossible ⟨rfl, by omega⟩
  obtain ⟨values, selected⟩ := counterexample_complete [0, 1] dependentVariables rejected
  have invalid := counterexample_sound [0, 1] dependentVariables values selected
  have valid : values 0 = 4 ∧ values 1 = values 0 + 1 := by
    by_contra absent
    exact invalid absent
  have atZero : values 0 = 4 := valid.1
  have atOne : values 1 = 5 := by omega
  simp only [selected, Option.map_some, atZero, atOne]

theorem counterexample_sound_zeuge (values : Assignment Nat)
    (success : counterexample [0] oddMatrix = some values) : ¬ oddMatrix.denote values :=
  counterexample_sound [0] oddMatrix values success

theorem counterexample_of_exists_zeuge :
    ∃ values : Assignment Nat, counterexample [0] lowerWitness = some values := by
  apply counterexample_of_exists [0] lowerWitness
  apply (decideB_true_iff (existentialClosure [0] (.not lowerWitness)) (by decide)
    (fun _ => 0)).mpr
  refine ⟨4, ?_⟩
  change ¬ ¬ ((3 : Int) < 4 ∧ (2 : Int) ∣ 4)
  exact fun absent => absent ⟨by omega, ⟨2, by omega⟩⟩

theorem valid_formula_has_no_counterexample_zeuge :
    (counterexample [0] (.le (.var 0) (.var 0))).isSome = false := by
  cases selected : counterexample [0] (.le (.var 0) (.var 0)) with
  | none => rfl
  | some values =>
      exact False.elim (counterexample_sound [0] (.le (.var 0) (.var 0)) values selected
        (Int.le_refl _))

def observationValues : Assignment (Observation Frag.Witness.declaration)
  | .glob name => match (name : Bool) with | true => 8 | false => 9
  | .slot _ _ _ => 7

def snippetKeys : List (Observation Frag.Witness.declaration) :=
  [.glob false, .glob true, .slot () () 0]

private theorem glob_false_mem : (.glob false : Observation Frag.Witness.declaration) ∈ snippetKeys :=
  List.mem_cons_self

private theorem glob_true_mem : (.glob true : Observation Frag.Witness.declaration) ∈ snippetKeys :=
  List.mem_cons_of_mem _ List.mem_cons_self

private theorem slot_zero_mem :
    (.slot () () 0 : Observation Frag.Witness.declaration) ∈ snippetKeys :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem snippet_bounds : (observationBounds snippetKeys).denote observationValues := by
  change ((0 : Int) ≤ 9 ∧ (9 : Int) ≤ 10) ∧
    ((0 : Int) ≤ 8 ∧ (8 : Int) ≤ 10) ∧ ((0 : Int) ≤ 7 ∧ (7 : Int) ≤ 10) ∧ True
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

private theorem snippet_realized :
    reconstructWorld Frag.Witness.initial snippetKeys observationValues =
      some (snippetWorld Frag.Witness.initial snippetKeys observationValues) :=
  reconstructWorld_complete Frag.Witness.initial snippetKeys observationValues snippet_bounds

private theorem snippet_agrees :
    ∀ key ∈ snippetKeys,
      assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues) key =
        observationValues key :=
  reconstructWorld_sound Frag.Witness.initial snippetKeys observationValues _ snippet_realized

theorem fields_and_globals_computed_zeuge :
    (reconstructWorld Frag.Witness.initial snippetKeys observationValues).map
      (fun world => (assignment world (.glob false), assignment world (.slot () () 0))) =
        some (9, 7) := by
  have atGlob : assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.glob false) = 9 := snippet_agrees _ glob_false_mem
  have atSlot : assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.slot () () 0) = 7 := snippet_agrees _ slot_zero_mem
  simp only [snippet_realized, Option.map_some, atGlob, atSlot]

theorem unobserved_field_preserved_zeuge :
    (snippetWorld Frag.Witness.initial snippetKeys observationValues).slots () 1 () =
      Frag.Witness.initial.slots () 1 () := by
  have absent : (.slot () () 1 : Observation Frag.Witness.declaration) ∉ snippetKeys := by
    decide
  exact snippetWorld_slot_of_not_mem Frag.Witness.initial snippetKeys observationValues
    () 1 () absent

theorem snippet_false_invariant_zeuge :
    eval (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      Frag.Witness.boundedLength
      (snippetWorld Frag.Witness.initial snippetKeys observationValues) .nil = false := by
  change wahr? (eval (snippetWorld Frag.Witness.initial snippetKeys observationValues)
    Frag.Witness.boundedLength
    (snippetWorld Frag.Witness.initial snippetKeys observationValues) .nil) = false
  apply Bool.eq_false_iff.mpr
  intro evaluated
  have holds := (Frag.Witness.boundedLength_sound_zeuge
    (snippetWorld Frag.Witness.initial snippetKeys observationValues)).mp evaluated
  have atFalse : assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.glob false) = 9 := snippet_agrees _ glob_false_mem
  have atTrue : assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.glob true) = 8 := snippet_agrees _ glob_true_mem
  change assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.glob false) ≤
      assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues) (.glob true) ∧
    0 ≤ assignment (snippetWorld Frag.Witness.initial snippetKeys observationValues)
      (.glob false) at holds
  rw [atFalse, atTrue] at holds
  omega

/-- A one-global end-to-end counterexample; all type bounds are generated by the
    world layer. Completeness supplies a typed state that refutes this invariant. -/
def shortInvariant : Expr Frag.Witness.declaration [] [] .bool :=
  .le (.glob false (Frag.Witness.globalAccess false)) (.lit 3)

def shortFormula : LProp (Observation Frag.Witness.declaration) :=
  .le (.var (.glob false)) (.konst 3)

theorem short_translated_zeuge :
    uebersetzeB (Frag.Witness.declaration.traeger ()) shortInvariant = .ok shortFormula := by
  rfl

theorem state_counterexample_complete_zeuge :
    ∃ world : World Frag.Witness.declaration,
      stateCounterexample Frag.Witness.initial [.glob false] shortFormula = some world := by
  apply stateCounterexample_complete
  apply (decideB_false_iff (universalClosure [.glob false]
      (stateValidity (D := Frag.Witness.declaration) [.glob false] shortFormula))
    (by decide) (fun _ => 0)).mpr
  intro valid
  have atFour : ((0 : Int) ≤ 4 ∧ (4 : Int) ≤ 10) ∧ True → (4 : Int) ≤ 3 := valid 4
  have impossible := atFour ⟨⟨by omega, by omega⟩, trivial⟩
  omega

theorem invariant_counterexample_sound_zeuge (world : World Frag.Witness.declaration)
    (success : stateCounterexample Frag.Witness.initial [.glob false] shortFormula = some world) :
    eval world shortInvariant world .nil = false :=
  invariant_counterexample_sound Frag.Witness.initial [.glob false]
    (Frag.Witness.declaration.traeger ()) shortInvariant shortFormula short_translated_zeuge
    (by decide) world success

/-- Existence and semantic refutation replace the former exact choice of 4:
    validity alone does not determine which value in 4..10 is recovered. -/
theorem state_counterexample_refutes_zeuge :
    ∃ world : World Frag.Witness.declaration,
      stateCounterexample Frag.Witness.initial [.glob false] shortFormula = some world ∧
        eval world shortInvariant world .nil = false := by
  obtain ⟨world, success⟩ := state_counterexample_complete_zeuge
  exact ⟨world, success, invariant_counterexample_sound_zeuge world success⟩

/-- Length reconstruction is concrete (three zero bytes), with no claim about
    contents. Bad lengths and bad bounded integers cannot produce typed states. -/
theorem string_length_computed_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) 3).map
      (fun value => value.val.length) = some 3 := by
  obtain ⟨decoded, success⟩ := decodeScalar_complete (D := Frag.Witness.declaration) (.str 5) 3
    (by change (0 : Int) ≤ 3 ∧ (3 : Int) ≤ 5; constructor <;> omega)
  have length := decodeScalar_sound (.str 5) 3 decoded success
  change (decoded.val.length : Int) = 3 at length
  have natural : decoded.val.length = 3 := by omega
  rw [success]
  exact congrArg some natural

def stringInitial : World Frag.Witness.stringDeclaration where
  slots := Frag.Witness.initial.slots
  globs := fun (name : Bool) =>
    match name with
    | false => ⟨[], by decide⟩
    | true => ⟨2, by decide, by decide⟩
  spur := []

theorem string_world_false_computed_zeuge :
    (reconstructWorld stringInitial [.glob false] (fun _ => 3)).map
      (fun world => eval world Frag.Witness.stringBound world .nil) = some false := by
  have bounds : (observationBounds (D := Frag.Witness.stringDeclaration) [.glob false]).denote
      (fun _ : Observation Frag.Witness.stringDeclaration => 3) := by
    change ((0 : Int) ≤ 3 ∧ (3 : Int) ≤ 10) ∧ True
    exact ⟨⟨by omega, by omega⟩, trivial⟩
  have realized := reconstructWorld_complete stringInitial [.glob false] (fun _ => 3) bounds
  have agrees := reconstructWorld_sound stringInitial [.glob false] (fun _ => 3) _ realized
  have refuted : eval (snippetWorld stringInitial [.glob false] (fun _ => 3))
      Frag.Witness.stringBound (snippetWorld stringInitial [.glob false] (fun _ => 3)) .nil =
        false := by
    change wahr? (eval (snippetWorld stringInitial [.glob false] (fun _ => 3))
      Frag.Witness.stringBound (snippetWorld stringInitial [.glob false] (fun _ => 3)) .nil) =
        false
    apply Bool.eq_false_iff.mpr
    intro evaluated
    have holds := (uebersetzeB_sound (Frag.Witness.stringDeclaration.traeger ())
      Frag.Witness.stringBound (.le (.var (.glob false)) (.var (.glob true)))
      Frag.Witness.stringBound_translated_zeuge
      (snippetWorld stringInitial [.glob false] (fun _ => 3))).mp evaluated
    have atFalse : assignment (snippetWorld stringInitial [.glob false] (fun _ => 3))
        (.glob false) = 3 := agrees (.glob false) List.mem_cons_self
    have atTrue : assignment (snippetWorld stringInitial [.glob false] (fun _ => 3))
        (.glob true) = 2 := rfl
    change assignment (snippetWorld stringInitial [.glob false] (fun _ => 3)) (.glob false) ≤
      assignment (snippetWorld stringInitial [.glob false] (fun _ => 3)) (.glob true) at holds
    rw [atFalse, atTrue] at holds
    omega
  rw [realized]
  exact congrArg some refuted

theorem negative_length_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) (-1)).isSome = false := by decide

theorem overlong_length_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.str 5) 6).isSome = false := by decide

theorem out_of_range_integer_refused_zeuge :
    (decodeScalar (D := Frag.Witness.declaration) (.int 0 10) 11).isSome = false := by decide

end Gabbro.Grammatik.Invarianten.Modell.Witness
