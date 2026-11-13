module

public import Grammatik.Logik.Invarianten.Modell.Scalar
public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

variable {D : Deklaration}

/-- A finite snippet supplies exactly the observed fields, globals and lengths.
    Every other value and the event trace come from the supplied base world. -/
def snippetWorld (base : World D) (keys : List (Observation D))
    (values : Assignment (Observation D)) : World D :=
  { slots := fun table index field =>
      if Observation.slot table field index ∈ keys then
        (decodeScalar (D.typ table field) (values (.slot table field index))).getD
          (base.slots table index field)
      else base.slots table index field
    globs := fun name =>
      if Observation.glob name ∈ keys then
        (decodeScalar (D.gtyp name) (values (.glob name))).getD (base.globs name)
      else base.globs name
    spur := base.spur }

/-- A finite check, even though the returned world has total memory functions.
    Unsupported observations and unrepresentable values return `none`. -/
def reconstructWorld (base : World D) (keys : List (Observation D))
    (values : Assignment (Observation D)) : Option (World D) :=
  if keys.all (fun key => (decodeScalar (D := D) (observationType key) (values key)).isSome) then
    some (snippetWorld base keys values)
  else none

theorem snippetWorld_observation (base : World D) (keys : List (Observation D))
    (values : Assignment (Observation D)) (key : Observation D) (member : key ∈ keys)
    (decoded : Wert D (observationType key))
    (success : decodeScalar (observationType key) (values key) = some decoded) :
    assignment (snippetWorld base keys values) key = values key := by
  have sound := decodeScalar_sound (observationType key) (values key) decoded success
  cases key with
  | glob name =>
      simpa only [assignment, snippetWorld, member, ↓reduceIte, observationType,
        success, Option.getD_some] using sound
  | slot table field index =>
      simpa only [assignment, snippetWorld, member, ↓reduceIte, observationType,
        success, Option.getD_some] using sound

theorem reconstructWorld_sound (base : World D) (keys : List (Observation D))
    (values : Assignment (Observation D)) (world : World D)
    (success : reconstructWorld base keys values = some world) :
    ∀ key ∈ keys, assignment world key = values key := by
  unfold reconstructWorld at success
  split at success
  · rename_i valid
    cases success
    intro key member
    have available := List.all_eq_true.mp valid key member
    obtain ⟨decoded, decodedAt⟩ := Option.isSome_iff_exists.mp available
    exact snippetWorld_observation base keys values key member decoded decodedAt
  · contradiction

theorem reconstructWorld_complete (base : World D) (keys : List (Observation D))
    (values : Assignment (Observation D)) (valid : (observationBounds keys).denote values) :
    reconstructWorld base keys values = some (snippetWorld base keys values) := by
  have available : keys.all
      (fun key => (decodeScalar (D := D) (observationType key) (values key)).isSome) = true := by
    apply List.all_eq_true.mpr
    intro key member
    obtain ⟨decoded, success⟩ := observationBounds_sound keys values valid key member
    simp only [success, Option.isSome_some]
  simp only [reconstructWorld, available, ↓reduceIte]

/-- Typed validity is what a model invariant VC must decide. An unrestricted
    integer counterexample alone need not be a value of the declared memory type. -/
def stateValidity (keys : List (Observation D)) (formula : LProp (Observation D)) :
    LProp (Observation D) := .imp (observationBounds keys) formula

def stateCounterexample (base : World D) (keys : List (Observation D))
    (formula : LProp (Observation D)) : Option (World D) := do
  let values ← counterexample keys (stateValidity keys formula)
  reconstructWorld base keys values

theorem stateCounterexample_complete (base : World D) (keys : List (Observation D))
    (formula : LProp (Observation D))
    (rejected : decideB (universalClosure keys (stateValidity keys formula)) = false) :
    ∃ world : World D, stateCounterexample base keys formula = some world := by
  classical
  obtain ⟨values, selected⟩ := counterexample_complete keys (stateValidity keys formula) rejected
  have invalid := counterexample_sound keys (stateValidity keys formula) values selected
  have bounds : (observationBounds keys).denote values := by
    by_contra absent
    exact invalid (fun present => False.elim (absent present))
  refine ⟨snippetWorld base keys values, ?_⟩
  simp only [stateCounterexample, selected, Option.bind_some,
    reconstructWorld_complete base keys values bounds]

/-- The same finite observation support used for universal closure suffices to
    transfer the extracted false formula into the concrete typed world. -/
theorem stateCounterexample_sound (base : World D) (keys : List (Observation D))
    (formula : LProp (Observation D)) (supported : closedUnderB keys formula = true)
    (world : World D) (success : stateCounterexample base keys formula = some world) :
    ¬ formula.denote (assignment world) := by
  cases selected : counterexample keys (stateValidity keys formula) with
  | none => simp [stateCounterexample, selected] at success
  | some values =>
      have realized : reconstructWorld base keys values = some world := by
        simpa only [stateCounterexample, selected, Option.bind_some] using success
      have agrees := reconstructWorld_sound base keys values world realized
      have invalid := counterexample_sound keys (stateValidity keys formula) values selected
      intro holds
      have atValues := (closed_congr keys formula (assignment world) values supported agrees).mp holds
      exact invalid (fun _ => atValues)

/-- P13's translation theorem connects the snippet to the canonical invariant
    evaluator. This statement concerns a state, not reachability or a writer step;
    the latter are the obligations of the later VC packages. -/
theorem invariant_counterexample_sound (base : World D) (keys : List (Observation D))
    (carriers : List (D.Tab ⊕ D.Glob)) (expression : Expr D [] Λ .bool)
    (formula : LProp (Observation D))
    (translated : uebersetzeB carriers expression = .ok formula)
    (supported : closedUnderB keys formula = true) (world : World D)
    (success : stateCounterexample base keys formula = some world) :
    eval world expression world .nil = false := by
  have invalid := stateCounterexample_sound base keys formula supported world success
  cases evaluated : eval world expression world .nil with
  | false => rfl
  | true =>
      exact False.elim (invalid ((uebersetzeB_sound carriers expression formula translated world).mp evaluated))

end Gabbro.Grammatik.Invarianten.Modell
