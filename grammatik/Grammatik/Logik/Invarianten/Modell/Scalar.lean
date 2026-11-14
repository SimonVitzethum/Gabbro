module

public import Grammatik.Logik.Invarianten.Frag.Observation
public import Grammatik.Logik.Invarianten.Modell.Closure

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell

open Frag Elim Elim.Korrekt

variable {D : Deklaration}

/-- Reconstruction accepts exactly the memory observations admitted by P13.
    String contents are irrelevant to the fragment; zero bytes realize the length.
    An out-of-range integer or length is refused, never clipped or wrapped. -/
def decodeScalar (τ : Ty) (value : Int) : Option (Wert D τ) :=
  match τ with
  | .int lo hi =>
      if valid : lo ≤ value ∧ value ≤ hi then
        some
          { n := value
            lo_le := valid.1
            le_hi := valid.2 }
      else none
  | .str capacity =>
      if valid : 0 ≤ value ∧ value ≤ (capacity : Int) then
        some ⟨List.replicate value.toNat ⟨0, by decide, by decide⟩, by
          simp only [List.length_replicate]
          omega⟩
      else none
  | _ => none

theorem decodeScalar_sound (τ : Ty) (value : Int) (decoded : Wert D τ)
    (success : decodeScalar τ value = some decoded) : scalarValue τ decoded = value := by
  cases τ with
  | int lo hi =>
      simp only [decodeScalar] at success
      split at success
      · rename_i valid
        cases success
        rfl
      · contradiction
  | str capacity =>
      simp only [decodeScalar] at success
      split at success
      · rename_i valid
        cases success
        simp only [scalarValue, List.length_replicate]
        exact Int.toNat_of_nonneg valid.1
      · contradiction
  | _ => simp [decodeScalar] at success

/-- The type bounds are ordinary Presburger formulas, inserted BEFORE deciding
    universal validity when a concrete typed model counterexample is requested. -/
def scalarBounds (τ : Ty) (term : LTerm α) : LProp α :=
  match τ with
  | .int lo hi => .and (.le (.konst lo) term) (.le term (.konst hi))
  | .str capacity => .and (.le (.konst 0) term) (.le term (.konst capacity))
  | _ => .fls

theorem decodeScalar_complete (τ : Ty) (value : Int)
    (valid : (scalarBounds τ (.konst value) : LProp Unit).denote (fun _ => 0)) :
    ∃ decoded : Wert D τ, decodeScalar τ value = some decoded := by
  cases τ with
  | int lo hi =>
      change lo ≤ value ∧ value ≤ hi at valid
      exact ⟨_, dif_pos valid⟩
  | str capacity =>
      change 0 ≤ value ∧ value ≤ (capacity : Int) at valid
      exact ⟨_, dif_pos valid⟩
  | _ => exact False.elim valid

def observationBounds (keys : List (Observation D)) : LProp (Observation D) :=
  keys.foldr (fun key rest => .and (scalarBounds (observationType key) (.var key)) rest) .tru

theorem observationBounds_sound (keys : List (Observation D))
    (values : Assignment (Observation D)) (valid : (observationBounds keys).denote values)
    (key : Observation D) (member : key ∈ keys) :
    ∃ decoded : Wert D (observationType key),
      decodeScalar (observationType key) (values key) = some decoded := by
  have atKey : (scalarBounds (observationType key) (.var key)).denote values := by
    revert valid key
    induction keys with
    | nil => intro _ key member; simp at member
    | cons head tail ih =>
        intro valid key member
        change (scalarBounds (observationType head) (.var head)).denote values ∧
          (observationBounds tail).denote values at valid
        rcases List.mem_cons.mp member with same | later
        · subst key
          exact valid.1
        · exact ih valid.2 key later
  apply decodeScalar_complete
  cases kind : observationType key <;>
    simpa only [scalarBounds, LProp.denote, LTerm.denote, kind] using atKey

/-- Every actual scalar value satisfies its declared bounds; no range hypothesis
    is added to the invariant soundness theorem. Support precedes the dependent
    value so its type test does not generalize that value or the equality proof. -/
theorem scalarBounds_value (τ : Ty)
    (supported : match τ with | .int _ _ | .str _ => True | _ => False)
    (value : Wert D τ) (term : LTerm α) [DecidableEq α] (values : Assignment α)
    (same : term.denote values = scalarValue τ value) :
    (scalarBounds τ term).denote values := by
  cases τ with
  | int lo hi =>
      change lo ≤ term.denote values ∧ term.denote values ≤ hi
      rw [same]
      exact ⟨value.lo_le, value.le_hi⟩
  | str capacity =>
      change 0 ≤ term.denote values ∧ term.denote values ≤ (capacity : Int)
      rw [same]
      change 0 ≤ (value.val.length : Int) ∧ (value.val.length : Int) ≤ (capacity : Int)
      constructor
      · omega
      · exact_mod_cast value.property
  | _ => exact False.elim supported

theorem observationBounds_assignment (keys : List (Observation D)) (world : World D)
    (supported : ∀ key ∈ keys, ScalarObservation key) :
    (observationBounds keys).denote (assignment world) := by
  induction keys with
  | nil => trivial
  | cons key keys ih =>
      change (scalarBounds (observationType key) (.var key)).denote (assignment world) ∧
        (observationBounds keys).denote (assignment world)
      constructor
      · have atKey := supported key (List.mem_cons.mpr (Or.inl rfl))
        cases key with
        | glob name => exact scalarBounds_value _ atKey (world.globs name) _ _ rfl
        | slot table field index =>
            exact scalarBounds_value _ atKey (world.slots table index field) _ _ rfl
      · exact ih (fun other member => supported other (List.mem_cons.mpr (Or.inr member)))

theorem scalarBounds_closed [DecidableEq α] (τ : Ty) (term : LTerm α) (bound : List α)
    (supported : termClosedB bound term = true) :
    closedUnderB bound (scalarBounds τ term) = true := by
  cases τ <;> simp [scalarBounds, closedUnderB, termClosedB, supported]

theorem observationBounds_closed (keys : List (Observation D)) (bound : List (Observation D))
    (covered : ∀ key ∈ keys, key ∈ bound) :
    closedUnderB bound (observationBounds keys) = true := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      change (closedUnderB bound (scalarBounds (observationType key) (.var key)) &&
        closedUnderB bound (observationBounds keys)) = true
      rw [Bool.and_eq_true]
      constructor
      · apply scalarBounds_closed
        simpa only [termClosedB, decide_eq_true_eq] using
          covered key (List.mem_cons.mpr (Or.inl rfl))
      · exact ih (fun other member => covered other (List.mem_cons.mpr (Or.inr member)))

end Gabbro.Grammatik.Invarianten.Modell
