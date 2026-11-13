module

public import Grammatik.Logik.Invarianten.Frag.Observation
public import Grammatik.Logik.Invarianten.Modell.Trace

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

/-- The type of the observed location; a slot index changes no field type. -/
def observationType : Observation D → Ty
  | .glob name => D.gtyp name
  | .slot table field _ => D.typ table field

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

end Gabbro.Grammatik.Invarianten.Modell
