module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Symbolic

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Invarianten.Modell

theorem prop_congr [DecidableEq α] (body : LProp α) (before after : Assignment α)
    (agree : ∀ key ∈ body.keys, before key = after key) : body.denote before ↔ body.denote after :=
  closed_congr body.keys body before after body.keys_supported agree

theorem closure_transfer [DecidableEq α] (names : List α) (body : LProp α)
    (before after : Assignment α) (valid : (universalClosure names body).denote before)
    (agree : ∀ key ∈ body.keys, key ∉ names → before key = after key) : body.denote after := by
  induction names generalizing before with
  | nil => exact (prop_congr body before after (fun key member => agree key member (by simp))).mp valid
  | cons name names ih =>
      apply ih (before.bind name (after name)) (valid (after name))
      intro key member absent
      by_cases same : key = name
      · subst key
        exact bind_same before name (after name)
      · simpa only [Assignment.bind, same, ↓reduceIte] using
          agree key member (by simp only [List.mem_cons, not_or]; exact ⟨same, absent⟩)

def memoryKeys (body : LProp (Key D Nat)) : List (Observation D) :=
  body.keys.filterMap (fun key => match key with | .inl memory => some memory | .inr _ => none)

def memoryFacts (body : LProp (Key D Nat)) : LProp (Key D Nat) :=
  renameProp Sum.inl (VC.typeFacts (memoryKeys body))

theorem memoryFacts_sound (body : LProp (Key D Nat)) (valuation : Assignment Nat) (world : World D) :
    (memoryFacts body).denote (values valuation world) := by
  apply (renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mpr
  exact VC.typeFacts_sound _ world

def havocFormula (written : Observation D → Bool) (body : LProp (Key D Nat)) : LProp (Key D Nat) :=
  let guarded : LProp (Key D Nat) := .imp (memoryFacts body) body
  let names := guarded.keys.filter (fun key => match key with | .inl memory => written memory | .inr _ => false)
  universalClosure names guarded

theorem havocFormula_sound (written : Observation D → Bool) (body : LProp (Key D Nat))
    (valuation : Assignment Nat) (before after : World D)
    (valid : (havocFormula written body).denote (values valuation before))
    (frame : ∀ key, written key = false → assignment before key = assignment after key) :
    body.denote (values valuation after) := by
  apply (closure_transfer _ (.imp (memoryFacts body) body) (values valuation before)
    (values valuation after) valid _)
  · exact memoryFacts_sound body valuation after
  · intro key member absent
    cases key with
    | inr localKey => rfl
    | inl memory =>
        have unchanged : written memory = false := by
          cases answer : written memory with
          | false => rfl
          | true => exact False.elim (absent (List.mem_filter.mpr ⟨member, answer⟩))
        exact frame memory unchanged

/-- Only the declared field list is traversed, never a field's value range. -/
def fieldConjunction (fields : List Ty)
    (formula : ∀ {kind}, FieldAt fields kind → LProp α) : LProp α :=
  match fields with
  | [] => .tru
  | _ :: rest => .and (formula .head) (fieldConjunction rest (fun field => formula (.tail field)))

theorem fieldConjunction_denote [DecidableEq α] (fields : List Ty)
    (formula : ∀ {kind}, FieldAt fields kind → LProp α) (values : Assignment α) :
    (fieldConjunction fields formula).denote values ↔ ∀ {kind} (field : FieldAt fields kind),
      (formula field).denote values := by
  induction fields with
  | nil =>
      constructor
      · intro _ kind field; cases field
      · intro _; trivial
  | cons kind fields ih =>
      change ((formula .head).denote values ∧ _) ↔ _
      rw [ih]
      constructor
      · intro ready selected field
        cases field with
        | head => exact ready.1
        | tail field => exact ready.2 field
      · intro ready
        exact ⟨ready .head, fun field => ready (.tail field)⟩

def valueBounds (symbol : SymValue D Nat τ) : LProp (Key D Nat) :=
  match symbol with
  | .known _ => .tru
  | .integer (lo := lo) (hi := hi) term => .and
      (.le (.konst lo) (renameTerm Sum.inr term)) (.le (renameTerm Sum.inr term) (.konst hi))
  | .product components => fieldConjunction _ (fun field => valueBounds (components field))

theorem valueBounds_sound (symbol : SymValue D Nat τ) (valuation : Assignment Nat)
    (world : World D) (actual : Wert D τ) (realized : symbol.Realizes valuation world actual) :
    (valueBounds symbol).denote (values valuation world) := by
  induction symbol with
  | known value => trivial
  | integer term =>
      change _ ≤ (renameTerm Sum.inr term).denote _ ∧ (renameTerm Sum.inr term).denote _ ≤ _
      rw [renameTerm_denote]
      change _ ≤ term.denote valuation ∧ term.denote valuation ≤ _
      rw [realized]
      exact ⟨actual.lo_le, actual.le_hi⟩
  | product components ih =>
      apply (fieldConjunction_denote _ _ _).mpr
      intro kind field
      exact ih field _ (realized field)

def environmentBounds : SymEnv D Nat Γ → LProp (Key D Nat)
  | .nil => .tru
  | .cons value rest => .and (valueBounds value) (environmentBounds rest)

theorem environmentBounds_sound (symbols : SymEnv D Nat Γ) (valuation : Assignment Nat)
    (world : World D) (actual : Env D Γ) (realized : symbols.Realizes valuation world actual) :
    (environmentBounds symbols).denote (values valuation world) := by
  induction symbols with
  | nil => trivial
  | cons value rest ih =>
      cases actual
      exact ⟨valueBounds_sound value valuation world _ realized.1, ih _ realized.2⟩

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
