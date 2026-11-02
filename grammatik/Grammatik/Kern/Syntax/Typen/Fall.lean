module

public import Grammatik.Kern.Syntax.Typen.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- A case value is its payload value: the propositional bridge between the
    structural case type `Fall` and the payload type `Nutzlast`. -/
theorem Fall_eq_Nutzlast (F : Type) (passt : F → Nat → Bool) :
    ∀ (cs : List (Option Ty)) (i : Fin cs.length),
      Fall F passt cs i = Nutzlast F passt (cs.get i)
  | [], i => (Nat.not_lt_zero _ i.isLt).elim
  | none :: _, ⟨0, _⟩ => rfl
  | some _ :: _, ⟨0, _⟩ => rfl
  | _ :: cs, ⟨i + 1, h⟩ => Fall_eq_Nutzlast F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- A payload value as a case value. -/
def Fall.ofNutzlast (F : Type) (passt : F → Nat → Bool) :
    (cs : List (Option Ty)) → (i : Fin cs.length) →
    Nutzlast F passt (cs.get i) → Fall F passt cs i
  | [], i, _ => (Nat.not_lt_zero _ i.isLt).elim
  | none :: _, ⟨0, _⟩, v => v
  | some _ :: _, ⟨0, _⟩, v => v
  | _ :: cs, ⟨i + 1, h⟩, v => Fall.ofNutzlast F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v

/-- A case value as its payload value. -/
def Fall.toNutzlast (F : Type) (passt : F → Nat → Bool) :
    (cs : List (Option Ty)) → (i : Fin cs.length) →
    Fall F passt cs i → Nutzlast F passt (cs.get i)
  | [], i, _ => (Nat.not_lt_zero _ i.isLt).elim
  | none :: _, ⟨0, _⟩, v => v
  | some _ :: _, ⟨0, _⟩, v => v
  | _ :: cs, ⟨i + 1, h⟩, v => Fall.toNutzlast F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v

/-- Casting forth and back is the identity. -/
@[simp] theorem Fall.to_of (F : Type) (passt : F → Nat → Bool) :
    ∀ (cs : List (Option Ty)) (i : Fin cs.length) (v : Nutzlast F passt (cs.get i)),
      Fall.toNutzlast F passt cs i (Fall.ofNutzlast F passt cs i v) = v
  | [], i, _ => (Nat.not_lt_zero _ i.isLt).elim
  | none :: _, ⟨0, _⟩, _ => rfl
  | some _ :: _, ⟨0, _⟩, _ => rfl
  | _ :: cs, ⟨i + 1, h⟩, v => Fall.to_of F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v

/-- Casting back and forth is the identity. -/
@[simp] theorem Fall.of_to (F : Type) (passt : F → Nat → Bool) :
    ∀ (cs : List (Option Ty)) (i : Fin cs.length) (v : Fall F passt cs i),
      Fall.ofNutzlast F passt cs i (Fall.toNutzlast F passt cs i v) = v
  | [], i, _ => (Nat.not_lt_zero _ i.isLt).elim
  | none :: _, ⟨0, _⟩, _ => rfl
  | some _ :: _, ⟨0, _⟩, _ => rfl
  | _ :: cs, ⟨i + 1, h⟩, v => Fall.of_to F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v

/-- The cast of a bare case is the unit value. -/
@[simp] theorem Fall.ofNutzlast_zero_none (F : Type) (passt : F → Nat → Bool)
    (cs : List (Option Ty)) (h : 0 < (none :: cs).length) (v : Nutzlast F passt ((none :: cs).get ⟨0, h⟩)) :
    Fall.ofNutzlast F passt (none :: cs) ⟨0, h⟩ v = v := rfl

/-- The cast of a payload case is the payload value. -/
@[simp] theorem Fall.ofNutzlast_zero_some (F : Type) (passt : F → Nat → Bool)
    (τ : Ty) (cs : List (Option Ty)) (h : 0 < (some τ :: cs).length)
    (v : Nutzlast F passt ((some τ :: cs).get ⟨0, h⟩)) :
    Fall.ofNutzlast F passt (some τ :: cs) ⟨0, h⟩ v = v := rfl

/-- The cast pushes through a later case. -/
theorem Fall.ofNutzlast_succ (F : Type) (passt : F → Nat → Bool)
    (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length)
    (v : Nutzlast F passt ((c :: cs).get ⟨i + 1, h⟩)) :
    Fall.ofNutzlast F passt (c :: cs) ⟨i + 1, h⟩ v =
      Fall.ofNutzlast F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v := rfl

/-- The back cast of a bare case is the unit value. -/
@[simp] theorem Fall.toNutzlast_zero_none (F : Type) (passt : F → Nat → Bool)
    (cs : List (Option Ty)) (h : 0 < (none :: cs).length) (v : Fall F passt (none :: cs) ⟨0, h⟩) :
    Fall.toNutzlast F passt (none :: cs) ⟨0, h⟩ v = v := rfl

/-- The back cast of a payload case is the payload value. -/
@[simp] theorem Fall.toNutzlast_zero_some (F : Type) (passt : F → Nat → Bool)
    (τ : Ty) (cs : List (Option Ty)) (h : 0 < (some τ :: cs).length)
    (v : Fall F passt (some τ :: cs) ⟨0, h⟩) :
    Fall.toNutzlast F passt (some τ :: cs) ⟨0, h⟩ v = v := rfl

/-- The back cast pushes through a later case. -/
theorem Fall.toNutzlast_succ (F : Type) (passt : F → Nat → Bool)
    (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length)
    (v : Fall F passt (c :: cs) ⟨i + 1, h⟩) :
    Fall.toNutzlast F passt (c :: cs) ⟨i + 1, h⟩ v =
      Fall.toNutzlast F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ v := rfl

/-- A later case value is the case value of the tail. -/
theorem Fall.cons_succ (F : Type) (passt : F → Nat → Bool)
    (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length) :
    Fall F passt (c :: cs) ⟨i + 1, h⟩ = Fall F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

end Gabbro.Grammatik
