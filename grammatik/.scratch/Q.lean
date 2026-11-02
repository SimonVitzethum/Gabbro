import Grammatik.Kern.Syntax.Typen.Teil1
namespace X
open Gabbro.Grammatik (Ty Zahl Gleit)
mutual
def Val (F : Type) (passt : F → Nat → Bool) : Ty → Type
  | .int lo hi => Zahl lo hi
  | .bool => Bool
  | .opt n => Option (Zahl 0 (n - 1))
  | .sum cs => Σ i : Fin cs.length, Fall F passt cs i
  | .why n => Fin n
  | .never => Empty
  | .fl lo hi => Gleit lo hi
  | .fnptr n => { f : F // passt f n = true }
  | .ptr _ => Unit
  | .ref _ => Nat
  | .arr τ n => Fin n → Val F passt τ
  | .str n => { bs : List (Zahl 0 255) // bs.length ≤ n }
def Fall (F : Type) (passt : F → Nat → Bool) : (cs : List (Option Ty)) → Fin cs.length → Type
  | c :: _, ⟨0, _⟩ => Kopf F passt c
  | _ :: cs, ⟨i + 1, h⟩ => Fall F passt cs ⟨i, Nat.lt_of_succ_lt_succ h⟩
def Kopf (F : Type) (passt : F → Nat → Bool) : Option Ty → Type
  | none => Unit
  | some τ => Val F passt τ
end
#print axioms Fall
example (F : Type) (p : F → Nat → Bool) (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length) :
  Fall F p (c :: cs) ⟨i+1, h⟩ = Fall F p cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl
example (F : Type) (p : F → Nat → Bool) (τ : Ty) (cs : List (Option Ty)) (h : 0 < (some τ :: cs).length) :
  Fall F p (some τ :: cs) ⟨0, h⟩ = Val F p τ := rfl
example (F : Type) (p : F → Nat → Bool) (cs) : Val F p (.sum cs) = (Σ i : Fin cs.length, Fall F p cs i) := rfl
end X
