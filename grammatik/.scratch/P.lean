import Grammatik.Kern.Syntax.Typen.Teil1
open Gabbro.Grammatik
#print axioms Fall
example (F : Type) (p : F → Nat → Bool) (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length) :
  Fall F p (c :: cs) ⟨i+1, h⟩ = Fall F p cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl
example (F : Type) (p : F → Nat → Bool) (c : Option Ty) (cs : List (Option Ty)) (i : Nat) (h : i + 1 < (c :: cs).length) :
  Fall F p (c :: cs) ⟨i+1, h⟩ = Fall F p cs ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by simp only [Fall]
