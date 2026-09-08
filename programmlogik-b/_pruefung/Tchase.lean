import Gabbro.Body
open Gabbro.Body
namespace Gabbro.Body

theorem chase_store_ne (σ : World) (c via : String) (to : Int) (p : Place) (v : Value)
    (h : ∀ m, p ≠ .slot c m via) (k : Int) (n : Nat) :
    chase (store σ p v) c via to k n = chase σ c via to k n := by
  induction n generalizing k with
  | zero => rw [chase_zero, chase_zero]
  | succ n ih =>
    rw [chase_succ, chase_succ]
    by_cases hk : k = to
    · simp [hk]
    · simp only [hk, if_false]
      rw [store_elsewhere _ _ _ _ (fun e => h k e.symm)]
      cases σ (.slot c k via) <;> simp [ih]

@[simp] theorem chase_store_field (σ : World) (c c' via f' : String) (to k' : Int) (v : Value)
    (h : f' ≠ via) (to' k : Int) (n : Nat) :
    chase (store σ (.slot c' k' f') v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun m e => by cases e; exact h rfl) k n

@[simp] theorem chase_store_carrier (σ : World) (c c' via f' : String) (k' : Int) (v : Value)
    (h : c' ≠ c) (to' k : Int) (n : Nat) :
    chase (store σ (.slot c' k' f') v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun m e => by cases e; exact h rfl) k n

@[simp] theorem chase_store_global (σ : World) (c via g : String) (v : Value) (to' k : Int) (n : Nat) :
    chase (store σ (.global g) v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun m e => by cases e) k n

@[simp] theorem chase_store_fieldPlace (σ : World) (c via r f : String) (v : Value) (to' k : Int) (n : Nat) :
    chase (store σ (.field r f) v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun m e => by cases e) k n

end Gabbro.Body
