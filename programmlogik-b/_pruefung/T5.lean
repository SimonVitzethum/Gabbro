import Gabbro.Body
open Gabbro.Body
example (a b c : Nat) (h : a = 1 ∧ b = 2 ∧ c = 3) : c = 3 := by
  gabbro_assumption
example (a b c : Nat) (h : a = 1 ∧ b = 2 ∧ c = 3) : b = 2 := by
  gabbro_wf shapeOf
example (Γ : Typing) (σ : World) (h : WF Γ σ ∧ True) : WF Γ (store σ (.global "x") (.int 3)) := by
  gabbro_wf Γ
