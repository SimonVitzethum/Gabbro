/-
  File:      stage0/Stage0/Senke/Ausdruck/Aggregat/WideInt/Proben.lean
  Subject:   Acceptance witnesses of the multiword integer lowering on the model: operands that need two or
             three limbs are emitted, not refused, for every operator of lane IR-02.

  The textual programs of `stage0/proben-ir/wide-*` run the same lowering on the assembly runner. `eng` has no
  textual form over a wide input (only the `update` body of an atomic exchange produces it), so its witness is
  here; it also fixes the code shape: input, extension, narrowing test, branch, fallback.
-/
import Stage0.Senke.Ausdruck.Satz

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} (L : Lay D)

abbrev wideA : Int := 2 ^ 100
abbrev wideB : Int := 3

theorem lowE_wide_ring_zeuge :
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.add (.lit wideA) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.sub (.lit wideA) (.lit wideB)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.mul (.lit wideA) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.neg (.lit wideA)) 0 = some (c, top)) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

theorem lowE_wide_division_zeuge :
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.div (by decide) (by decide) (.lit wideA) (.lit wideB)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.rem (by decide) (by decide) (.lit wideA) (.lit wideB)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.sdiv (Or.inl (by decide)) (.lit (-wideA)) (.lit wideB)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.srem (Or.inr (by decide)) (.lit (-wideA)) (.lit (-wideB))) 0 = some (c, top)) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

theorem lowE_wide_order_zeuge :
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.lt (.lit (-wideA)) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.le (.lit (-wideA)) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := []) (Expr.eq (.lit wideA) (.lit wideA)) 0 = some (c, top)) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

theorem lowE_wide_bits_zeuge :
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.band (by decide) (by decide) (.lit wideA) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.bor 101 (by decide) (by decide) (by decide) (by decide) (.lit wideA) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.bxor 101 (by decide) (by decide) (by decide) (by decide) (.lit wideA) (.lit wideA)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.shl 101 (by decide) (by decide) (by decide) (by decide) (.lit wideA) (.lit wideB)) 0 = some (c, top)) ∧
    (∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.shr 101 (by decide) (by decide) (by decide) (by decide) (.lit wideA) (.lit wideB)) 0 = some (c, top)) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

/-- Narrowing a 101-bit input to an interval of its own width: lowered with the test and the branch. -/
theorem lowE_wide_eng_zeuge :
    ∃ c top, lowE L (reserved := 0) (Γ := []) (Λ := [])
      (Expr.eng (.lit wideA) wideA wideA (.lit wideA)) 0 = some (c, top) :=
  ⟨_, _, rfl⟩

end Gabbro.Stage0.Senke
