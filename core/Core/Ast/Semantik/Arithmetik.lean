module

public import Core.Ast.Tree

@[expose] public section

namespace Gabbro.Core.Ast

/-- A source integer carries both bounds of its declared interval. -/
structure Zahl (lo hi : Int) where
  wert : Int
  unten : lo ≤ wert
  oben : wert ≤ hi

def Zahl.literal (value : Int) : Zahl value value :=
  ⟨value, Int.le_refl _, Int.le_refl _⟩

def Wert : Ty .value → Type
  | .int lo hi => Zahl lo hi
  | .bool => Bool

/-- Multiplying a bounded integer by a fixed factor stays between the two
    endpoint products, in either order. -/
theorem mul_endpoint_bounds (a : Zahl lo hi) (k : Int) :
    min (lo * k) (hi * k) ≤ a.wert * k ∧ a.wert * k ≤ max (lo * k) (hi * k) := by
  rcases Int.le_total 0 k with positive | negative
  · exact ⟨Int.le_trans (Int.min_le_left _ _) (Int.mul_le_mul_of_nonneg_right a.unten positive),
      Int.le_trans (Int.mul_le_mul_of_nonneg_right a.oben positive) (Int.le_max_right _ _)⟩
  · exact ⟨Int.le_trans (Int.min_le_right _ _) (Int.mul_le_mul_of_nonpos_right a.oben negative),
      Int.le_trans (Int.mul_le_mul_of_nonpos_right a.unten negative) (Int.le_max_left _ _)⟩

def Zahl.mul (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂) :
    Zahl (Arith.mul.bounds lo₁ hi₁ lo₂ hi₂).1 (Arith.mul.bounds lo₁ hi₁ lo₂ hi₂).2 := by
  have left := mul_endpoint_bounds b lo₁
  have right := mul_endpoint_bounds b hi₁
  rw [Int.mul_comm lo₂ lo₁, Int.mul_comm hi₂ lo₁, Int.mul_comm b.wert lo₁] at left
  rw [Int.mul_comm lo₂ hi₁, Int.mul_comm hi₂ hi₁, Int.mul_comm b.wert hi₁] at right
  have middle := mul_endpoint_bounds a b.wert
  exact ⟨a.wert * b.wert,
    Int.le_trans (Int.le_min.mpr ⟨Int.le_trans (Int.min_le_left _ _) left.1,
      Int.le_trans (Int.min_le_right _ _) right.1⟩) middle.1,
    Int.le_trans middle.2 (Int.max_le.mpr ⟨Int.le_trans left.2 (Int.le_max_left _ _),
      Int.le_trans right.2 (Int.le_max_right _ _)⟩)⟩

def Arith.auswerten (op : Arith) (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂) :
    Zahl (op.bounds lo₁ hi₁ lo₂ hi₂).1 (op.bounds lo₁ hi₁ lo₂ hi₂).2 :=
  match op with
  | .add => ⟨a.wert + b.wert, Int.add_le_add a.unten b.unten, Int.add_le_add a.oben b.oben⟩
  | .mul => a.mul b

/-- The exact mathematical result has the interval computed by the constructor. -/
def Expr.wert : Expr scope type → Wert type
  | .lit value => Zahl.literal value
  | .binary op left right => op.auswerten left.wert right.wert

end Gabbro.Core.Ast
