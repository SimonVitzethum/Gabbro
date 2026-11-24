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
  | .sub => ⟨a.wert - b.wert, Int.sub_le_sub a.unten b.oben, Int.sub_le_sub a.oben b.unten⟩


def Zahl.neg (a : Zahl lo hi) : Zahl (-hi) (-lo) :=
  ⟨-a.wert, Int.neg_le_neg a.oben, Int.neg_le_neg a.unten⟩

-- Mirror mul_endpoint_bounds using the unsigned and signed Int.tdiv bounds.
theorem Zahl.div_bounds (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂) (nonzero : Divisor lo₂ hi₂) :
    (quotientBounds lo₁ hi₁ lo₂).1 ≤ a.wert.tdiv b.wert ∧
      a.wert.tdiv b.wert ≤ (quotientBounds lo₁ hi₁ lo₂).2 := by
  sorry

def Zahl.div (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂) (nonzero : Divisor lo₂ hi₂) :
    Wert (quotientType lo₁ hi₁ lo₂) :=
  ⟨a.wert.tdiv b.wert, (a.div_bounds b nonzero).1, (a.div_bounds b nonzero).2⟩

def Compare.eval (op : Compare) (a b : Int) : Bool :=
  match op with
  | .eq => decide (a = b)
  | .ne => decide (a ≠ b)
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .gt => decide (b < a)
  | .ge => decide (b ≤ a)

def Logic.skips : Logic → Bool
  | .and => false
  | .or => true

def Umgebung (scope : Scope) := ∀ {type}, Local scope type → Wert type

def leereUmgebung : Umgebung [] := by
  intro type ref
  cases ref

/-- Mathematical expression evaluation retains the type index of the source node. -/
def Expr.wert (env : Umgebung scope) : Expr scope type → Wert type
  | .lit value => Zahl.literal value
  | .binary op left right => op.auswerten (left.wert env) (right.wert env)
  | .trueLit => true
  | .falseLit => false
  | .variable ref _ _ => env ref
  | .negativeLit magnitude => Zahl.literal (-(magnitude : Int))
  | .neg operand => (operand.wert env).neg
  | .not operand => !(operand.wert env)
  | .div left right nonzero => (left.wert env).div (right.wert env) nonzero
  | .compare op left right => op.eval (left.wert env).wert (right.wert env).wert
  | .logic op left right =>
    let a : Bool := left.wert env
    if a = op.skips then a else right.wert env

end Gabbro.Core.Ast
