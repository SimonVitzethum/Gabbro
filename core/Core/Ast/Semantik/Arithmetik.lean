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

def Wert : {kind : Kind} → Ty kind → Type
  | _, .int lo hi => Zahl lo hi
  | _, .bool => Bool
  | _, .array element count => Vector (Wert element) count
  | _, .productEnd => PUnit
  | _, .product head tail => Wert head × Wert tail
  | _, .record _ _ layout => Wert layout
  | _, .recordSchema .. | _, .variantSchema .. | _, .carrierSchema .. | _, .effectGroupSchema .. => PUnit
  | _, .sumEnd => Empty
  | _, .sum head tail => Sum (Wert head) (Wert tail)
  | _, .variant _ _ _ layout => Wert layout
  | _, .text capacity => TextValue capacity

def indexOptionPresent (value : Wert (indexOptionType count)) : Bool :=
  match value with
  | .inl _ => true
  | .inr _ => false

/-- Widening changes interval evidence and the type of a zero-length array. -/
def Wert.widen (source target : Ty .value) (fits : Fits source target) (value : Wert source) :
    Wert target := by
  cases source <;> cases target
  case int.int lo hi lower upper =>
    exact ⟨value.wert, Int.le_trans fits.1 value.unten, Int.le_trans value.oben fits.2⟩
  case array.array source count target other =>
    cases count <;> cases other <;>
      first
      | exact #v[]
      | simp only [Fits] at fits <;> (cases fits <;> exact value)
  case text.text source target => exact TextValue.widen value fits
  all_goals
    first
    | exact value
    | simp only [Fits] at fits <;> (cases fits <;> exact value)

def tupleGet : (types : List (Ty .value)) → (i : Fin types.length) →
    Wert (tupleType types) → Wert (types.get i)
  | [], index, _value => Fin.elim0 index
  | _ :: rest, ⟨0, _⟩, values => values.1
  | _ :: rest, ⟨n + 1, bound⟩, values => tupleGet rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ values.2

def tupleOfFn : (types : List (Ty .value)) → ((i : Fin types.length) → Wert (types.get i)) →
    Wert (tupleType types)
  | [], _ => PUnit.unit
  | _ :: tail, values => (values 0, tupleOfFn tail fun i => values i.succ)

def tupleSet : (types : List (Ty .value)) → (i : Fin types.length) →
    Wert (types.get i) → Wert (tupleType types) → Wert (tupleType types)
  | [], i, _value, _old => Fin.elim0 i
  | _ :: _, ⟨0, _⟩, value, old => (value, old.2)
  | _ :: tail, ⟨n + 1, bound⟩, value, old =>
    (old.1, tupleSet tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ value old.2)

def variantInject : (cases : List (Option (Ty .value))) → (index : Fin cases.length) →
    Wert ((cases.get index).getD .productEnd) → Wert (variantLayout cases)
  | [], index, _value => Fin.elim0 index
  | _ :: _, ⟨0, _⟩, value => .inl value
  | _ :: tail, ⟨n + 1, bound⟩, value =>
    .inr (variantInject tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ value)

def indexPosition {count : Nat} (i : Zahl lo hi) (lower : 0 ≤ lo) (upper : hi < (count : Int)) : Fin count :=
  have nonnegative := Int.le_trans lower i.unten
  have bound : (i.wert.toNat : Int) < (count : Int) := by
    rw [Int.toNat_of_nonneg nonnegative]
    exact Int.lt_of_le_of_lt i.oben upper
  ⟨i.wert.toNat, Int.ofNat_lt.mp bound⟩

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

def byteValue (byte : UInt8) : Zahl 0 255 :=
  ⟨byte.toNat, Int.natCast_nonneg _, by
    have := byte.toBitVec.isLt
    change byte.toNat < 256 at this
    omega⟩

def TextValue.lengthValue (text : TextValue capacity) : Zahl 0 capacity :=
  ⟨text.bytes.size, Int.natCast_nonneg _, Int.ofNat_le.mpr text.bound⟩

def Umgebung (scope : Scope) := ∀ {type}, Local scope type → Wert type

def leereUmgebung : Umgebung [] := by
  intro type ref
  cases ref

mutual

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
  | .arrayValue (types := types) (element := element) items _ fits =>
    let values := items.wert env
    Vector.ofFn fun i => Wert.widen (types.get i) element (fits i) (tupleGet types i values)
  | .arrayIndex base index lower upper =>
    let position := indexPosition (index.wert env) lower upper
    let values : Vector (Wert _) _ := base.wert env
    values[position.val]'position.isLt
  | .tupleValue first second tail => (first.wert env, second.wert env, tail.wert env)
  | .tupleField (first := first) (second := second) (types := rest) base i =>
    tupleGet (first :: second :: rest) i (base.wert env)
  | .recordValue (types := types) (actualTypes := actualTypes) _ args fields fits =>
    let values := args.wert env
    tupleOfFn types fun i => Wert.widen (actualTypes.get (fields.slot i)) (types.get i) (fits i)
      (tupleGet actualTypes (fields.slot i) values)
  | .recordField (types := types) base _ index _ =>
    let record := base.wert env
    tupleGet types index record
  | .variantValue (payloads := payloads) _ _ index _ _ _ payload =>
    variantInject payloads index (payload.wert env)
  | .textLiteral decoded => TextValue.literal decoded
  | .textConcat left right => (left.wert env).concat (right.wert env)
  | .textIndex base offset =>
    byteValue ((base.wert env).bytes[(offset.wert env).wert.toNat]?.getD 0)
  | .substring base first last =>
    (base.wert env).slice (first.wert env).wert.toNat (last.wert env).wert.toNat
  | .textLength base => (base.wert env).lengthValue
  | .optionIsSome ref _ _ => indexOptionPresent (env ref)

def ExprItems.wert (env : Umgebung scope) : ExprItems scope types → Wert (tupleType types)
  | .empty => PUnit.unit
  | .next head tail => (head.wert env, tail.wert env)

def LabeledItems.wert (env : Umgebung scope) : LabeledItems scope labels types → Wert (tupleType types)
  | .empty => PUnit.unit
  | .next _ head tail => (head.wert env, tail.wert env)

def CasePayload.wert (env : Umgebung scope) : CasePayload scope type → Wert (type.getD .productEnd)
  | .nullary _ => PUnit.unit
  | .value expression => expression.wert env

end

end Gabbro.Core.Ast
