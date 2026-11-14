module

public import Lean

@[expose] public section

namespace Gabbro.Body

inductive Value where
  | int (n : Int)
  | bool (t : Bool)
  | absent
  | present (n : Int)
  /-- **A `reason` -- the error value of the one error propagation** (2026-09-07). `let x =
      f() else (e) { … }` binds `e` to it; a `match` over it picks the arm by the case's
      name; `==` compares it. The name is the CASE (`Unbelegt`), not the declaration's,
      because that is how a `match` arm spells it. -/
  | reason (r : String)
  /-- **A `tagged` value** (2026-09-07): the case's name and its payload, where the payload
      is a NUMBER -- an index, an integer, or an opaque handle taken as its representation.
      A `tagged` type whose payload is anything else has no value here. -/
  | tagged (t : String) (payload : Option Int)
  /-- Ordered fields in declaration order. Nominal product identity is deliberately
      erased here: the bridge must reject cross-identity uses before translation.
      `record` avoids the reserved name of the generated `Value.rec` recursor. -/
  | record (fields : List Value)
  deriving Repr

/-- The shape of a value. **A sum carries its cases** -- the case's name and whether it
    has a payload -- so that a `tagged` value of the shape is one of the declared cases WITH
    the declared payload: a `match` over it then has an arm for every value the world can
    hold, and none of the model's arms gets stuck on a case the type excludes. -/
inductive Shape where
  | int | bool | opt
  /-- **A number in its declared range** (2026-09-08): a place of type `u8 in 0 .. 15`
      holds a number the checker keeps in range (`M1`), and the well-typed world says so
      -- a read from it comes with its bounds (`WF_intIn`), a store into it owes them. -/
  | intIn (lo hi : Int)
  /-- The cases of a `tagged` type, each with its payload: `none` -- no payload;
      `some none` -- a number; `some (some (lo, hi))` -- a number in its declared range
      (2026-09-08: the range is part of the type, and the checker keeps every payload in
      it, so a `match` arm that reads the payload has the range it has). -/
  | sum (cases : List (String × Option (Option (Int × Int))))
  /-- Field shapes in declaration order. Equal field shapes share this Body shape;
      nominal product identity remains a bridge-side translation obligation. -/
  | record (fields : List Shape)
  deriving Repr

/-- Whether a payload is what a case declares. -/
def Shape.payloadOk : Option (Option (Int × Int)) → Option Int → Bool
  | none, none => true
  | some none, some _ => true
  | some (some (lo, hi)), some n => decide (lo ≤ n ∧ n ≤ hi)
  | _, _ => false

/-- Whether a case with this name and payload is one of the declared cases. -/
def Shape.caseOk (cases : List (String × Option (Option (Int × Int)))) (t : String) (p : Option Int) : Bool :=
  cases.any (fun c => c.1 == t && Shape.payloadOk c.2 p)

/-! **`payloadOk`, computed** -- on a literal case, `simp` turns it into what the payload
    is: nothing, a number, or a number in its range. -/
@[simp] theorem Shape.payloadOk_none_iff (p : Option Int) : Shape.payloadOk none p = true ↔ p = none := by
  cases p <;> simp only [payloadOk, Bool.false_eq_true, reduceCtorEq]
@[simp] theorem Shape.payloadOk_some_none_iff (p : Option Int) :
    Shape.payloadOk (some none) p = true ↔ ∃ n, p = some n := by
  cases p <;> simp only [payloadOk, Bool.false_eq_true, reduceCtorEq, exists_const, Option.some.injEq, exists_eq']
@[simp] theorem Shape.payloadOk_range_iff (lo hi : Int) (p : Option Int) :
    Shape.payloadOk (some (some (lo, hi))) p = true ↔ ∃ n, p = some n ∧ lo ≤ n ∧ n ≤ hi := by
  cases p <;> simp only [payloadOk, Bool.false_eq_true, reduceCtorEq, false_and, exists_const, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, exists_eq_left']
@[simp] theorem Shape.payloadOk_none_none : Shape.payloadOk none none = true := by rfl
@[simp] theorem Shape.payloadOk_none_some (n : Int) : Shape.payloadOk none (some n) = false := by rfl
@[simp] theorem Shape.payloadOk_some_none_none : Shape.payloadOk (some none) none = false := by rfl
@[simp] theorem Shape.payloadOk_some_none_some (n : Int) : Shape.payloadOk (some none) (some n) = true := by rfl
@[simp] theorem Shape.payloadOk_range_none (lo hi : Int) : Shape.payloadOk (some (some (lo, hi))) none = false := by rfl
@[simp] theorem Shape.payloadOk_range_some (lo hi n : Int) :
    Shape.payloadOk (some (some (lo, hi))) (some n) = decide (lo ≤ n ∧ n ≤ hi) := by rfl

mutual
def Value.hasShape : Value → Shape → Bool
  | .int _, .int => true
  | .int n, .intIn lo hi => decide (lo ≤ n ∧ n ≤ hi)
  | .bool _, .bool => true
  | .absent, .opt => true
  | .present _, .opt => true
  | .tagged t p, .sum cs => Shape.caseOk cs t p
  | .record vs, .record ss => vs.length == ss.length && Value.fieldsHaveShape vs ss
  | _, _ => false
termination_by structural v _ => v

/-- Pointwise field checking, including equal arity. Kept mutually recursive with
    `hasShape` so nested record values decrease structurally through their field lists. -/
def Value.fieldsHaveShape : List Value → List Shape → Bool
  | [], [] => true
  | v :: vs, sh :: ss => v.hasShape sh && Value.fieldsHaveShape vs ss
  | _, _ => false
termination_by structural vs _ => vs
end

-- Lean's `deriving DecidableEq` does not support nested inductives. Decide each
-- tree together with its field list, preserving constructive equality for `binop`.
mutual
def Value.decEq (a b : Value) : Decidable (a = b) := by
  cases a <;> cases b <;> try (refine isFalse ?_; intro h; cases h; done)
  case int.int a b =>
    exact decidable_of_iff (a = b) (by simp only [Value.int.injEq])
  case bool.bool a b =>
    exact decidable_of_iff (a = b) (by simp only [Value.bool.injEq])
  case absent.absent => exact isTrue rfl
  case present.present a b =>
    exact decidable_of_iff (a = b) (by simp only [Value.present.injEq])
  case reason.reason a b =>
    exact decidable_of_iff (a = b) (by simp only [Value.reason.injEq])
  case tagged.tagged a p b q =>
    exact decidable_of_iff (a = b ∧ p = q) (by simp only [Value.tagged.injEq])
  case record.record as bs =>
    letI := Value.decFields as bs
    exact decidable_of_iff (as = bs) (by simp only [Value.record.injEq])
termination_by structural a

def Value.decFields : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => by
      letI := Value.decEq a b
      letI := Value.decFields as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp only [List.cons.injEq])
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
termination_by structural as _ => as
end

instance : DecidableEq Value := Value.decEq

mutual
def Shape.decEq (a b : Shape) : Decidable (a = b) := by
  cases a <;> cases b <;> try (refine isFalse ?_; intro h; cases h; done)
  case int.int => exact isTrue rfl
  case bool.bool => exact isTrue rfl
  case opt.opt => exact isTrue rfl
  case intIn.intIn lo hi lo' hi' =>
    exact decidable_of_iff (lo = lo' ∧ hi = hi') (by simp only [Shape.intIn.injEq])
  case sum.sum as bs =>
    exact decidable_of_iff (as = bs) (by simp only [Shape.sum.injEq])
  case record.record as bs =>
    letI := Shape.decFields as bs
    exact decidable_of_iff (as = bs) (by simp only [Shape.record.injEq])
termination_by structural a

def Shape.decFields : (as bs : List Shape) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => by
      letI := Shape.decEq a b
      letI := Shape.decFields as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp only [List.cons.injEq])
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
termination_by structural as _ => as
end

instance : DecidableEq Shape := Shape.decEq

@[simp] theorem Value.hasShape_record_record (vs : List Value) (ss : List Shape) :
    (Value.record vs).hasShape (.record ss) =
      (vs.length == ss.length && Value.fieldsHaveShape vs ss) := by
  rw [Value.hasShape]

@[simp] theorem Value.fieldsHaveShape_nil_nil : Value.fieldsHaveShape [] [] = true := by
  rw [Value.fieldsHaveShape]
@[simp] theorem Value.fieldsHaveShape_cons_cons (v : Value) (vs : List Value)
    (sh : Shape) (ss : List Shape) :
    Value.fieldsHaveShape (v :: vs) (sh :: ss) =
      (v.hasShape sh && Value.fieldsHaveShape vs ss) := by
  rw [Value.fieldsHaveShape]
@[simp] theorem Value.fieldsHaveShape_nil_cons (sh : Shape) (ss : List Shape) :
    Value.fieldsHaveShape [] (sh :: ss) = false := by simp [Value.fieldsHaveShape]
@[simp] theorem Value.fieldsHaveShape_cons_nil (v : Value) (vs : List Value) :
    Value.fieldsHaveShape (v :: vs) [] = false := by simp [Value.fieldsHaveShape]

@[simp] theorem Value.hasShape_int_record (n : Int) (ss : List Shape) :
    Value.hasShape (.int n) (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_bool_record (b : Bool) (ss : List Shape) :
    Value.hasShape (.bool b) (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_absent_record (ss : List Shape) :
    Value.hasShape .absent (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_present_record (n : Int) (ss : List Shape) :
    Value.hasShape (.present n) (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_reason_record (r : String) (ss : List Shape) :
    Value.hasShape (.reason r) (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_tagged_record (t : String) (p : Option Int) (ss : List Shape) :
    Value.hasShape (.tagged t p) (.record ss) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_record_int (vs : List Value) :
    (Value.record vs).hasShape .int = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_record_bool (vs : List Value) :
    (Value.record vs).hasShape .bool = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_record_opt (vs : List Value) :
    (Value.record vs).hasShape .opt = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_record_intIn (vs : List Value) (lo hi : Int) :
    (Value.record vs).hasShape (.intIn lo hi) = false := by simp [Value.hasShape]
@[simp] theorem Value.hasShape_record_sum (vs : List Value) (cs : List (String × Option (Option (Int × Int)))) :
    (Value.record vs).hasShape (.sum cs) = false := by simp [Value.hasShape]

/-- A record shape supplies the ordered field values, equal arity and pointwise shapes. -/
theorem Value.hasShape_rec_true (v : Value) (ss : List Shape)
    (h : v.hasShape (.record ss) = true) :
    ∃ vs, v = .record vs ∧ vs.length = ss.length ∧ Value.fieldsHaveShape vs ss = true := by
  cases v <;> simp only [Value.hasShape, Bool.false_eq_true] at h
  rename_i vs
  obtain ⟨hlen, hfields⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨vs, rfl, beq_iff_eq.mp hlen, hfields⟩

end Gabbro.Body
