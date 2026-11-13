module

public import Lean
public import Gabbro.Body.Teil9Rec

@[expose] public section



namespace Gabbro.Body

/-! ## 1. Values

    Scalar, option, tagged and positional record values. `option index into T` is `absent`/`present` -- **not
    `Option Int`**, because a value has to be comparable with every other value, and a sum
    type over `Int` would be two levels.
-/


/-! ## 2. Places

    A place is a location in the WORLD. Two forms: a table's slot field with an evaluated
    index, and a `static`.

    **`DecidableEq` here IS the alias freedom.** Two places are equal or distinct and nothing
    in between -- the statement that costs an alias analysis in the general case and that
    Gabbro carries.
-/

inductive Place where
  | slot (carrier : String) (index : Int) (field : String)
  /-- A field of a RECORD or a `format` -- `s.len`, `header.e_entry`. **No index**: a record
      is one object, not a table of them, and giving it a dummy index would make two
      different things one `Place` and let a slot alias a record field. -/
  | field (carrier : String) (name : String)
  | global (name : String)
  deriving DecidableEq

abbrev World := Place → Value
abbrev Binding := String → Value

/-- The state: the world and the local names. -/
structure State where
  world : World
  local' : Binding

/-- A pointwise write. **The frame falls out here** -- every other place survives. -/
def store (σ : World) (p : Place) (v : Value) : World :=
  fun q => if q = p then v else σ q

/-- **`bindLocal`, not `bind`.** A definition called `bind` is shadowed by `Bind.bind` from
    core, and `simp [bind]` then resolves to the class method instead of this function --
    measured: the speech test's TRUE theorem stopped going through, with the message
    *"Expected a proposition, but found `Binding → String → Value → Binding`"*. -/
def bindLocal (β : Binding) (n : String) (v : Value) : Binding :=
  fun m => if m = n then v else β m

@[simp] theorem store_here (σ : World) (p : Place) (v : Value) : store σ p v p = v := by
  simp only [store, ↓reduceIte]

@[simp] theorem store_elsewhere (σ : World) (p q : Place) (v : Value) (h : q ≠ p) :
    store σ p v q = σ q := by
  simp only [store, h, ↓reduceIte]

@[simp] theorem bindLocal_here (β : Binding) (n : String) (v : Value) : bindLocal β n v n = v := by
  simp only [bindLocal, ↓reduceIte]

@[simp] theorem bindLocal_elsewhere (β : Binding) (n m : String) (v : Value) (h : m ≠ n) :
    bindLocal β n v m = β m := by
  simp only [bindLocal, h, ↓reduceIte]

/-! ## 3. Expressions

    The list covers exactly what `refinement.rs` already has a term for, plus the PLACE WITH
    A SUFFIX -- and that is the whole gain. `messung/P6.md` §4.3 names it as the thing the
    Isabelle emitter has no model of: *"a place with suffixes is a location in the WORLD"*.
    Here is the world.
-/

inductive UnOp where
  | not
  | neg
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | mul
  /-- `/` and `%` -- **the C operators and not Lean's.** See `binop` and §3.2. -/
  | div | rem
  /-- `&`, `|`, `^` -- the bit MASKS, over non-negative operands and nowhere else. -/
  | band | bor | bxor
  /-- `<<`, `>>` -- likewise. -/
  | shl | shr
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving DecidableEq, Repr


/-! **`hasShape` on a constructor computes, and stays folded on a variable** -- these are
    the equations the simp set uses instead of unfolding the definition, so that a
    `hasShape v sh = true` about an unknown `v` keeps the form `gabbro_open` turns into a
    witness. -/
@[simp] theorem Value.hasShape_int_int (n : Int) : Value.hasShape (.int n) .int = true := by rfl
@[simp] theorem Value.hasShape_int_bool (n : Int) : Value.hasShape (.int n) .bool = false := by rfl
@[simp] theorem Value.hasShape_int_opt (n : Int) : Value.hasShape (.int n) .opt = false := by rfl
@[simp] theorem Value.hasShape_int_sum (cs : List (String × Option (Option (Int × Int)))) (n : Int) : Value.hasShape (.int n) (.sum cs) = false := by rfl
@[simp] theorem Value.hasShape_int_intIn (n lo hi : Int) : Value.hasShape (.int n) (.intIn lo hi) = decide (lo ≤ n ∧ n ≤ hi) := by rfl
@[simp] theorem Value.hasShape_bool_intIn (t : Bool) (lo hi : Int) : Value.hasShape (.bool t) (.intIn lo hi) = false := by rfl
@[simp] theorem Value.hasShape_absent_intIn (lo hi : Int) : Value.hasShape (.absent) (.intIn lo hi) = false := by rfl
@[simp] theorem Value.hasShape_present_intIn (n lo hi : Int) : Value.hasShape (.present n) (.intIn lo hi) = false := by rfl
@[simp] theorem Value.hasShape_reason_intIn (r : String) (lo hi : Int) : Value.hasShape (.reason r) (.intIn lo hi) = false := by rfl
@[simp] theorem Value.hasShape_tagged_intIn (t : String) (p : Option Int) (lo hi : Int) : Value.hasShape (.tagged t p) (.intIn lo hi) = false := by rfl
@[simp] theorem Value.hasShape_bool_int (t : Bool) : Value.hasShape (.bool t) .int = false := by rfl
@[simp] theorem Value.hasShape_bool_bool (t : Bool) : Value.hasShape (.bool t) .bool = true := by rfl
@[simp] theorem Value.hasShape_bool_opt (t : Bool) : Value.hasShape (.bool t) .opt = false := by rfl
@[simp] theorem Value.hasShape_bool_sum (cs : List (String × Option (Option (Int × Int)))) (t : Bool) : Value.hasShape (.bool t) (.sum cs) = false := by rfl
@[simp] theorem Value.hasShape_absent_int : Value.hasShape (.absent) .int = false := by rfl
@[simp] theorem Value.hasShape_absent_bool : Value.hasShape (.absent) .bool = false := by rfl
@[simp] theorem Value.hasShape_absent_opt : Value.hasShape (.absent) .opt = true := by rfl
@[simp] theorem Value.hasShape_absent_sum (cs : List (String × Option (Option (Int × Int)))) : Value.hasShape (.absent) (.sum cs) = false := by rfl
@[simp] theorem Value.hasShape_present_int (n : Int) : Value.hasShape (.present n) .int = false := by rfl
@[simp] theorem Value.hasShape_present_bool (n : Int) : Value.hasShape (.present n) .bool = false := by rfl
@[simp] theorem Value.hasShape_present_opt (n : Int) : Value.hasShape (.present n) .opt = true := by rfl
@[simp] theorem Value.hasShape_present_sum (cs : List (String × Option (Option (Int × Int)))) (n : Int) : Value.hasShape (.present n) (.sum cs) = false := by rfl
@[simp] theorem Value.hasShape_reason_int (r : String) : Value.hasShape (.reason r) .int = false := by rfl
@[simp] theorem Value.hasShape_reason_bool (r : String) : Value.hasShape (.reason r) .bool = false := by rfl
@[simp] theorem Value.hasShape_reason_opt (r : String) : Value.hasShape (.reason r) .opt = false := by rfl
@[simp] theorem Value.hasShape_reason_sum (cs : List (String × Option (Option (Int × Int)))) (r : String) : Value.hasShape (.reason r) (.sum cs) = false := by rfl
@[simp] theorem Value.hasShape_tagged_int (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .int = false := by rfl
@[simp] theorem Value.hasShape_tagged_sum (t : String) (p : Option Int) (cs : List (String × Option (Option (Int × Int)))) :
    Value.hasShape (.tagged t p) (.sum cs) = Shape.caseOk cs t p := by rfl
@[simp] theorem Value.hasShape_tagged_bool (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .bool = false := by rfl
@[simp] theorem Value.hasShape_tagged_opt (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .opt = false := by rfl

/-! **A shape, as a witness.** `v.hasShape .int = true` says WHAT `v` is; these turn that
    into the equation a proof rewrites with. -/
theorem Value.hasShape_int_true (v : Value) (h : v.hasShape .int = true) : ∃ n, v = .int n := by
  cases v <;> simp only [hasShape, int.injEq, exists_eq', Bool.false_eq_true] at h ⊢
theorem Value.hasShape_bool_true (v : Value) (h : v.hasShape .bool = true) : ∃ b, v = .bool b := by
  cases v <;> simp only [hasShape, Bool.false_eq_true, bool.injEq, exists_eq'] at h ⊢
theorem Value.hasShape_intIn_true (v : Value) (lo hi : Int) (h : v.hasShape (.intIn lo hi) = true) :
    ∃ n, v = .int n ∧ lo ≤ n ∧ n ≤ hi := by
  cases v <;> simp only [hasShape, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, int.injEq, exists_eq_left', Bool.false_eq_true] at h ⊢
  exact h
theorem Value.hasShape_sum_true (v : Value) (cs : List (String × Option (Option (Int × Int)))) (h : v.hasShape (.sum cs) = true) :
    ∃ t p, v = .tagged t p ∧ Shape.caseOk cs t p = true := by
  cases v <;> simp only [hasShape, Bool.false_eq_true, tagged.injEq] at h ⊢
  exact ⟨_, _, ⟨rfl, rfl⟩, h⟩

/-- **`caseOk`, computed** -- for a literal case list, `simp` decides the names and leaves
    the payload: `p.isSome = true` or `p.isSome = false`. -/
@[simp] theorem Shape.caseOk_cons (c : String × Option (Option (Int × Int))) (cs : List (String × Option (Option (Int × Int)))) (t : String) (p : Option Int) :
    Shape.caseOk (c :: cs) t p = ((c.1 == t && Shape.payloadOk c.2 p) || Shape.caseOk cs t p) := by
  simp only [caseOk, List.any_cons]
@[simp] theorem Shape.caseOk_nil (t : String) (p : Option Int) : Shape.caseOk [] t p = false := by rfl
@[simp] theorem isSome_true_iff (o : Option Int) : o.isSome = true ↔ ∃ n, o = some n := by
  cases o <;> simp only [Option.isSome_none, Bool.false_eq_true, reduceCtorEq, exists_const, Option.isSome_some, Option.some.injEq, exists_eq']
@[simp] theorem isSome_false_iff (o : Option Int) : o.isSome = false ↔ o = none := by
  cases o <;> simp only [Option.isSome_none, Option.isSome_some, Bool.true_eq_false, reduceCtorEq]
theorem Value.hasShape_opt_true (v : Value) (h : v.hasShape .opt = true) :
    v = .absent ∨ ∃ n, v = .present n := by
  cases v <;> simp only [hasShape, Bool.false_eq_true, reduceCtorEq, exists_const, or_false, present.injEq, exists_eq', or_true] at h ⊢

inductive Expr where
  | lit (v : Value)
  | name (n : String)
  | place (carrier : String) (index : Expr) (field : String)
  | global (name : String)
  | un (op : UnOp) (a : Expr)
  | bin (op : BinOp) (a b : Expr)
  /-- `Some(e)` -- the one value CONSTRUCTOR the corpus writes. `None` needs none: it is a
      literal. **A body that writes an option and could not say `Some` would have to be
      refused whole**, and `27-freiliste` is exactly that shape. -/
  | someOf (a : Expr)
  /-- `s.len` -- a field of a record or a `format`. -/
  | fieldOf (carrier : String) (name : String)
  /-- `forall v in slots of T : body` -- **a BOUNDED quantifier over the index domain
      `0 ..< count`**, and `count` is read from the `table` declaration by the emitter
      (2026-09-07).

      It is an `Expr` and not a `Prop`, and that decision is what makes a callee's
      `requires forall x in slots of o : …` a stuck-condition at the call (see `step`) --
      a precondition that lived on the `Prop` side could be assumed but never DEMANDED. The
      `Prop` reading stands beside it as a theorem (`eval_forallSlots`), so a proof may
      switch to `∀ k, 0 ≤ k → k < count → …` the moment it wants to. -/
  | forallSlots (v : String) (count : Int) (body : Expr)
  | existsSlots (v : String) (count : Int) (body : Expr)
  /-- `T.slots[from] reaches T.slots[to] via field` -- the REFLEXIVE-TRANSITIVE chain over
      an option-index field, with the table's `count` as fuel.

      **The fuel is exact and not a cut-off.** A chain that has not reached `to` after
      `count` steps has visited `count + 1` slots of a table with `count` of them, so it has
      repeated one -- and a chain that repeats a slot never reaches anything it has not
      reached already. `reaches_of_chase` and `chase_of_reaches` say so. -/
  | reaches (carrier : String) (src dst : Expr) (via : String) (count : Int)
  /-- `x in chain(h, n) in T.slots[p]` -- **the linked list**: `head` is the option field
      the chain starts at (`T.slots[p].h`), and `x` is on the chain if the `via`-chain from
      the head's slot reaches it. An absent head is an empty chain. -/
  | chainFrom (carrier : String) (head x : Expr) (via : String) (count : Int)
  /-- **`n` carries the declared shape** -- the type test the checker decides (`M1`) and a
      contract needs as a WORD (2026-09-07): a callee's precondition has to be able to
      demand that `p` is a number before it can say `p < 64`, and a loop invariant has to
      carry the shape of every local in scope across the pass, or the pass after it reads
      an unconstrained value. *It is written by the emitter out of declarations and never
      guessed from a use.* -/
  | hasShape (n : String) (sh : Shape)
  /-- **A value stored into a `wrapping` place is REDUCED to its width** (2026-09-07).
      `u32 wrapping` is the one type whose overflow is the point; `M1` suppresses the
      overflow refusal on it, so the model has to compute what the machine computes: the
      value modulo `2^bits`, signed or not. Read-side nothing changes -- the place holds
      what was stored. -/
  | wrapTo (bits : Nat) (signed : Bool) (a : Expr)
  /-- `Case(e)` / `Case` -- a `tagged` value; the payload, where there is one, must
      evaluate to a number. -/
  | tagOf (t : String) (payload : Option Expr)
  /-- Construct fields in declaration order; nominal identity is checked and erased by
      the bridge, never resolved from names during evaluation. -/
  | recOf (args : List Expr)
  /-- Read a positional field. The bridge must emit `idx < fields.length` from the
      schema; a non-record base or an out-of-range index gets stuck. -/
  | recGet (base : Expr) (idx : Nat)
  /-- Replace a positional field. The bridge must emit `idx < fields.length` from the
      schema; nominal identity is checked before erasure, and invalid access gets stuck. -/
  | recSet (base : Expr) (idx : Nat) (val : Expr)
  deriving Repr

/-- Two's complement reduction to `bits` -- `Int.emod`, so the unsigned form is never
    negative. -/
def wrap (bits : Nat) (signed : Bool) (n : Int) : Int :=
  let m : Int := 2 ^ bits
  if signed then ((n + m / 2) % m) - m / 2 else n % m

/-- `∀ k < n, f k` over `Option Bool` -- **stuck on the first `k` where `f` is.**

    **Sealed behind an `opaque` constant, on purpose.** A definition the reducer can unfold
    unfolds in the KERNEL as far as the literal reaches -- and a `count 4096` table then
    costs four thousand nested reductions the moment `simp` looks at a `match` whose
    discriminant mentions the quantifier next to a free state: measured as *"(kernel) deep
    recursion detected"* on the first loop of `beispiele/01`, with a structural definition
    and with a well-founded one alike. `allBelow` is the first projection of an opaque
    package and reduces to nothing; a proof unfolds it exactly as often as it says so,
    through `allBelow_zero`/`allBelow_succ` (and `allBelow_true_iff`). -/
def allBelowImpl (f : Nat → Option Value) : Nat → Option Value
  | 0 => some (.bool true)
  | n + 1 =>
      match allBelowImpl f n, f n with
      | some (.bool a), some (.bool b) => some (.bool (a && b))
      | _, _ => none

opaque allBelowPkg : { g : (Nat → Option Value) → Nat → Option Value // g = allBelowImpl } :=
  ⟨allBelowImpl, rfl⟩

def allBelow : (Nat → Option Value) → Nat → Option Value := allBelowPkg.1

theorem allBelow_eq : allBelow = allBelowImpl := allBelowPkg.2

/-- `∃ k < n, f k` -- the same, disjunctively. -/
def anyBelowImpl (f : Nat → Option Value) : Nat → Option Value
  | 0 => some (.bool false)
  | n + 1 =>
      match anyBelowImpl f n, f n with
      | some (.bool a), some (.bool b) => some (.bool (a || b))
      | _, _ => none

opaque anyBelowPkg : { g : (Nat → Option Value) → Nat → Option Value // g = anyBelowImpl } :=
  ⟨anyBelowImpl, rfl⟩

def anyBelow : (Nat → Option Value) → Nat → Option Value := anyBelowPkg.1

theorem anyBelow_eq : anyBelow = anyBelowImpl := anyBelowPkg.2

/-- **The chain, followed with fuel.** `some true` -- reached within `fuel` steps; `some
    false` -- not reached within them; `none` -- the `via` field of a visited slot does not
    carry an option, which is the well-formedness premise `U2` failing under our feet.
    Sealed like `allBelow`, for the same reason. -/
def chaseImpl (σ : World) (c via : String) (to : Int) : Int → Nat → Option Value
  | k, 0 => some (.bool (decide (k = to)))
  | k, n + 1 =>
      if k = to then some (.bool true)
      else
        match σ (.slot c k via) with
        | .present m => chaseImpl σ c via to m n
        | .absent => some (.bool false)
        | _ => none

opaque chasePkg : { g : World → String → String → Int → Int → Nat → Option Value // g = chaseImpl } :=
  ⟨chaseImpl, rfl⟩

def chase : World → String → String → Int → Int → Nat → Option Value := chasePkg.1

theorem chase_eq : chase = chaseImpl := chasePkg.2

/-- **An evaluation may GET STUCK.** `none` means the value did not have the shape the
    operator needs. That is not an error case one may define away -- the world is an
    unconstrained map, and that a slot field carries the shape its declaration names is
    hypothesis `U2` and stands per unit as a premise.

    *A model that substituted a default value here would prove statements for a reason the
    machine does not have* -- the same trap `messung/P6.md` §2.1 names for `nat`. -/
def unop : UnOp → Value → Option Value
  | .not, .bool t => some (.bool (!t))
  | .neg, .int n => some (.int (-n))
  | _, _ => none

/-- **A bit mask, over the NON-NEGATIVE integers and nowhere else.**

    For `0 ≤ a` and `0 ≤ b` the C operators `&`, `|`, `^` are the plain binary operations on
    the binary digits, and that answer does not depend on a WIDTH: neither operand has a sign
    bit, and none of the three can carry a digit out of the operands' own range. **That is
    the whole reason the guard is here.** With a negative operand the C answer is read off a
    two's complement of a width this model does not have -- and worse, the usual arithmetic
    conversions may first turn the negative operand into a large unsigned one, so that even
    the width would not settle it. *Getting stuck is the honest answer; a width-independent
    formula would compute something the machine does not.*

    The detour through `Nat` is the same statement in the type: `Int.toNat` is faithful
    exactly where the guard holds. -/
def bits (f : Nat → Nat → Nat) (a b : Int) : Option Value :=
  if 0 ≤ a ∧ 0 ≤ b then some (.int ((f a.toNat b.toNat : Nat) : Int)) else none

def binop : BinOp → Value → Value → Option Value
  | .add, .int a, .int b => some (.int (a + b))
  | .sub, .int a, .int b => some (.int (a - b))
  | .mul, .int a, .int b => some (.int (a * b))
  -- **`Int.tdiv` and `Int.tmod`, and NOT `/` and `%`.** Lean's own `/` on `Int` is the
  -- Euclidean one -- `(-7) / 2` is `-4` -- and C truncates toward zero -- `-3`. The two are
  -- different functions, and §3.2 writes that difference down as a theorem so that a later
  -- tidying to `/` fails there first.
  --
  -- **A zero denominator gets the model STUCK.** Lean answers -- `a.tdiv 0` is `0` and
  -- `a.tmod 0` is `a`; C says nothing at all.
  -- `M102` already refuses a denominator whose range does not exclude zero, so no accepted
  -- program is turned away by this -- but a model that *defined* the case would let a goal
  -- close on a value the machine never produces, and that is the one thing this file is
  -- against. The premise is now visible: whoever proves through a division proves the
  -- denominator non-zero, out of a guard or out of a `requires`.
  | .div, .int a, .int b => if b = 0 then none else some (.int (a.tdiv b))
  | .rem, .int a, .int b => if b = 0 then none else some (.int (a.tmod b))
  | .band, .int a, .int b => bits (· &&& ·) a b
  | .bor, .int a, .int b => bits (· ||| ·) a b
  | .bxor, .int a, .int b => bits (· ^^^ ·) a b
  -- **The shifts, and they carry the same guard for the same reason plus one more.** A shift
  -- COUNT at or above the operand's width is undefined in C, and this model has no width --
  -- so that bound is booked where the header books every other one: `typen::schiebe_links`
  -- and `typen::schiebe_rechts` mark `b.max >= a.breite` as an overflow, and `M104` refuses
  -- it. *Under that booking `a << b` IS `a * 2^b` and `a >> b` IS `a / 2^b`*, written out
  -- here rather than hidden in a `ShiftLeft Int` instance, because the reader of this file
  -- has to be able to check the claim.
  --
  -- **The negative left operand is NOT booked, it is refused.** `>>` on a negative signed
  -- value is *implementation-defined* in C (C99 6.5.7p5), not undefined -- so `M104` never
  -- fires on it, and `typen::schiebe_rechts` lets `a.min < 0` through with the full range.
  -- A model that picked the arithmetic shift here would pick one compiler's answer and call
  -- it the language's.
  | .shl, .int a, .int b => if 0 ≤ a ∧ 0 ≤ b then some (.int (a * 2 ^ b.toNat)) else none
  | .shr, .int a, .int b =>
      if 0 ≤ a ∧ 0 ≤ b then some (.int (a.tdiv (2 ^ b.toNat))) else none
  | .lt, .int a, .int b => some (.bool (decide (a < b)))
  | .le, .int a, .int b => some (.bool (decide (a ≤ b)))
  | .gt, .int a, .int b => some (.bool (decide (a > b)))
  | .ge, .int a, .int b => some (.bool (decide (a ≥ b)))
  | .and, .bool x, .bool y => some (.bool (x && y))
  | .or, .bool x, .bool y => some (.bool (x || y))
  -- **Equality stands over ALL values**, not only over numbers: `c.slots[s].elter == None`
  -- is exactly this form, and it is the commonest postcondition in the corpus.
  | .eq, x, y => some (.bool (decide (x = y)))
  | .ne, x, y => some (.bool (decide (x ≠ y)))
  | _, _, _ => none

/-- **The two connectives, held apart from `binop`** (2026-09-07). `andBool (eval s a)
    (eval s b)` is what `eval s (.bin .and a b)` reduces to -- and `andBool` is NOT unfolded
    by the model's simp set, so that `andBool_true_iff` can split a conjunction that is
    true into its two halves even where one half stays symbolic (a `forallSlots`, a read
    from a state the environment answered). The computing cases are simp lemmas of their
    own (`andBool_some`). Until today a conjunction with one symbolic half was a stuck
    `match`, and the person opened it by hand. -/
def andBool : Option Value → Option Value → Option Value
  | some (.bool x), some (.bool y) => some (.bool (x && y))
  | _, _ => none

def orBool : Option Value → Option Value → Option Value
  | some (.bool x), some (.bool y) => some (.bool (x || y))
  | _, _ => none

@[simp] theorem andBool_some (x y : Bool) : andBool (some (.bool x)) (some (.bool y)) = some (.bool (x && y)) := by rfl
@[simp] theorem orBool_some (x y : Bool) : orBool (some (.bool x)) (some (.bool y)) = some (.bool (x || y)) := by rfl
@[simp] theorem andBool_none_left (y : Option Value) : andBool none y = none := by cases y <;> rfl
end Gabbro.Body
