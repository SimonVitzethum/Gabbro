/-
  File:    Gabbro/Body.lean
  Subject: What a Gabbro BODY means -- the statement descent as a state transition.

  WHY THIS FILE IS NOT IN `passlogik/`
    `passlogik/` formalises the CHECKER -- range lattices, effect hulls, rank order. Those
    are statements about PASSES. This one is a statement about PROGRAMS, and the two must not
    live in one namespace: a theorem about a pass read as a theorem about a program is a
    different claim with different consequences.

  WHAT IT CLOSES
    `passlogik/README.md` books the same missing item four times (`B1`, `L1`, `P2`, `R1`):

        "The STATEMENT DESCENT -- what a body does statement by statement -- stands in NONE
         of the seven files."

    And `messung/P6.md` measures what hangs on it: of 62 obligations, `refinement.rs` refuses
    seventeen with `body-effect`, because there is no meaning of a Gabbro body -- ten `N`,
    six `E`, and the one `R`.

  WHAT IS MODELLED
    A WORLD as an assignment of places (a table's slot field, a `static`) to values, a local
    binding for `let` names, and the descent over the SEQUENTIAL CORE: `let`, assignment,
    `if`, `match` over `option`, `return`.

    **And since 2026-09-07 the composition** -- everything that was a person's plumbing
    until then, and is the generator's now (`crates/gabbro-check/src/lean.rs`):
      * a CALL over the callee's contract (§4.1: `Contract`, `Frame`), with the callee's
        `requires` as the stuck-condition of the call;
      * a LOOP as an anonymous routine with a rule (`LoopRule`), the exits `next`/`leave`,
        and a `return` inside one desugared to a flagged `leave`;
      * the bounded QUANTIFIER over a table's index domain and the parent CHAIN
        (`forallSlots`, `existsSlots`, `reaches`, `chainFrom`) -- as expressions, so that a
        contract may demand them;
      * the error propagation (`bindCallElse`, `Value.reason`), `tagged` values
        (`Value.tagged`, `onTag`), `wrapping` stores (`wrapTo`), `narrow` (an `ite`);
      * the well-typed world as ONE typing per unit (`WF`, §4.0), and the two theorems that
        make it free (`WF_store`, `WF_int`);
      * and the wiring: `contract_of_duty`, `looprule_of_body` (§5.1) -- the induction over
        the call graph and over the passes, done once here and instantiated per unit.

  WHAT THE PLUMBING ALREADY CARRIES -- and what this model therefore need not build
    This is the whole reason the file is short. Every line names the theorem that allows it:

      overflow      Integers are `Int`, unbounded.
                    -> `Passlogik.Bereich.passt_dann_kein_ueberlauf` (`M104`)
      shift width   A shift COUNT at or above the operand's width is undefined in C, and
                    there is no width here. It is booked as an overflow like every other:
                    `typen::schiebe_links`/`schiebe_rechts` mark `b.max >= a.breite`.
                    -> `M104`.  **This booking is void for a `wrapping` operand** -- see
                    §3.2 and DOES NOT COVER below.
      zero divisor  A denominator whose range does not exclude zero is refused.
                    -> `M102`.  The model does NOT lean on it: it gets stuck at zero, so
                    the premise stays visible in every proof that goes through a `/`.
      frame         The frame IS the declared `effects` list; a place outside it survives.
                    -> `Passlogik.Wirkung.huelle_deckt` (`E005`/`E008`)
      alias         Two distinct `Place`s are distinct places, full stop.
                    -> the alias passes; `A1` closed 2026-08-24 with `R007`
      termination   The core has no loop -- and the loop forms carry their measure.
                    -> `K008`/`K009`, `Bereich.keine_unendliche_verengung`
      races         Sequential reading is sound; `Held(L)` holds at the body's entry.
                    -> `H005`/`H006`/`H012`/`H016`

    **Hence there is NO heap model here, NO separation logic, NO pointers and NO
    concurrency.** A state is a map from places to values. Whoever reads this file without
    reading the plumbing alongside will take the model for naive -- it is the cashed-out form
    of this folder's thesis.

  ASSUMED RATHER THAN PROVED
    (U1) That the EMITTER (`crates/gabbro-check/src/lean.rs`) translates a Gabbro body into a
         `Stmt` datum correctly does not stand here. That is the same seam the other seven
         files have -- only this one is drawn mechanically and is therefore mutable.
         `instrumente/pruefe-lean-beweis.sh` drives it in both directions.
    (U2) The WELL-FORMED state -- that a slot field carries a value of its declared shape --
         is a hypothesis and not a consequence. The emitter writes it per unit out of the
         `table` declaration; it stands visibly in the theory.
    (U3) Two distinct carrier names denote two distinct objects. That is the alias statement,
         and the alias passes carry it -- no line here does.

  DOES NOT PROVE
    That a body terminates (the core has no loop -- there is nothing to show), that it is
    overflow-free (`M104`), or that it respects its frame (`E005`).

  DOES NOT COVER, and the names are here rather than in a commit message
    (N1) A bit operation or a shift with a NEGATIVE operand. The C answer is read off a
         two's complement of a width this file does not have -- and for `>>` it is
         *implementation-defined* even then, so `M104` never fires on it either. `binop`
         gets stuck; §3.2 says so as a theorem.
    (N2) A shift whose left operand has a `wrapping` type. `M1` suppresses the overflow
         there, so the shift-width booking above does not apply -- and a count at or above
         the width is undefined in C even on an unsigned operand. A `wrapping` FIELD is
         already refused by the emitter (`no-shape-for-field`); a `wrapping` LOCAL is not,
         and that hole is older than the shifts: `+` on one stands here unbooked too.
    (N3) That a DECLARED range is a hypothesis. `u32` says `0 ≤ x` and `u16 in 1 .. Q` says
         `x ≠ 0`, and neither reaches this model: the emitter writes shapes (`isInt`), not
         ranges. So a proof through a mask or a division must get the guard from the body
         or from a `requires` -- which is where `raeumen`-style bodies get it, and where
         `falte(s : u32)` does not.
-/

import Lean

namespace Gabbro.Body

/-! ## 1. Values

    Four forms, and the list is closed. `option index into T` is `absent`/`present` -- **not
    `Option Int`**, because a value has to be comparable with every other value, and a sum
    type over `Int` would be two levels.
-/

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
  deriving DecidableEq, Repr

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
  simp [store]

@[simp] theorem store_elsewhere (σ : World) (p q : Place) (v : Value) (h : q ≠ p) :
    store σ p v q = σ q := by
  simp [store, h]

@[simp] theorem bindLocal_here (β : Binding) (n : String) (v : Value) : bindLocal β n v n = v := by
  simp [bindLocal]

@[simp] theorem bindLocal_elsewhere (β : Binding) (n m : String) (v : Value) (h : m ≠ n) :
    bindLocal β n v m = β m := by
  simp [bindLocal, h]

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
  deriving DecidableEq, Repr

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
  cases p <;> simp [Shape.payloadOk]
@[simp] theorem Shape.payloadOk_some_none_iff (p : Option Int) :
    Shape.payloadOk (some none) p = true ↔ ∃ n, p = some n := by
  cases p <;> simp [Shape.payloadOk]
@[simp] theorem Shape.payloadOk_range_iff (lo hi : Int) (p : Option Int) :
    Shape.payloadOk (some (some (lo, hi))) p = true ↔ ∃ n, p = some n ∧ lo ≤ n ∧ n ≤ hi := by
  cases p <;> simp [Shape.payloadOk]
@[simp] theorem Shape.payloadOk_none_none : Shape.payloadOk none none = true := rfl
@[simp] theorem Shape.payloadOk_none_some (n : Int) : Shape.payloadOk none (some n) = false := rfl
@[simp] theorem Shape.payloadOk_some_none_none : Shape.payloadOk (some none) none = false := rfl
@[simp] theorem Shape.payloadOk_some_none_some (n : Int) : Shape.payloadOk (some none) (some n) = true := rfl
@[simp] theorem Shape.payloadOk_range_none (lo hi : Int) : Shape.payloadOk (some (some (lo, hi))) none = false := rfl
@[simp] theorem Shape.payloadOk_range_some (lo hi n : Int) :
    Shape.payloadOk (some (some (lo, hi))) (some n) = decide (lo ≤ n ∧ n ≤ hi) := rfl

def Value.hasShape : Value → Shape → Bool
  | .int _, .int => true
  | .int n, .intIn lo hi => decide (lo ≤ n ∧ n ≤ hi)
  | .bool _, .bool => true
  | .absent, .opt => true
  | .present _, .opt => true
  | .tagged t p, .sum cs => Shape.caseOk cs t p
  | _, _ => false

/-! **`hasShape` on a constructor computes, and stays folded on a variable** -- these are
    the equations the simp set uses instead of unfolding the definition, so that a
    `hasShape v sh = true` about an unknown `v` keeps the form `gabbro_open` turns into a
    witness. -/
@[simp] theorem Value.hasShape_int_int (n : Int) : Value.hasShape (.int n) .int = true := rfl
@[simp] theorem Value.hasShape_int_bool (n : Int) : Value.hasShape (.int n) .bool = false := rfl
@[simp] theorem Value.hasShape_int_opt (n : Int) : Value.hasShape (.int n) .opt = false := rfl
@[simp] theorem Value.hasShape_int_sum (cs : List (String × Option (Option (Int × Int)))) (n : Int) : Value.hasShape (.int n) (.sum cs) = false := rfl
@[simp] theorem Value.hasShape_int_intIn (n lo hi : Int) : Value.hasShape (.int n) (.intIn lo hi) = decide (lo ≤ n ∧ n ≤ hi) := rfl
@[simp] theorem Value.hasShape_bool_intIn (t : Bool) (lo hi : Int) : Value.hasShape (.bool t) (.intIn lo hi) = false := rfl
@[simp] theorem Value.hasShape_absent_intIn (lo hi : Int) : Value.hasShape (.absent) (.intIn lo hi) = false := rfl
@[simp] theorem Value.hasShape_present_intIn (n lo hi : Int) : Value.hasShape (.present n) (.intIn lo hi) = false := rfl
@[simp] theorem Value.hasShape_reason_intIn (r : String) (lo hi : Int) : Value.hasShape (.reason r) (.intIn lo hi) = false := rfl
@[simp] theorem Value.hasShape_tagged_intIn (t : String) (p : Option Int) (lo hi : Int) : Value.hasShape (.tagged t p) (.intIn lo hi) = false := rfl
@[simp] theorem Value.hasShape_bool_int (t : Bool) : Value.hasShape (.bool t) .int = false := rfl
@[simp] theorem Value.hasShape_bool_bool (t : Bool) : Value.hasShape (.bool t) .bool = true := rfl
@[simp] theorem Value.hasShape_bool_opt (t : Bool) : Value.hasShape (.bool t) .opt = false := rfl
@[simp] theorem Value.hasShape_bool_sum (cs : List (String × Option (Option (Int × Int)))) (t : Bool) : Value.hasShape (.bool t) (.sum cs) = false := rfl
@[simp] theorem Value.hasShape_absent_int : Value.hasShape (.absent) .int = false := rfl
@[simp] theorem Value.hasShape_absent_bool : Value.hasShape (.absent) .bool = false := rfl
@[simp] theorem Value.hasShape_absent_opt : Value.hasShape (.absent) .opt = true := rfl
@[simp] theorem Value.hasShape_absent_sum (cs : List (String × Option (Option (Int × Int)))) : Value.hasShape (.absent) (.sum cs) = false := rfl
@[simp] theorem Value.hasShape_present_int (n : Int) : Value.hasShape (.present n) .int = false := rfl
@[simp] theorem Value.hasShape_present_bool (n : Int) : Value.hasShape (.present n) .bool = false := rfl
@[simp] theorem Value.hasShape_present_opt (n : Int) : Value.hasShape (.present n) .opt = true := rfl
@[simp] theorem Value.hasShape_present_sum (cs : List (String × Option (Option (Int × Int)))) (n : Int) : Value.hasShape (.present n) (.sum cs) = false := rfl
@[simp] theorem Value.hasShape_reason_int (r : String) : Value.hasShape (.reason r) .int = false := rfl
@[simp] theorem Value.hasShape_reason_bool (r : String) : Value.hasShape (.reason r) .bool = false := rfl
@[simp] theorem Value.hasShape_reason_opt (r : String) : Value.hasShape (.reason r) .opt = false := rfl
@[simp] theorem Value.hasShape_reason_sum (cs : List (String × Option (Option (Int × Int)))) (r : String) : Value.hasShape (.reason r) (.sum cs) = false := rfl
@[simp] theorem Value.hasShape_tagged_int (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .int = false := rfl
@[simp] theorem Value.hasShape_tagged_sum (t : String) (p : Option Int) (cs : List (String × Option (Option (Int × Int)))) :
    Value.hasShape (.tagged t p) (.sum cs) = Shape.caseOk cs t p := rfl
@[simp] theorem Value.hasShape_tagged_bool (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .bool = false := rfl
@[simp] theorem Value.hasShape_tagged_opt (t : String) (p : Option Int) : Value.hasShape (.tagged t p) .opt = false := rfl

/-! **A shape, as a witness.** `v.hasShape .int = true` says WHAT `v` is; these turn that
    into the equation a proof rewrites with. -/
theorem Value.hasShape_int_true (v : Value) (h : v.hasShape .int = true) : ∃ n, v = .int n := by
  cases v <;> simp [Value.hasShape] at h ⊢
theorem Value.hasShape_bool_true (v : Value) (h : v.hasShape .bool = true) : ∃ b, v = .bool b := by
  cases v <;> simp [Value.hasShape] at h ⊢
theorem Value.hasShape_intIn_true (v : Value) (lo hi : Int) (h : v.hasShape (.intIn lo hi) = true) :
    ∃ n, v = .int n ∧ lo ≤ n ∧ n ≤ hi := by
  cases v <;> simp [Value.hasShape] at h ⊢
  exact h
theorem Value.hasShape_sum_true (v : Value) (cs : List (String × Option (Option (Int × Int)))) (h : v.hasShape (.sum cs) = true) :
    ∃ t p, v = .tagged t p ∧ Shape.caseOk cs t p = true := by
  cases v <;> simp [Value.hasShape] at h ⊢
  exact ⟨_, _, ⟨rfl, rfl⟩, h⟩

/-- **`caseOk`, computed** -- for a literal case list, `simp` decides the names and leaves
    the payload: `p.isSome = true` or `p.isSome = false`. -/
@[simp] theorem Shape.caseOk_cons (c : String × Option (Option (Int × Int))) (cs : List (String × Option (Option (Int × Int)))) (t : String) (p : Option Int) :
    Shape.caseOk (c :: cs) t p = ((c.1 == t && Shape.payloadOk c.2 p) || Shape.caseOk cs t p) := by
  simp [Shape.caseOk, List.any_cons]
@[simp] theorem Shape.caseOk_nil (t : String) (p : Option Int) : Shape.caseOk [] t p = false := rfl
@[simp] theorem isSome_true_iff (o : Option Int) : o.isSome = true ↔ ∃ n, o = some n := by
  cases o <;> simp
@[simp] theorem isSome_false_iff (o : Option Int) : o.isSome = false ↔ o = none := by
  cases o <;> simp
theorem Value.hasShape_opt_true (v : Value) (h : v.hasShape .opt = true) :
    v = .absent ∨ ∃ n, v = .present n := by
  cases v <;> simp [Value.hasShape] at h ⊢

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

@[simp] theorem andBool_some (x y : Bool) : andBool (some (.bool x)) (some (.bool y)) = some (.bool (x && y)) := rfl
@[simp] theorem orBool_some (x y : Bool) : orBool (some (.bool x)) (some (.bool y)) = some (.bool (x || y)) := rfl
@[simp] theorem andBool_none_left (y : Option Value) : andBool none y = none := by cases y <;> rfl
@[simp] theorem andBool_none_right (x : Option Value) : andBool x none = none := by
  cases x with
  | none => rfl
  | some v => cases v <;> rfl
@[simp] theorem orBool_none_left (y : Option Value) : orBool none y = none := by cases y <;> rfl
@[simp] theorem orBool_none_right (x : Option Value) : orBool x none = none := by
  cases x with
  | none => rfl
  | some v => cases v <;> rfl

/-- **A conjunction that evaluates to true is two that do.** -/
@[simp] theorem andBool_true_iff (x y : Option Value) :
    andBool x y = some (.bool true) ↔ x = some (.bool true) ∧ y = some (.bool true) := by
  constructor
  · intro h
    cases x with
    | none => simp [andBool] at h
    | some v =>
      cases y with
      | none => simp [andBool] at h
      | some w =>
        cases v <;> cases w <;> simp [andBool] at h
        rename_i a b
        simp [h.1, h.2]
  · intro ⟨hx, hy⟩
    simp [hx, hy]

/-- **A disjunction that evaluates to true**: both halves are truth values, and one is true. -/
theorem orBool_true_iff (x y : Option Value) :
    orBool x y = some (.bool true)
      ↔ ∃ a b, x = some (.bool a) ∧ y = some (.bool b) ∧ (a || b) = true := by
  constructor
  · intro h
    cases x with
    | none => simp [orBool] at h
    | some v =>
      cases y with
      | none => simp [orBool] at h
      | some w =>
        cases v <;> cases w <;> simp [orBool] at h
        rename_i a b
        exact ⟨a, b, rfl, rfl, by simpa using h⟩
  · intro ⟨a, b, hx, hy, hab⟩
    simp [hx, hy, hab]

def eval (s : State) : Expr → Option Value
  | .lit v => some v
  | .name n => some (s.local' n)
  | .global g => some (s.world (.global g))
  | .place c i f =>
      match eval s i with
      | some (.int k) => some (s.world (.slot c k f))
      | _ => none
  | .un op a =>
      match eval s a with
      | some v => unop op v
      | none => none
  | .bin .and a b => andBool (eval s a) (eval s b)
  | .bin .or a b => orBool (eval s a) (eval s b)
  | .bin op a b =>
      match eval s a, eval s b with
      | some x, some y => binop op x y
      | _, _ => none
  | .someOf a =>
      match eval s a with
      | some (.int n) => some (.present n)
      | _ => none
  | .fieldOf c f => some (s.world (.field c f))
  | .forallSlots v n b =>
      allBelow (fun k => eval { s with local' := bindLocal s.local' v (.int k) } b) n.toNat
  | .existsSlots v n b =>
      anyBelow (fun k => eval { s with local' := bindLocal s.local' v (.int k) } b) n.toNat
  | .reaches c a z via n =>
      match eval s a, eval s z with
      | some (.int k), some (.int t) => chase s.world c via t k n.toNat
      | _, _ => none
  | .chainFrom c h x via n =>
      match eval s h, eval s x with
      | some .absent, some (.int _) => some (.bool false)
      | some (.present m), some (.int t) => chase s.world c via t m n.toNat
      | _, _ => none
  | .hasShape n sh => some (.bool ((s.local' n).hasShape sh))
  | .wrapTo b sg a =>
      match eval s a with
      | some (.int n) => some (.int (wrap b sg n))
      | _ => none
  | .tagOf t none => some (.tagged t none)
  | .tagOf t (some e) =>
      match eval s e with
      | some (.int n) => some (.tagged t (some n))
      | _ => none

/-! ### 3.1 The WELL-FORMEDNESS of a place

    The world is an unconstrained map: nothing about `Place → Value` says that a `bool` slot
    field carries a truth value. **That is deliberate** -- a model that builds the shape into
    the type can no longer NAME the premise, and an unnamed premise is the most expensive
    kind.

    The emitter writes per unit which shape a field has, **and it reads that from the
    DECLARATION** -- not from how the body uses the field. *A premise guessed from the use
    makes the goal easier, not harder; it is exactly the quiet weakening this channel is
    built against.*
-/

def isInt (v : Value) : Prop := ∃ n, v = .int n
def isBool (v : Value) : Prop := ∃ t, v = .bool t
def isOption (v : Value) : Prop := v = .absent ∨ ∃ n, v = .present n
def isTagged (v : Value) : Prop := ∃ t p, v = .tagged t p

/-! ### 3.2 The division and the bits, held against C

    **These theorems are the reason the arms above may be believed.** Each one names a case
    where the convenient reading and the machine's reading come apart, and pins the model to
    the machine's. *A model whose choice is only stated in a comment is a choice nobody can
    fail.*
-/

/-- **C truncates toward zero; Lean's own `/` on `Int` does not.** Both halves stand in one
    statement on purpose: the second is what a later "simplification" of the model would
    silently install, and this theorem is where that fails first. -/
theorem div_truncates_where_lean_rounds_down :
    binop .div (.int (-7)) (.int 2) = some (.int (-3)) ∧ ((-7 : Int) / 2) = -4 := by
  decide

/-- **`%` carries the sign of the DIVIDEND**, as C says and as `Int.tmod` does. Lean's `%`
    is non-negative here, which is the same disagreement one operator further on. -/
theorem rem_follows_the_dividend :
    binop .rem (.int (-7)) (.int 2) = some (.int (-1))
    ∧ binop .rem (.int 7) (.int (-2)) = some (.int 1)
    ∧ ((-7 : Int) % 2) = 1 := by
  decide

/-- **A zero denominator gets the model stuck, in both operators.** Lean would answer `0`
    and `a`; C answers nothing. -/
theorem division_by_zero_is_stuck (a : Int) :
    binop .div (.int a) (.int 0) = none ∧ binop .rem (.int a) (.int 0) = none := by
  simp [binop]

/-- **A negative operand gets a bit operation stuck** -- all five of them, on either side.
    This is the refusal the model makes instead of guessing a width. -/
theorem a_negative_operand_stops_the_bits (a : Int) (h : a < 0) :
    binop .band (.int a) (.int 1) = none ∧ binop .band (.int 1) (.int a) = none
    ∧ binop .bor (.int a) (.int 1) = none ∧ binop .bxor (.int a) (.int 1) = none
    ∧ binop .shl (.int a) (.int 1) = none ∧ binop .shr (.int a) (.int 1) = none
    ∧ binop .shl (.int 1) (.int a) = none ∧ binop .shr (.int 1) (.int a) = none := by
  simp [binop, bits, Int.not_le.mpr h]

/-- **The shifts are a multiplication and a division**, under the guard and under the `M104`
    booking the arm names. Stated in general and not on an example, because it is the claim
    the booking rests on. -/
theorem a_shift_is_arithmetic (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    binop .shl (.int a) (.int b) = some (.int (a * 2 ^ b.toNat))
    ∧ binop .shr (.int a) (.int b) = some (.int (a.tdiv (2 ^ b.toNat))) := by
  simp [binop, ha, hb]

/-- **Where a mask answers at all, it answers with a non-negative number.** That is the
    half of the width-independence claim this file can state on its own; that the result
    also fits the DECLARED range is `M104`'s half, and `typen::bitweise` computes it. -/
theorem a_mask_stays_non_negative (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ n : Nat, binop .band (.int a) (.int b) = some (.int (n : Int)) := by
  exact ⟨a.toNat &&& b.toNat, by simp [binop, bits, ha, hb]⟩

/-! ### 3.3 The quantifier and the chain, read as propositions

    **These are the theorems that let a proof leave the evaluator.** `forallSlots` is an
    `Expr` so that a callee may DEMAND it (§4, `step`); a person proving it wants the
    `∀ k < n` on the left of the turnstile, and this is the bridge.
-/

@[simp] theorem allBelow_zero (f : Nat → Option Value) : allBelow f 0 = some (.bool true) := by
  rw [allBelow_eq]; rfl

theorem allBelow_succ (f : Nat → Option Value) (n : Nat) :
    allBelow f (n + 1) =
      match allBelow f n, f n with
      | some (.bool a), some (.bool b) => some (.bool (a && b))
      | _, _ => none := by
  rw [allBelow_eq]; rfl

@[simp] theorem anyBelow_zero (f : Nat → Option Value) : anyBelow f 0 = some (.bool false) := by
  rw [anyBelow_eq]; rfl

theorem anyBelow_succ (f : Nat → Option Value) (n : Nat) :
    anyBelow f (n + 1) =
      match anyBelow f n, f n with
      | some (.bool a), some (.bool b) => some (.bool (a || b))
      | _, _ => none := by
  rw [anyBelow_eq]; rfl

theorem chase_zero (σ : World) (c via : String) (to k : Int) :
    chase σ c via to k 0 = some (.bool (decide (k = to))) := by
  rw [chase_eq]; rfl

theorem chase_succ (σ : World) (c via : String) (to k : Int) (n : Nat) :
    chase σ c via to k (n + 1) =
      if k = to then some (.bool true)
      else
        match σ (.slot c k via) with
        | .present m => chase σ c via to m n
        | .absent => some (.bool false)
        | _ => none := by
  rw [chase_eq]; rfl

/-- **A chain reaches where it starts** -- with any fuel. The reflexive half of `reaches`,
    computed: `x reaches x` is `true` without a step, and a `simp` set that carries this
    closes the case `src = dst` of an invariant instead of leaving it to the person. -/
@[simp] theorem chase_refl (σ : World) (c via : String) (to : Int) (n : Nat) :
    chase σ c via to to n = some (.bool true) := by
  cases n with
  | zero => rw [chase_zero]; simp
  | succ n => rw [chase_succ]; simp

/-- **A chain does not see a store beside it.** A store into another field, another
    carrier, a global or a record field leaves every `via`-chain as it was -- the frame of
    `reaches`, so that an invariant over a chain survives the stores a body makes next to
    it without the person walking the chain (2026-09-08, `55-kindkette`). -/
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

@[simp] theorem chase_store_field (σ : World) (c c' via f' : String) (k' : Int) (v : Value)
    (h : f' ≠ via) (to' k : Int) (n : Nat) :
    chase (store σ (.slot c' k' f') v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun _ e => by cases e; exact h rfl) k n

@[simp] theorem chase_store_carrier (σ : World) (c c' via f' : String) (k' : Int) (v : Value)
    (h : c' ≠ c) (to' k : Int) (n : Nat) :
    chase (store σ (.slot c' k' f') v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun _ e => by cases e; exact h rfl) k n

@[simp] theorem chase_store_global (σ : World) (c via g : String) (v : Value) (to' k : Int) (n : Nat) :
    chase (store σ (.global g) v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun _ e => by cases e) k n

@[simp] theorem chase_store_fieldPlace (σ : World) (c via r f : String) (v : Value) (to' k : Int) (n : Nat) :
    chase (store σ (.field r f) v) c via to' k n = chase σ c via to' k n :=
  chase_store_ne σ c via to' _ v (fun _ e => by cases e) k n

theorem allBelow_true_iff (f : Nat → Option Value) (n : Nat) :
    allBelow f n = some (.bool true) ↔ ∀ k, k < n → f k = some (.bool true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · intro h k hk
      rw [allBelow_succ] at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Value.bool.injEq, Bool.and_eq_true] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · exact ih.mp (by rw [ha, h.1]) k hlt
        · subst heq; rw [hb, h.2]
      · exact absurd h (by simp)
    · intro h
      have hn : allBelow f n = some (.bool true) := ih.mpr (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hf : f n = some (.bool true) := h n (Nat.lt_succ_self n)
      rw [allBelow_succ, hn, hf]
      rfl

theorem anyBelow_true_of (f : Nat → Option Value) (n k : Nat) (hk : k < n)
    (hall : ∀ j, j < n → ∃ b, f j = some (.bool b)) (h : f k = some (.bool true)) :
    anyBelow f n = some (.bool true) := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    obtain ⟨b, hb⟩ := hall n (Nat.lt_succ_self n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · have := ih hlt (fun j hj => hall j (Nat.lt_succ_of_lt hj))
      rw [anyBelow_succ, this, hb]
      rfl
    · subst heq
      rw [h] at hb
      have hb' : b = true := by simpa using hb.symm
      subst hb'
      have : ∃ a, anyBelow f k = some (.bool a) := by
        clear ih h hb hk
        induction k with
        | zero => exact ⟨false, by simp⟩
        | succ m ihm =>
          obtain ⟨a, ha⟩ := ihm (fun j hj => hall j (Nat.lt_succ_of_lt hj))
          obtain ⟨c, hc⟩ := hall m (Nat.lt_succ_of_lt (Nat.lt_succ_self m))
          exact ⟨a || c, by rw [anyBelow_succ, ha, hc]⟩
      obtain ⟨a, ha⟩ := this
      rw [anyBelow_succ, ha, h]
      simp

/-- The chain as a relation -- `hier`/`hoeher`, the same two rules `Table_Ops_Erhaltung.thy`
    calls `ueber`. -/
inductive Reaches (σ : World) (c via : String) : Int → Int → Prop
  | hier (k : Int) : Reaches σ c via k k
  | hoeher (k m n : Int) (h : σ (.slot c k via) = .present m) (r : Reaches σ c via m n) :
      Reaches σ c via k n

/-- **`chase` answers `true` only along a real chain.** -/
theorem reaches_of_chase (σ : World) (c via : String) (to : Int) :
    ∀ (n : Nat) (k : Int), chase σ c via to k n = some (.bool true) → Reaches σ c via k to := by
  intro n
  induction n with
  | zero =>
    intro k h
    rw [chase_zero] at h
    simp only [Option.some.injEq, Value.bool.injEq, decide_eq_true_eq] at h
    subst h; exact .hier k
  | succ n ih =>
    intro k h
    rw [chase_succ] at h
    split at h
    · rename_i hk; subst hk; exact .hier k
    · split at h
      · rename_i m hm; exact .hoeher k m to hm (ih m h)
      · simp at h
      · simp at h

/-- **And a real chain is found with enough fuel** -- one unit per edge. -/
theorem chase_of_reaches (σ : World) (c via : String) (k to : Int)
    (r : Reaches σ c via k to) : ∃ n, chase σ c via to k n = some (.bool true) := by
  induction r with
  | hier k => exact ⟨0, by rw [chase_zero]; simp⟩
  | hoeher k m n h _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [chase_succ]
    split
    · rfl
    · simp [h, hf]

/-! ### 3.4 Opening a precondition

    A precondition is ONE expression -- shapes, `requires`, invariants, conjoined right to
    left by the emitter -- and a proof wants its conjuncts as separate facts, the shapes as
    witnesses. These four lemmas are what the generated `obtain` lines apply; the emitter
    knows the position of every conjunct and writes the path.
-/

theorem and_left (s : State) (a b : Expr) (h : eval s (.bin .and a b) = some (.bool true)) :
    eval s a = some (.bool true) := by
  simp only [eval] at h
  exact (andBool_true_iff _ _).mp h |>.1

theorem and_right (s : State) (a b : Expr) (h : eval s (.bin .and a b) = some (.bool true)) :
    eval s b = some (.bool true) := by
  simp only [eval] at h
  exact (andBool_true_iff _ _).mp h |>.2

/-- **A conjunction that evaluates to true is two that do** -- as a rewrite, for the
    hypotheses: an instantiated invariant is one `eval … (.bin .and …) = some (.bool true)`,
    and `simp` splits it with this BEFORE it unfolds `eval` (used as `↓eval_and_true_iff`). -/
theorem eval_and_true_iff (s : State) (a b : Expr) :
    eval s (.bin .and a b) = some (.bool true)
      ↔ eval s a = some (.bool true) ∧ eval s b = some (.bool true) := by
  simp only [eval, andBool_true_iff]

/-- **A shape test that evaluates to true is the shape** -- the form `gabbro_open` turns
    into a witness. -/
theorem eval_hasShape_true_iff (s : State) (n : String) (sh : Shape) :
    eval s (.hasShape n sh) = some (.bool true) ↔ (s.local' n).hasShape sh = true := by
  simp [eval]

theorem shape_int (s : State) (n : String) (h : eval s (.hasShape n .int) = some (.bool true)) :
    ∃ k, s.local' n = .int k := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp [hv, Value.hasShape] at h ⊢

/-- A local of a ranged type: its witness and its bounds. -/
theorem shape_intIn (s : State) (n : String) (lo hi : Int)
    (h : eval s (.hasShape n (.intIn lo hi)) = some (.bool true)) :
    ∃ k, s.local' n = .int k ∧ lo ≤ k ∧ k ≤ hi := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp [hv, Value.hasShape] at h ⊢
  exact h

theorem shape_bool (s : State) (n : String) (h : eval s (.hasShape n .bool) = some (.bool true)) :
    ∃ b, s.local' n = .bool b := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp [hv, Value.hasShape] at h ⊢

theorem shape_opt (s : State) (n : String) (h : eval s (.hasShape n .opt) = some (.bool true)) :
    s.local' n = .absent ∨ ∃ k, s.local' n = .present k := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp [hv, Value.hasShape] at h ⊢

theorem shape_sum (s : State) (n : String) (cs : List (String × Option (Option (Int × Int))))
    (h : eval s (.hasShape n (.sum cs)) = some (.bool true)) :
    ∃ t p, s.local' n = .tagged t p ∧ Shape.caseOk cs t p = true := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp [hv, Value.hasShape] at h ⊢
  exact ⟨_, _, ⟨rfl, rfl⟩, h⟩

/-- **A ranged integer parameter** -- `n : u32 in lo .. hi` -- is an integer within its
    bounds. The emitter writes the shape conjunct of such a parameter in exactly this form,
    and the bounds are what the checker holds at every call site. -/
theorem shape_int_in (s : State) (n : String) (lo hi : Int)
    (h : eval s (.bin .and (.hasShape n .int)
          (.bin .and (.bin .le (.lit (.int lo)) (.name n)) (.bin .le (.name n) (.lit (.int hi)))))
        = some (.bool true)) :
    ∃ k, s.local' n = .int k ∧ lo ≤ k ∧ k ≤ hi := by
  have h1 := and_left _ _ _ h
  have h2 := and_right _ _ _ h
  obtain ⟨k, hk⟩ := shape_int s n h1
  have hlo := and_left _ _ _ h2
  have hhi := and_right _ _ _ h2
  simp [eval, binop, hk] at hlo hhi
  exact ⟨k, hk, hlo, hhi⟩

/-! ## 4. Statements -- the SEQUENTIAL CORE

    Seven kinds of `StmtArt`, and `messung/` measures that they carry **12 of the 17** open
    body obligations: `Let`, `LetSonst`, assignment, `Wenn`, `Match`, `Return`, `Ruf`. What
    does not stand here the emitter refuses by name.

    `Ruf` is absent on purpose and is not an omission: a call is to be taken COMPOSITIONALLY
    over the callee's contract, never over its body. As long as the emitter has no gate for
    that, it refuses -- **a refused obligation costs a number; an inlined body costs the
    number's meaning.**
-/

inductive Stmt where
  /-- `carrier.slots[index].field = value;` -/
  | assign (carrier : String) (index : Expr) (field : String) (value : Expr)
  /-- `carrier.field = value;` at a record or a `format`. -/
  | assignField (carrier : String) (field : String) (value : Expr)
  /-- `name = value;` at a `static`. -/
  | assignGlobal (name : String) (value : Expr)
  /-- `let name = value;` -/
  | bindName (name : String) (value : Expr)
  | ite (cond : Expr) (thenB elseB : List Stmt)
  /-- `match e { Some(b) => …, None => … }` -- the only `match` form of the core. -/
  | onOption (subject : Expr) (binder : String) (onPresent onAbsent : List Stmt)
  /-- `f(a, b);` -- **a call, and it is taken over the callee's CONTRACT.**

      The callee is named, not inlined. What it does is looked up in an ENVIRONMENT that
      the theorem quantifies over, and the caller's theorem then carries the callee's
      contract as a HYPOTHESIS. *Nothing about the callee is assumed here* -- and that is
      the difference between compositional reasoning and an axiom about foreign code, which
      `refinement.rs` refuses for the reason that an axiom proves everything after it. -/
  | call (callee : String) (params : List String) (args : List Expr) (pre : Expr)
  /-- `let n = f(a, b);` -- **a call whose RESULT is bound.** The commonest call shape in the
      corpus, and it stays a STATEMENT: a callee may write, so an expression that contained
      it would no longer be pure and `eval` would have to carry the environment. -/
  | bindCall (name : String) (callee : String) (params : List String) (args : List Expr)
      (pre : Expr)
  /-- `let name = f(a, b) else (err) { … };` -- **the error propagation**: a callee that
      answers with a `reason` does not fill the binding; the `else` block runs with the
      reason bound to `err`, and ends (`M1` demands it). -/
  | bindCallElse (name : String) (callee : String) (params : List String) (args : List Expr)
      (pre : Expr) (err : String) (onErr : List Stmt)
  /-- `match e { Case => …, … }` over a `reason` -- the arm is picked by the case's name;
      no arm for the reason met is stuck (`M123` demands the enumeration be closed). -/
  | onReason (subject : Expr) (arms : List (String × List Stmt))
  /-- `match e { Case(b) => …, Case2 => …, … }` over a `tagged` value -- the arm by the
      case's name, the payload bound to the binder where the arm names one. `D005` demands
      the match be exhaustive, so a case no arm names is stuck, never silent. -/
  | onTag (subject : Expr) (arms : List (String × Option String × List Stmt))
  /-- `return f(a, b);` -- a call whose result is returned straight on. -/
  | retCall (callee : String) (params : List String) (args : List Expr) (pre : Expr)
  /-- `traverse … invariant P { … }` -- **a loop is an anonymous routine.**

      Its meaning is looked up in the same `Env` a call uses, under an id of its own. *That
      is not a shortcut: it is what a loop IS to a prover* -- something that runs an unknown
      number of times and leaves a state, and the only thing anyone knows about it is what
      the invariant says.

      **The invariant is DATA and not decoration.** The theorem over a body that loops carries
      the loop rule as a hypothesis --

          \forall t, eval t inv = some (.bool true)
                 \to eval (\rho id t).1 inv = some (.bool true)

      -- and that hypothesis is discharged by a separate theorem over `body`. The body is
      carried too, so that theorem has something to talk about. -/
  | loop (id : String) (inv : Expr) (body : List Stmt)
  /-- `locks S { … }` -- **a critical section, and it costs no memory model.**

      Its meaning is the body's. That looks naive read alone and is not: the whole model is
      SEQUENTIAL, and what makes a sequential reading sound is exactly that the lock is held
      -- `H005`/`H006`/`H012`/`H016` carry it, and the header books it as `races`. *A lock
      that added state here would be the second register over a statement a pass already
      discharges.*

      **The lock's NAME stays in the datum** all the same. Inlining the body would erase the
      critical section from the record, and a reader could no longer see where one was. -/
  | locked (lock : String) (body : List Stmt)
  /-- `breaking I { … }` -- **the SUSPENSION of a table invariant, and it is not an exit.**

      Its meaning is the body's, and the ground is the same as at a lock: what `breaking`
      changes is not which statements run but which DUTY holds in between. The transition is
      the body's; the duty stands beside it as an obligation of its own -- `maintains I`
      appears in the register as its own line and is refused there (`table-invariant`,
      quantified over every slot).

      **The names travel in the datum, and that is the load-bearing half.** This reading is
      sound exactly as far as this channel cannot state a table invariant, and it cannot.
      *Should it ever get a quantifier, this name is where an invariant channel has to read
      off where the suspension lay* -- a record that inlined the body would have erased it.

      It stood refused as `non-local-exit` until 2026-08-28, in one arm with `leave` and
      `next`, under the sentence *"a non-local exit out of a named loop"*. It is neither
      non-local nor an exit: four obligations of the register paid for one word covering
      three things (`messung/AUSSETZUNG.md`). -/
  | breaking (invariants : List String) (body : List Stmt)
  /-- `A = v publishes { p, q };` -- **a release store, and it costs no memory model either.**

      The store itself is a store. What makes the PAYLOAD visible to the reader is
      `release_stellt_sichtbarkeit_her` -- an assumption of the axiom layer since
      `beispiele/06-annahmen.gab`, `unfalsifiable` with its reason written out, and rebooked
      there by `K100.2`. *In a single world the visibility is automatic; the assumption is
      what licenses reading it that way.*

      **The payload travels in the datum all the same.** It is the surface that rests on the
      assumption rather than on the transition -- and a record that dropped it would hide
      exactly which places those are. -/
  | publish (atomic : String) (value : Expr) (payload : List String)
  /-- `let n = A awaits { p, q };` -- the other half of the pairing. -/
  | awaitLoad (name : String) (atomic : String) (payload : List String)
  /-- `let n = A exchange …;` -- an atomic swap: the old value is bound, the new one stored. -/
  | exchangeWith (name : String) (atomic : String) (value : Expr)
  | ret (value : Option Expr)
  /-- `next m;` -- **the end of one pass of the innermost loop** (2026-09-07): the
      iteration ends here, in this state, the invariant has to hold in it, and the loop goes
      on. *A `next` of an OUTER loop is refused by the emitter* -- it would have to carry
      the mark through a `.loop` step that does not run the body. -/
  | exit
  /-- `leave m;` -- **the end of the innermost loop**: the pass ends here, the invariant has
      to hold, and no pass follows (`iterate` stops). A `return` inside a loop is desugared
      to this by the emitter, with the value in a local. -/
  | leave
  deriving Repr

/-- **What every routine of the program does, as a map from name to state transformer.**

    **The pair is the state AND the result.** A callee can both write and return, and an
    environment that gave only the state would make `let x = f(a);` unstatable -- which is
    22 of the corpus's call sites.

    A theorem about a body that calls does not fix `Env`: it QUANTIFIES over it and assumes
    only what the callee's contract says. *An environment fixed by the emitter would be the
    emitter deciding what a callee does, and that is exactly the decision a proof is for.* -/
abbrev Env := String → State → State × Option Value

/-- The carrier a place belongs to -- what an `effects { writes X }` clause names. -/
def Place.carrier : Place → String
  | .slot c _ _ => c
  | .field c _ => c
  | .global n => n

/-! ### 4.1 What a theorem may ASSUME about a callee -- and nothing else

    Three hypotheses, each read off a DECLARATION by the emitter (2026-09-07), and together
    they are the whole of what "compositional over the contract" means here:

      `Contract ρ f pre post`   the callee's `ensures`, under its `requires`;
      `Frame ρ f writes`        the callee's `effects` list -- every place outside it survives
                                (`Passlogik.Wirkung.huelle_deckt` is what licenses reading
                                the DECLARED list as the transitive one);
      `LoopRule ρ id inv`       a loop preserves its `invariant` -- and the theorem that
                                discharges it is emitted beside the routine's.

    *None of them is an axiom.* Each is a hypothesis of the theorem that uses it, and each is
    discharged by another theorem of the same register -- the callee's `ensures` by the
    callee's duty, the loop rule by the loop's. **What remains assumed is what the plumbing
    carries** (the `effects` list is complete, `E008`/`E010`), exactly as before.
-/

/-! ### 4.0 The well-typed WORLD

    `Place → Value` is an unconstrained map; that a slot declared `u32` carries a number is
    hypothesis `U2`. Since 2026-09-07 the hypothesis has ONE form for the whole unit: a
    `Typing` -- the shape every declared place carries, written by the emitter out of the
    declarations -- and `WF Γ σ`, that the world respects it. **The two theorems below are
    what make it cost a person nothing**: a store of a value of the right shape keeps the
    world well-formed, and a read from a well-formed world yields a value of the declared
    shape. `gabbro_simp` carries both.
-/

abbrev Typing := Place → Option Shape

def WF (Γ : Typing) (σ : World) : Prop :=
  ∀ p sh, Γ p = some sh → (σ p).hasShape sh = true

theorem WF_store (Γ : Typing) (σ : World) (p : Place) (v : Value) (h : WF Γ σ)
    (hv : ∀ sh, Γ p = some sh → v.hasShape sh = true) : WF Γ (store σ p v) := by
  intro q sh hq
  simp only [store]
  split
  · rename_i hqp; subst hqp; exact hv sh hq
  · exact h q sh hq

theorem WF_int (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .int) :
    ∃ n, σ p = .int n := by
  have := h p .int hp
  cases hv : σ p <;> simp [hv, Value.hasShape] at this ⊢

theorem WF_intIn (Γ : Typing) (σ : World) (p : Place) (lo hi : Int) (h : WF Γ σ)
    (hp : Γ p = some (.intIn lo hi)) : ∃ n, σ p = .int n ∧ lo ≤ n ∧ n ≤ hi := by
  have := h p (.intIn lo hi) hp
  cases hv : σ p <;> simp [hv, Value.hasShape] at this ⊢
  exact this

theorem WF_bool (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .bool) :
    ∃ b, σ p = .bool b := by
  have := h p .bool hp
  cases hv : σ p <;> simp [hv, Value.hasShape] at this ⊢

theorem WF_opt (Γ : Typing) (σ : World) (p : Place) (h : WF Γ σ) (hp : Γ p = some .opt) :
    σ p = .absent ∨ ∃ n, σ p = .present n := by
  have := h p .opt hp
  cases hv : σ p <;> simp [hv, Value.hasShape] at this ⊢

theorem WF_sum (Γ : Typing) (σ : World) (p : Place) (cs : List (String × Option (Option (Int × Int)))) (h : WF Γ σ)
    (hp : Γ p = some (.sum cs)) :
    ∃ t q, σ p = .tagged t q ∧ Shape.caseOk cs t q = true := by
  have := h p (.sum cs) hp
  cases hv : σ p <;> simp [hv, Value.hasShape] at this ⊢
  exact ⟨_, _, ⟨rfl, rfl⟩, this⟩

/-- **The callee's contract.** `pre` is a `Prop` over the entry state: the world is
    well-formed, and the callee's precondition expression -- the SAME expression the call
    gets stuck on in `step` (the declared shapes of the parameters, the `requires`, and
    every invariant the callee maintains) -- holds. So a caller that gets past the call
    has, by that very fact, the second half of what the contract asks for; the first it
    carries along, because every post promises it back. `post` sees the entry state (for
    `old(...)`), the exit state and the result. -/
def Contract (ρ : Env) (f : String) (pre : State → Prop)
    (post : State → State → Option Value → Prop) : Prop :=
  ∀ t, pre t → post t (ρ f t).1 (ρ f t).2

/-- **The callee's frame.** A place whose carrier is not in the `writes` list is untouched. -/
def Frame (ρ : Env) (f : String) (writes : List String) : Prop :=
  ∀ t p, p.carrier ∉ writes → (ρ f t).1.world p = t.world p

/-- **The loop rule.** From a well-formed state that satisfies the invariant, the loop
    leaves a well-formed one that does. `wf` is the unit's well-formedness of the WORLD
    (`U2`); the shapes of the LOCALS in scope travel inside `inv`, as `hasShape` conjuncts
    the emitter adds -- a local whose shape the invariant did not carry would come out of
    the loop unconstrained. -/
def LoopRule (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) : Prop :=
  ∀ t, wf t → eval t inv = some (.bool true) →
    wf (ρ id t).1 ∧ eval (ρ id t).1 inv = some (.bool true)

/-- Bind a list of names to a list of values, left to right. -/
def bindAll : List String → List Value → Binding → Binding
  | [], _, β => β
  | _, [], β => β
  | n :: ns, v :: vs, β => bindAll ns vs (bindLocal β n v)

/-- Evaluate a list of expressions, or get stuck on the first that does. -/
def evalAll (s : State) : List Expr → Option (List Value)
  | [] => some []
  | e :: es =>
      match eval s e, evalAll s es with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- How a descent ends. **`stuck` is an outcome of its own and not a `running`** -- a model
    that conflated getting stuck with carrying on would prove things about a body that never
    runs. -/
inductive Outcome where
  | running (s : State)
  | returned (s : State) (v : Option Value)
  /-- The body of a loop ended through `next` -- a THIRD way to end, beside falling off
      the end and returning. `finalState` has it; `finalValue` has not. -/
  | exited (s : State)
  /-- The body of a loop ended through `leave`, and so did the loop. -/
  | left (s : State)
  | stuck

mutual

def step (ρ : Env) : Stmt → State → Outcome
  | .assign c i f e, s =>
      match eval s i, eval s e with
      | some (.int k), some v => .running { s with world := store s.world (.slot c k f) v }
      | _, _ => .stuck
  | .assignField c f e, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.field c f) v }
      | none => .stuck
  | .assignGlobal n e, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.global n) v }
      | none => .stuck
  | .bindName n e, s =>
      match eval s e with
      | some v => .running { s with local' := bindLocal s.local' n v }
      | none => .stuck
  | .ite c t e, s =>
      match eval s c with
      | some (.bool true) => exec ρ t s
      | some (.bool false) => exec ρ e s
      | _ => .stuck
  | .onOption g bn onP onA, s =>
      match eval s g with
      | some (.present k) => exec ρ onP { s with local' := bindLocal s.local' bn (.int k) }
      | some .absent => exec ρ onA s
      | _ => .stuck
  -- **A call changes the WORLD and nothing else.** Gabbro is call by value, so a callee
  -- cannot touch the caller's local names -- the caller's `local'` survives by construction
  -- rather than by a frame argument.
  -- **And a call whose PRECONDITION does not hold gets STUCK** (2026-09-07). `pre` is the
  -- callee's `requires`, evaluated in the callee's entry state -- so the strong goal
  -- (*the body runs to an end*) demands at every call site that the caller established
  -- it. That is the `V` duty of the register, carried by the theorem of the caller instead
  -- of by a goal of its own; `refinement.rs` could only write it for a literal or an
  -- untouched parameter, and this reads the state at the call.
  | .call f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) => .running { s with world := (ρ f t).1.world }
          | _ => .stuck
      | none => .stuck
  | .bindCall n f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) =>
            -- **The call's answer is read through the PROJECTIONS, never by matching the
            -- pair** (2026-09-07): `(ρ f t).1` and `(ρ f t).2` are what a contract talks
            -- about, and a `match ρ f t with | (t', v)` would stand in a proof until someone
            -- wrote the pair's eta by hand.
            match (ρ f t).2 with
            -- **A callee that returns nothing cannot fill a binding.** Getting stuck is
            -- the right answer: `M1` refuses the program, and a model that invented a
            -- value here would prove things about a program the checker rejects.
            | some v => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n v }
            | none => .stuck
          | _ => .stuck
      | none => .stuck
  | .bindCallElse n f ps as pre err onErr, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) =>
            match (ρ f t).2 with
            | some (.reason x) =>
                exec ρ onErr { world := (ρ f t).1.world, local' := bindLocal s.local' err (.reason x) }
            | some v => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n v }
            -- **A callee with an error channel and NO value** (`fn f() or R`) answers
            -- nothing on success: the binding gets no value (`absent`), and the body goes
            -- on -- what `let ok = f() else (e) { … }` means for such a callee.
            | none => .running { world := (ρ f t).1.world, local' := bindLocal s.local' n .absent }
          | _ => .stuck
      | none => .stuck
  | .onReason g arms, s =>
      match eval s g with
      | some (.reason x) => pickArm ρ arms x s
      | _ => .stuck
  | .onTag g arms, s =>
      match eval s g with
      | some (.tagged x p) => pickTag ρ arms x p s
      | _ => .stuck
  | .retCall f ps as pre, s =>
      match evalAll s as with
      | some vs =>
          let t := { world := s.world, local' := bindAll ps vs (fun _ => .absent) }
          match eval t pre with
          | some (.bool true) => .returned { s with world := (ρ f t).1.world } (ρ f t).2
          | _ => .stuck
      | none => .stuck
  -- **A loop leaves a state the environment gives**, exactly as a call does. What is known
  -- about that state is what the loop rule -- carried as a hypothesis, never as an axiom --
  -- says about the invariant.
  -- **And a loop entered with its invariant FALSE gets stuck** (2026-09-07). The loop
  -- rule -- carried as `LoopRule` -- says only that the invariant is PRESERVED; that it
  -- holds on entry is the caller's half, and a model that let a body walk into a loop
  -- without it would let the rule conclude from nothing.
  --
  -- **And the loop leaves the WHOLE state, locals included** (2026-09-07). Until today the
  -- arm kept the caller's locals and took only the world -- wrong for every body that
  -- counts in a local inside the loop (`n = n + 1;`), which Gabbro allows and the corpus
  -- does. A `let` of the body leaks into the binding as a name nothing after the loop may
  -- read (`namen.rs`), so leaking it is harmless.
  -- **A `match` and not an `if`**: an `if` on an equation over `Option Value` asks for a
  -- `Decidable` instance, and a proof that unfolds the step then lets the kernel EVALUATE
  -- the decision -- over a `forallSlots` of four thousand slots. Measured: *deep recursion
  -- detected*, on the first loop of `beispiele/01`.
  | .loop id inv _, s =>
      match eval s inv with
      | some (.bool true) => .running (ρ id s).1
      | _ => .stuck
  | .locked _ b, s => exec ρ b s
  -- **A suspension changes no state.** See the constructor: the transition is the body's,
  -- the duty stands beside it.
  | .breaking _ b, s => exec ρ b s
  | .publish a e _, s =>
      match eval s e with
      | some v => .running { s with world := store s.world (.global a) v }
      | none => .stuck
  | .awaitLoad n a _, s =>
      .running { s with local' := bindLocal s.local' n (s.world (.global a)) }
  | .exchangeWith n a e, s =>
      match eval s e with
      | some v =>
          .running { world := store s.world (.global a) v,
                     local' := bindLocal s.local' n (s.world (.global a)) }
      | none => .stuck
  | .ret none, s => .returned s none
  | .ret (some e), s =>
      match eval s e with
      | some v => .returned s (some v)
      | none => .stuck
  | .exit, s => .exited s
  | .leave, s => .left s

def exec (ρ : Env) : List Stmt → State → Outcome
  | [], s => .running s
  | a :: rest, s =>
      match step ρ a s with
      | .running s' => exec ρ rest s'
      | o => o

/-- The arm of a `match` over a `reason`, by the case's name. -/
def pickArm (ρ : Env) : List (String × List Stmt) → String → State → Outcome
  | [], _, _ => .stuck
  | (n, b) :: rest, x, s => if n = x then exec ρ b s else pickArm ρ rest x s

/-- The arm of a `match` over a `tagged` value: by the case's name, the payload bound. -/
def pickTag (ρ : Env) : List (String × Option String × List Stmt) → String → Option Int → State → Outcome
  | [], _, _, _ => .stuck
  | (n, bd, b) :: rest, x, p, s =>
      if n = x then
        match bd, p with
        | some v, some k => exec ρ b { s with local' := bindLocal s.local' v (.int k) }
        | none, _ => exec ρ b s
        | some _, none => .stuck
      else pickTag ρ rest x p s

end

/-- The state at the end -- **`return` and running off the end both end in a state**, and for
    a postcondition the two are the same thing: the state afterwards. Only `stuck` has none. -/
def finalState : Outcome → Option State
  | .running s => some s
  | .returned s _ => some s
  | .exited s => some s
  | .left s => some s
  | .stuck => none

/-- The result, where the body produced one. For an `ensures` that names `result`. -/
def finalValue : Outcome → Option Value
  | .returned _ (some v) => some v
  | _ => none

/-! ### 5.1 What ties the environment to the BODIES -- and who discharges what

    Everything above quantifies over `Env`. The two definitions below say what it means for
    an `Env` to BE the program, and the two theorems after them are the whole of the wiring:
    a duty proved over a body yields the callee's `Contract`; a loop's body preserving the
    invariant yields its `LoopRule`. **The emitter instantiates them per unit** -- no person
    writes an induction over the call graph or over the iterations.
-/

/-- **`ρ f` runs `body`.** Wherever the body ends, the environment's answer is that state and
    that value. Nothing is said where the body gets stuck -- a stuck body is what the duties
    exclude. -/
def Runs (ρ : Env) (f : String) (body : List Stmt) : Prop :=
  ∀ t s', finalState (exec ρ body t) = some s' →
    (ρ f t).1 = s' ∧ (ρ f t).2 = finalValue (exec ρ body t)

/-- One pass of a loop body per index in `ks`, the loop variable `v` bound to it -- and each
    pass ends by falling off, by `next` or by `leave`. A `retry`/`forever` has no variable;
    the emitter passes a name no body reads. -/
def iterate (ρ : Env) (body : List Stmt) (v : String) : List Int → State → Option State
  | [], t => some t
  | k :: ks, t =>
      match exec ρ body { t with local' := bindLocal t.local' v (.int k) } with
      | .running t' => iterate ρ body v ks t'
      | .exited t' => iterate ρ body v ks t'
      -- **`leave` ends the loop**: the remaining indices are not visited.
      | .left t' => some t'
      | _ => none

/-- **`ρ id` runs the loop `id`**: some sequence of passes of the body, and the state
    afterwards is the one the environment answers with. WHICH indices, and how many, is the
    domain's and the measure's business (`K008`/`K009`, `S005`), not this file's -- the rule
    below holds for every sequence. -/
def RunsLoop (ρ : Env) (id : String) (body : List Stmt) (v : String) : Prop :=
  ∀ t, ∃ ks t', iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **A duty over the body IS the contract** -- for any environment that runs the body. -/
theorem contract_of_duty (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (hr : Runs ρ f body)
    (hd : ∀ t, pre t →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post := by
  intro t ht
  obtain ⟨s', hs', hp⟩ := hd t ht
  obtain ⟨h1, h2⟩ := hr t s' hs'
  rw [h1, h2]
  exact hp

/-- `t'` lies **below** `t` in the measure `e`: the measure is a non-negative integer in both
states and strictly smaller in `t'`. This is what `decreases e` on a recursive routine means. -/
def Below (e : Expr) (t' t : State) : Prop :=
  ∃ a b, eval t' e = some (.int a) ∧ eval t e = some (.int b) ∧ 0 ≤ a ∧ a < b

/-- **The bounded self-contract**: `ρ f` meets `post` under `pre` on every state strictly
below `s` in the measure `e`. What a self-recursive routine's duty may assume about its own
recursive call -- and only that. -/
def ContractBelow (ρ : Env) (f : String) (e : Expr) (s : State) (pre : State → Prop)
    (post : State → State → Option Value → Prop) : Prop :=
  ∀ t', pre t' → Below e t' s → post t' (ρ f t').1 (ρ f t').2

/-- **A self-recursive routine meeting its duty under the bounded self-contract IS its
contract** -- the duty may assume the contract for every call on a state strictly below the
current one in the measure `e`; induction over the measure lifts that to every state. The
person proves `hd` (their own logic); the induction lives here once. -/
theorem contract_of_duty_rec (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (hr : Runs ρ f body)
    (hd : ∀ t, pre t → ContractBelow ρ f e t pre post →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post := by
  unfold ContractBelow at hd
  have key : ∀ (n : Nat) (t : State), pre t → (∀ b, eval t e = some (.int b) → b < n) →
      post t (ρ f t).1 (ρ f t).2 := by
    intro n
    induction n with
    | zero =>
      intro t ht hb
      obtain ⟨s', hs', hp⟩ := hd t ht (by
        intro t' _ ⟨a, b, _, hbt, ha, hab⟩
        have := hb b hbt
        omega)
      obtain ⟨h1, h2⟩ := hr t s' hs'
      rw [h1, h2]
      exact hp
    | succ n ih =>
      intro t ht hb
      obtain ⟨s', hs', hp⟩ := hd t ht (by
        intro t' ht' ⟨a, b, hat, hbt, ha, hab⟩
        apply ih t' ht'
        intro b' hb'
        rw [hat] at hb'
        have := hb b hbt
        cases hb'
        omega)
      obtain ⟨h1, h2⟩ := hr t s' hs'
      rw [h1, h2]
      exact hp
  intro t ht
  by_cases hm : ∃ b, eval t e = some (.int b)
  · obtain ⟨b, hb⟩ := hm
    apply key (b.toNat + 1) t ht
    intro b' hb'
    rw [hb] at hb'
    cases hb'
    omega
  · apply key 0 t ht
    intro b hb
    exact absurd ⟨b, hb⟩ hm

/-! ### Mutual recursion -- a CYCLE of routines, one induction

    `gerade` calls `ungerade` calls `gerade`: no routine's duty can assume the other's
    contract outright. What each may assume is the other's contract on states whose measure
    lies strictly below its own -- `BelowM`, the callee's `decreases` at the callee's state
    against the caller's at the caller's -- and one induction over that common bound gives
    every contract of the cycle. The members are data (`Member`), so that the theorem is
    stated once for cycles of every size. -/

structure Member where
  name : String
  body : List Stmt
  pre : State → Prop
  post : State → State → Option Value → Prop
  measure : Expr

/-- `t'` lies below `t` -- the measure `e'` at `t'` against the measure `e` at `t`. -/
def BelowM (e' e : Expr) (t' t : State) : Prop :=
  ∃ a b, eval t' e' = some (.int a) ∧ eval t e = some (.int b) ∧ 0 ≤ a ∧ a < b

/-- The contract of a cycle member `r'`, bounded by the measure `e` of the caller at `s`. -/
def ContractBelowM (ρ : Env) (r' : Member) (e : Expr) (s : State) : Prop :=
  ∀ t', r'.pre t' → BelowM r'.measure e t' s → r'.post t' (ρ r'.name t').1 (ρ r'.name t').2

/-- **Every member of a cycle meeting its duty under the bounded contracts of the cycle
    IS every contract of the cycle.** -/
theorem contracts_of_duties_rec (ρ : Env) (rs : List Member)
    (hr : ∀ r ∈ rs, Runs ρ r.name r.body)
    (hd : ∀ r ∈ rs, ∀ t, r.pre t → (∀ r' ∈ rs, ContractBelowM ρ r' r.measure t) →
      ∃ s', finalState (exec ρ r.body t) = some s' ∧ r.post t s' (finalValue (exec ρ r.body t))) :
    ∀ r ∈ rs, Contract ρ r.name r.pre r.post := by
  unfold ContractBelowM at hd
  have key : ∀ (n : Nat), ∀ r ∈ rs, ∀ t, r.pre t →
      (∀ b, eval t r.measure = some (.int b) → b < n) →
      r.post t (ρ r.name t).1 (ρ r.name t).2 := by
    intro n
    induction n with
    | zero =>
      intro r hr' t ht hb
      obtain ⟨s', hs', hp⟩ := hd r hr' t ht (by
        intro r' _ t' _ ⟨a, b, _, hbt, ha, hab⟩
        have := hb b hbt
        omega)
      obtain ⟨h1, h2⟩ := hr r hr' t s' hs'
      rw [h1, h2]
      exact hp
    | succ n ih =>
      intro r hr' t ht hb
      obtain ⟨s', hs', hp⟩ := hd r hr' t ht (by
        intro r' hr'' t' ht' ⟨a, b, hat, hbt, ha, hab⟩
        apply ih r' hr'' t' ht'
        intro b' hb'
        rw [hat] at hb'
        have := hb b hbt
        cases hb'
        omega)
      obtain ⟨h1, h2⟩ := hr r hr' t s' hs'
      rw [h1, h2]
      exact hp
  intro r hr' t ht
  by_cases hm : ∃ b, eval t r.measure = some (.int b)
  · obtain ⟨b, hb⟩ := hm
    apply key (b.toNat + 1) r hr' t ht
    intro b' hb'
    rw [hb] at hb'
    cases hb'
    omega
  · apply key 0 r hr' t ht
    intro b hb
    exact absurd ⟨b, hb⟩ hm

/-- **The loop's body preserving the invariant IS the loop rule** -- for any environment that
    runs the loop. The induction over the passes stands here once. -/
theorem looprule_of_body (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v : String) (hr : RunsLoop ρ id body v)
    (hb : ∀ t (k : Int), wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) :
    LoopRule ρ id wf inv := by
  intro t hw ht
  obtain ⟨ks, t', hit, heq⟩ := hr t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp [iterate] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    simp only [iterate] at hit
    split at hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      exact ih u hwf hinv hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      exact ih u hwf hinv hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      simp at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp)

/-- **`ρ id` runs the loop `id` over indices of a RANGE** -- what a `traverse … over slots
    of T` (or any domain inside one table) visits: indices of that table, `lo ≤ k < hi`.
    Which of them, in which order, how often: the domain's business; that none lies
    outside: the checker's (`K008`/`K009`), and here the premise a pass may use. -/
def RunsLoopIn (ρ : Env) (id : String) (body : List Stmt) (v : String) (lo hi : Int) : Prop :=
  ∀ t, ∃ ks t', (∀ k ∈ ks, lo ≤ k ∧ k < hi) ∧ iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **The loop rule from a pass that may assume its index is in range.** -/
theorem looprule_of_body_in (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v : String) (lo hi : Int) (hr : RunsLoopIn ρ id body v lo hi)
    (hb : ∀ t (k : Int), lo ≤ k → k < hi → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) })
        = some t' ∧ wf t' ∧ eval t' inv = some (.bool true)) :
    LoopRule ρ id wf inv := by
  intro t hw ht
  obtain ⟨ks, t', hks, hit, heq⟩ := hr t
  rw [heq]
  clear heq
  induction ks generalizing t with
  | nil => simp [iterate] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    have hk : lo ≤ k ∧ k < hi := hks k (by simp)
    have hks' : ∀ k ∈ ks, lo ≤ k ∧ k < hi := fun k' hk' => hks k' (by simp [hk'])
    simp only [iterate] at hit
    split at hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      exact ih u hwf hinv hks' hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      exact ih u hwf hinv hks' hit
    · rename_i u hu
      obtain ⟨u', hu', hwf, hinv⟩ := hb t k hk.1 hk.2 hw ht
      rw [hu] at hu'; simp [finalState] at hu'; subst hu'
      simp at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp)

/-! ### 5.1a Counting the passes -- `#pass` (agent b, 2026-09-08)

    **A counter incremented in a loop cannot be bounded by an invariant that does not know
    how often the loop runs.** `n ≤ 16` does not survive `n += 1`, and it never will: the
    rule above quantifies over EVERY state that satisfies the invariant, so a pass starting
    at `n = 16` has to be handled and cannot be. What the person means is `n ≤ <passes so
    far>`, and for that sentence to be sayable two things must be true of the model:

    * the number of passes already done is a value the invariant can name -- the ghost local
      `#pass`, bound to `0` right before the loop and increased by one by every pass (the
      emitter writes both; the increment is the pass's own first statement, so a `next` or a
      `leave` in the middle does not skip it);
    * the number of passes is BOUNDED. `RunsLoopIn` says every index lies in the domain's
      range and says nothing about how many passes there are, and no invariant can bound a
      counter without that. `RunsLoopN` adds the bound: at most `np` passes, where `np` is
      the domain's `count`. **This is a stronger assumption about the environment than
      `RunsLoopIn`, and it is exactly the sentence `by unvisited` makes** -- each slot of the
      domain is visited at most once, so a traversal of a table of `count N` runs at most `N`
      passes. It is assumed here, as the running of the body is assumed (`Runs`,
      `RunsLoop`, `RunsLoopIn`), and not proved: which indices a domain yields is the
      checker's business (`K008`/`K009`), not this file's.

    The pass may then assume `#pass = i` with `0 ≤ i < np`, and owes `#pass = i + 1` at its
    end -- one `simp` over the increment the emitter wrote, never a person's line. -/

/-- **`ρ id` runs the loop `id` over indices of a range, in at most `np` passes.** -/
def RunsLoopN (ρ : Env) (id : String) (body : List Stmt) (v : String) (lo hi np : Int) : Prop :=
  ∀ t, ∃ ks t', (∀ k ∈ ks, lo ≤ k ∧ k < hi) ∧ (ks.length : Int) ≤ np ∧
    iterate ρ body v ks t = some t' ∧ (ρ id t).1 = t'

/-- **The loop rule of a loop that counts its passes in the ghost local `pv`.** The same
    sentence as `LoopRule`, from a state in which the counter stands at zero -- which is
    where the emitter puts the loop, one `bindName` before it. -/
def LoopRuleP (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr) (pv : String) : Prop :=
  ∀ t, wf t → eval t inv = some (.bool true) → t.local' pv = .int 0 →
    wf (ρ id t).1 ∧ eval (ρ id t).1 inv = some (.bool true)

/-- The induction over the passes, with the counter carried along. -/
theorem looprule_passes_aux (ρ : Env) (wf : State → Prop) (inv : Expr) (body : List Stmt)
    (v pv : String) (lo hi np : Int)
    (hb : ∀ t (k i : Int), lo ≤ k → k < hi → 0 ≤ i → i < np →
      t.local' pv = .int i → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) }) = some t'
        ∧ wf t' ∧ eval t' inv = some (.bool true) ∧ t'.local' pv = .int (i + 1)) :
    ∀ (ks : List Int) (i : Int) (t u : State), (∀ k ∈ ks, lo ≤ k ∧ k < hi) →
      0 ≤ i → i + (ks.length : Int) ≤ np → t.local' pv = .int i →
      wf t → eval t inv = some (.bool true) → iterate ρ body v ks t = some u →
      wf u ∧ eval u inv = some (.bool true) := by
  intro ks
  induction ks with
  | nil =>
    intro i t u _ _ _ _ hw ht hit
    simp [iterate] at hit; subst hit; exact ⟨hw, ht⟩
  | cons k ks ih =>
    intro i t u hks h0 hlen hpv hw ht hit
    have hk : lo ≤ k ∧ k < hi := hks k (by simp)
    have hks' : ∀ k' ∈ ks, lo ≤ k' ∧ k' < hi := fun k' hk' => hks k' (by simp [hk'])
    simp only [List.length_cons] at hlen
    have hlt : i < np := by omega
    have hlen' : i + 1 + (ks.length : Int) ≤ np := by omega
    obtain ⟨u', hu', hwf, hinv, hpv'⟩ := hb t k i hk.1 hk.2 h0 hlt hpv hw ht
    simp only [iterate] at hit
    split at hit
    · rename_i w hw'
      rw [hw'] at hu'; simp [finalState] at hu'; subst hu'
      exact ih (i + 1) w u hks' (by omega) hlen' hpv' hwf hinv hit
    · rename_i w hw'
      rw [hw'] at hu'; simp [finalState] at hu'; subst hu'
      exact ih (i + 1) w u hks' (by omega) hlen' hpv' hwf hinv hit
    · rename_i w hw'
      rw [hw'] at hu'; simp [finalState] at hu'; subst hu'
      simp at hit; subst hit; exact ⟨hwf, hinv⟩
    · exact absurd hit (by simp)

/-- **The loop rule from a pass that may assume its index is in range AND that it is the
    `i`-th of at most `np` passes.** -/
theorem looprule_of_body_p (ρ : Env) (id : String) (wf : State → Prop) (inv : Expr)
    (body : List Stmt) (v pv : String) (lo hi np : Int) (hr : RunsLoopN ρ id body v lo hi np)
    (hb : ∀ t (k i : Int), lo ≤ k → k < hi → 0 ≤ i → i < np →
      t.local' pv = .int i → wf t → eval t inv = some (.bool true) →
      ∃ t', finalState (exec ρ body { t with local' := bindLocal t.local' v (.int k) }) = some t'
        ∧ wf t' ∧ eval t' inv = some (.bool true) ∧ t'.local' pv = .int (i + 1)) :
    LoopRuleP ρ id wf inv pv := by
  intro t hw ht h0
  obtain ⟨ks, t', hks, hlen, hit, heq⟩ := hr t
  rw [heq]
  exact looprule_passes_aux ρ wf inv body v pv lo hi np hb ks 0 t t' hks (by omega)
    (by omega) h0 hw ht hit

/-! ## 5. What holds over EVERY body

    These theorems belong to the model, not to a unit -- the emitter may use them without
    rewriting them per file.
-/

/-- **An empty sequence changes nothing.** -/
@[simp] theorem exec_nil (ρ : Env) (s : State) : exec ρ [] s = .running s := by
  simp [exec]

/-- **The descent is deterministic** -- it is a function, so this holds by construction. The
    theorem stands here anyway, because it is the statement a RELATIONAL model would have to
    prove at this point. -/
theorem exec_deterministic (ρ : Env) (as : List Stmt) (s : State) (o₁ o₂ : Outcome)
    (h₁ : exec ρ as s = o₁) (h₂ : exec ρ as s = o₂) : o₁ = o₂ := by
  subst h₁; exact h₂

/-- **A place no assignment names survives a single step.**

    This is the frame statement in its smallest form. It stands here for assignment, because
    that is where the frame arises; over a whole sequence it is carried by
    `Passlogik.Wirkung.huelle_deckt` out of the `effects` list, and the two meet at the pass. -/
theorem assign_leaves_others (ρ : Env) (c : String) (i e : Expr) (f : String) (s s' : State)
    (p : Place) (h : step ρ (.assign c i f e) s = .running s')
    (hne : ∀ k, p ≠ .slot c k f) : s'.world p = s.world p := by
  simp only [step] at h
  split at h
  · rename_i k v hi he
    injection h with h
    subst h
    simp only [store]
    rw [if_neg (hne k)]
  · exact absurd h (by simp)

end Gabbro.Body

/-! ## 6. The proof bundle

    **`gabbro_simp` unfolds the model, and it stands OUTSIDE the namespace on purpose.**
    A tactic declared inside `Gabbro.Body` is not in scope for a specification that merely
    `open`s it -- measured: every use reported *"unknown tactic"*, and the goal then stood
    open beside an error that looked like a typo. The names inside are fully qualified for
    the same reason.

    It lives here and not in the generated file so that a specification need not know the
    model's internals, and so a change to the model reaches every proof through one place.
    *A tactic copied into every generated module is one statement in as many places as there
    are files.*
-/

open Lean.Parser.Tactic in
macro "gabbro_simp" : tactic =>
  `(tactic| simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag])

-- The same, with the caller's own facts: `gabbro_simp [hf, mySpec]`.
open Lean.Parser.Tactic in
macro "gabbro_simp" "[" ts:simpLemma,* "]" : tactic =>
  -- the caller's definitions first (`_pre`, `_inv`, `_post`), so that the pre-lemmas
  -- (`↓eval_and_true_iff`) see the conjunction BEFORE `eval` is unfolded under it
  `(tactic| ((try simp only [$ts,*]); simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*]))

-- The same, and every hypothesis of the context as a rewrite: `simp [model, lemmas, *]`.
open Lean.Parser.Tactic in
macro "gabbro_simp_hyps" "[" ts:simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [$ts,*]); simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier, Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*, *]))

/-! ## 7. What the generated theorem ends with

    **`gabbro_auto` closes what the model closes by computation and leaves a `sorry` on
    what it does not** -- and that `sorry` is, by construction, the human's own logic: every
    hypothesis the goal could need is already in front of the turnstile (§4.1). The
    generated file counts its `sorry` warnings in `instrumente/pruefe-lean-beweis.sh`; a
    person proves the corresponding `_statement` in a file of their own and instantiates
    the unit's wiring theorem with it.

    What the automation does, in order, and each step is plumbing a person used to write:
      1. `gabbro_simp` runs the body;
      2. `gabbro_calls` instantiates every `Contract` and `LoopRule` hypothesis at every
         `ρ f t` the goal mentions, tries the precondition (well-typed world by
         `gabbro_wf`, the rest by computation), and rewrites with the frame;
      3. the conjunction of the promise is split, `gabbro_wf` closes the well-typedness
         of every stored world;
      4. what is left is the person's: a `requires` at a call the model could not
         compute, an invariant after a store, an equation between two indices.
-/

namespace Gabbro.Body

/-- A read from a well-typed world has the declared shape. -/
theorem WF_read (Γ : Typing) (σ : World) (p : Place) (sh : Shape) (h : WF Γ σ)
    (hp : Γ p = some sh) : (σ p).hasShape sh = true := h p sh hp

/-- **A read outside the callee's frame reads the caller's world.** Written as a rewrite so
    that `simp` applies it; the side condition is a list membership over string literals,
    which `simp` decides. -/
theorem Frame_read (ρ : Env) (f : String) (w : List String) (fr : Frame ρ f w) (t : State)
    (p : Place) (h : p.carrier ∉ w) : (ρ f t).1.world p = t.world p := fr t p h

end Gabbro.Body

open Lean Elab Tactic Meta in
/-- **A `have` whose holes are closed HERE, by `tac`, or the `have` fails** -- never a
    nested `by`: that one is elaborated later, and where it does not close, its failure is
    LOGGED as an error of the theorem while the tactic that wrote it goes on believing it
    succeeded (measured 2026-09-07, `kapraum`). -/
def GabbroMeta.haveClosed (stx : TSyntax `tactic) (tac : TSyntax `tactic) : TacticM Unit := do
  let g ← getMainGoal
  let gty ← g.withContext (instantiateMVars (← g.getType))
  let before ← getGoals
  evalTactic stx
  let after ← getGoals
  let fresh := after.filter (fun m => !(before.contains m))
  let mut main? : Option MVarId := none
  let mut holes : List MVarId := []
  for m in fresh do
    let ty ← m.withContext (instantiateMVars (← m.getType))
    if main?.isNone && (← m.withContext (isDefEq ty gty)) then
      main? := some m
    else
      holes := holes ++ [m]
  let some main := main? | throwError "gabbro: the `have` left no main goal"
  for h in holes do
    setGoals [h]
    evalTactic tac
    unless (← getGoals).isEmpty do throwError "gabbro: a hole of the `have` stays open"
  setGoals ([main] ++ after.filter (fun m => !(fresh.contains m)))

open Lean Elab Tactic Meta in
/-- **`gabbro_assumption` -- `assumption`, and INTO the conjunctions.** A contract's
    instance is one hypothesis `wellFormed t' ∧ inv t' ∧ …`; the well-typed world the next
    call demands is its first half. This closes a goal that is a conjunct of a hypothesis,
    at any depth of a right-nested `∧`. -/
elab "gabbro_assumption" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let rec search (proof : Lean.Expr) (ty : Lean.Expr) : Nat → MetaM (Option Lean.Expr)
      | 0 => do if ← isDefEq ty target then return some proof else return none
      | depth + 1 => do
        if ← isDefEq ty target then return some proof
        let ty ← whnfR ty
        if ty.isAppOfArity ``And 2 then
          let a := ty.getAppArgs[0]!
          let b := ty.getAppArgs[1]!
          if let some p ← search (mkApp3 (mkConst ``And.left) a b proof) a depth then return some p
          if let some p ← search (mkApp3 (mkConst ``And.right) a b proof) b depth then return some p
        return none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some p ← search d.toExpr (← instantiateMVars d.type) 8 then
        g.assign p
        replaceMainGoal []
        return
    throwError "gabbro_assumption: no hypothesis, or conjunct of one, matches the goal"

open Lean Elab Tactic Meta in
/-- **A hypothesis, opened**: a conjunction into its parts, an existential into witness and
    fact, a disjunction into two goals -- as far down as it goes. What a contract instance
    says about a call's answer (`∃ x, (ρ f t).2 = some (.int x)`) becomes the rewrite
    `simp` can use. -/
partial def GabbroMeta.openHyp (n : Name) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  let g ← getMainGoal
  let some d ← g.withContext (return (← getLCtx).findFromUserName? n) | return
  let ty ← g.withContext (whnfR (← instantiateMVars d.type))
  -- the hypothesis itself STAYS -- it may be named in a simp set (`hall`, `c_m`); what is
  -- opened is a copy
  let h ← if n.hasMacroScopes then pure (mkIdent n) else do
    let c := mkIdent (← mkFreshUserName `hcopy)
    let orig := mkIdent n
    evalTactic (← `(tactic| have $c := $orig))
    pure c
  if ty.isAppOfArity ``And 2 then
    let a := mkIdent (← mkFreshUserName `ha)
    let b := mkIdent (← mkFreshUserName `hb)
    evalTactic (← `(tactic| obtain ⟨$a, $b⟩ := $h))
    openHyp a.getId (fuel - 1)
    openHyp b.getId (fuel - 1)
  else if ty.isAppOfArity ``Exists 2 then
    let x := mkIdent (← mkFreshUserName `x)
    let hx := mkIdent (← mkFreshUserName `hx)
    evalTactic (← `(tactic| obtain ⟨$x, $hx⟩ := $h))
    openHyp hx.getId (fuel - 1)
  -- a shape fact about a value becomes the witness it stands for
  else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Value.hasShape 2
      && ty.getAppArgs[2]!.isConstOf ``Bool.true then
    let sh := ty.getAppArgs[1]!.getAppArgs[1]!
    let w := mkIdent (← mkFreshUserName `hw)
    let lemma : Option Name :=
      if sh.isConstOf ``Gabbro.Body.Shape.int then some ``Gabbro.Body.Value.hasShape_int_true
      else if sh.isConstOf ``Gabbro.Body.Shape.bool then some ``Gabbro.Body.Value.hasShape_bool_true
      else if sh.isAppOfArity ``Gabbro.Body.Shape.sum 1 then some ``Gabbro.Body.Value.hasShape_sum_true
      else if sh.isConstOf ``Gabbro.Body.Shape.opt then some ``Gabbro.Body.Value.hasShape_opt_true
      else if sh.isAppOfArity ``Gabbro.Body.Shape.intIn 2 then some ``Gabbro.Body.Value.hasShape_intIn_true
      else none
    if let some l := lemma then
      let ls := mkIdent l
      if sh.isAppOfArity ``Gabbro.Body.Shape.intIn 2 then
        evalTactic (← `(tactic| have $w := $ls _ _ _ $h))
      else if sh.isAppOfArity ``Gabbro.Body.Shape.sum 1 then
        evalTactic (← `(tactic| have $w := $ls _ _ $h))
      else
        evalTactic (← `(tactic| have $w := $ls _ $h))
      openHyp w.getId (fuel - 1)
  -- a case fact about a `tagged` value: computed against the case names in play, it is
  -- the disjunction of the possible cases (with their payloads), and that is opened
  else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Shape.caseOk 3 then
    let c := mkIdent (← mkFreshUserName `hcase)
    evalTactic (← `(tactic| have $c := $h))
    evalTactic (← `(tactic| try simp [Gabbro.Body.Shape.caseOk_cons, Gabbro.Body.Shape.caseOk_nil, *] at $c:ident))
    -- (a `simp at` that turns the copy into `True` clears it; nothing to open then)
    let g' ← getMainGoal
    if (← g'.withContext (return (← getLCtx).findFromUserName? c.getId)).isSome then
      openHyp c.getId (fuel - 1)
  else if ty.isAppOfArity ``Or 2 then
    let a := mkIdent (← mkFreshUserName `ho)
    evalTactic (← `(tactic| rcases $h:ident with $a:ident | $a:ident))
    let gs ← getGoals
    let mut out : List MVarId := []
    for g' in gs do
      setGoals [g']
      openHyp a.getId (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out

open Lean Elab Tactic Meta in
/-- `gabbro_open h` -- `GabbroMeta.openHyp`, as a tactic. -/
elab "gabbro_open " h:ident : tactic => do
  GabbroMeta.openHyp h.getId 16

open Lean Elab Tactic Meta in
/-- **`gabbro_open_hyps` -- every hypothesis opened** that is a conjunction, an existential,
    a disjunction or a shape fact: what the openings and the instances left folded. A
    disjunction splits the goal; that is the case analysis a `tagged` value's cases or a
    `return` inside a loop demand anyway. -/
elab "gabbro_open_hyps" : tactic => do
  let g ← getMainGoal
  let names ← g.withContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2
          || (ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Value.hasShape 2)
          || (ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Shape.caseOk 3) then
        out := out.push d.userName
    pure out
  for n in names do
    -- in every goal an earlier opening left
    let gs ← getGoals
    let mut out : List MVarId := []
    for g' in gs do
      setGoals [g']
      try GabbroMeta.openHyp n 16 catch _ => pure ()
      out := out ++ (← getGoals)
    setGoals out

open Lean Elab Tactic Meta in
/-- **`gabbro_instantiate` -- a quantified invariant, at the index in play.** For every
    hypothesis `∀ k, k < N → P k` (what a `forallSlots` becomes) and every `k : Nat` of the
    context that is known to be below a bound, `P k` is added -- the instance a person
    would `specialize` by hand before arguing about the slot the body touched. -/
elab "gabbro_instantiate" : tactic => do
  withMainContext do
    let lctx ← getLCtx
    -- the quantified facts: at the top of a hypothesis, or inside its conjunctions
    let mut quantified : Array Lean.Expr := #[]
    let mut indices : Array LocalDecl := #[]
    let rec collect (proof : Lean.Expr) (ty : Lean.Expr) : Nat → MetaM (Array Lean.Expr)
      | 0 => pure #[]
      | depth + 1 => do
        match ty with
        | .forallE _ (.const ``Nat []) (.forallE _ bound _ _) _ =>
          if bound.isAppOfArity ``LT.lt 4 then return #[proof] else return #[]
        | _ =>
          let ty ← whnfR ty
          if ty.isAppOfArity ``And 2 then
            let a := ty.getAppArgs[0]!
            let b := ty.getAppArgs[1]!
            let l ← collect (mkApp3 (mkConst ``And.left) a b proof) a depth
            let r ← collect (mkApp3 (mkConst ``And.right) a b proof) b depth
            return l ++ r
          return #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      quantified := quantified ++ (← collect d.toExpr ty 6)
      if ty.isConstOf ``Nat then indices := indices.push d
    let mut n := 0
    for q in quantified do
      for k in indices do
        if n ≥ 12 then break
        -- only where the bound is at hand: `k < N` by a hypothesis or by arithmetic
        let saved ← saveState
        try
          let hq ← Term.exprToSyntax q
          let hk := mkIdent k.userName
          let w := mkIdent (← mkFreshUserName `hq)
          GabbroMeta.haveClosed (← `(tactic| have $w := $hq $hk ?_)) (← `(tactic| first | assumption | omega))
          n := n + 1
        catch _ =>
          saved.restore

open Lean Elab Tactic Meta in
/-- Every closed `allBelow f n` in `e`. -/
partial def GabbroMeta.collectAllBelow (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Gabbro.Body.allBelow 2 && !e.hasLooseBVars && !e.hasMVar then
        acc.modify (·.push (e.getAppArgs[0]!, e.getAppArgs[1]!))
      for a in e.getAppArgs do go a
      go e.getAppFn
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

open Lean Elab Tactic Meta in
/-- **`gabbro_forall [lemmas]` -- a quantified premise that the context already grants.**
    A `forallSlots` the goal is stuck on (a callee's `requires` over the whole table, an
    invariant demanded at a loop's entry) is `allBelow f n`; where every instance follows
    from the hypotheses, the whole is `some (.bool true)`, and the goal's `match` on it
    reduces. The instance is proved by `simp_all` after `gabbro_instantiate`; what does
    not go through this way stays. -/
syntax "gabbro_forall" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_forall [$ts,*]) => do
    let g ← getMainGoal
    let terms ← g.withContext do GabbroMeta.collectAllBelow (← instantiateMVars (← g.getType))
    for (f, n) in terms do
      let saved ← saveState
      try
        let fs ← (← getMainGoal).withContext do Term.exprToSyntax f
        let ns ← (← getMainGoal).withContext do Term.exprToSyntax n
        let w := mkIdent (← mkFreshUserName `hall)
        GabbroMeta.haveClosed
          (← `(tactic| have $w : Gabbro.Body.allBelow $fs $ns = some (.bool true) := ?_))
          (← `(tactic| (refine (Gabbro.Body.allBelow_true_iff _ _).mpr ?_
                        intro k hk
                        gabbro_instantiate
                        simp_all [$ts,*])))
        evalTactic (← `(tactic| simp only [$w:ident]))
      catch _ =>
        saved.restore

/-- Every closed `a &&& b`, `a ^^^ b`, `a ||| b` over `Nat` in `e` -- `0`, `1`, `2` for the
    operator. -/
partial def GabbroMeta.collectAnd (e : Lean.Expr) (acc : Array (Nat × Lean.Expr × Lean.Expr)) :
    Array (Nat × Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectAnd x a) (GabbroMeta.collectAnd fn acc)
    if args.size == 6 && args[0]!.isConstOf ``Nat && !args[4]!.hasLooseBVars && !args[5]!.hasLooseBVars then
      if fn.isConstOf ``HAnd.hAnd then acc.push (0, args[4]!, args[5]!)
      else if fn.isConstOf ``HXor.hXor then acc.push (1, args[4]!, args[5]!)
      else if fn.isConstOf ``HOr.hOr then acc.push (2, args[4]!, args[5]!)
      else acc
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectAnd b acc
  | .letE _ _ v b _ => GabbroMeta.collectAnd b (GabbroMeta.collectAnd v acc)
  | .mdata _ b => GabbroMeta.collectAnd b acc
  | .proj _ _ b => GabbroMeta.collectAnd b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_bits` -- the bounds of every bitwise `and` in the goal.** `x & 251` on a `u8`
    field is `↑(x.toNat &&& 251)` in the model, and `omega` cannot read `&&&`; the bounds
    `n &&& m ≤ m` and `n &&& m ≤ n` (`Nat.and_le_right/left`) are what the store into a
    ranged place needs, and the person never wrote them (2026-09-08, `planer`). -/
elab "gabbro_bits" : tactic => do
  let g ← getMainGoal
  let ands ← g.withContext do
    let mut acc := GabbroMeta.collectAnd (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectAnd (← instantiateMVars d.type) acc
    pure acc
  let ands := ands.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2.1 == t.2.1 && u.2.2 == t.2.2) then acc else acc.push t) #[]
  let close ← `(tactic| first | assumption | omega)
  for (op, a, b) in ands do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    if op == 0 then
      evalTactic (← `(tactic| try have := @Nat.and_le_right $as $bs))
      evalTactic (← `(tactic| try have := @Nat.and_le_left $as $bs))
    else
      -- `x ^^^ y < 2^n` and `x ||| y < 2^n` where both operands are below `2^n`: the
      -- width is tried from the narrowest up, and the first the context bounds is kept
      for w in [8, 16, 32, 64] do
        let ws := Syntax.mkNumLit (toString w)
        let saved ← saveState
        try
          if op == 1 then
            GabbroMeta.haveClosed (← `(tactic| have := @Nat.xor_lt_two_pow $as $bs $ws ?_ ?_)) close
          else
            GabbroMeta.haveClosed (← `(tactic| have := @Nat.or_lt_two_pow $as $bs $ws ?_ ?_)) close
          break
        catch _ => saved.restore

/-- **`gabbro_wf Γ` closes `WF Γ (store … (store σ p v) …)` from `WF Γ σ`**: every store
    is peeled with `WF_store`, and the side condition -- the stored value has the declared
    shape -- is decided by unfolding the typing, or read off a well-typed world where the
    value is a read (`WF_read`). Where neither applies the goal stays for the person. -/
syntax "gabbro_wf" ident : tactic
macro_rules
  | `(tactic| gabbro_wf $t:ident) =>
    `(tactic| first
        | assumption
        | gabbro_assumption
        | (apply Gabbro.Body.WF_store
           · gabbro_wf $t
           · (intro sh hsh; simp [$t:ident] at hsh;
              -- an undeclared place has no shape: `hsh` is `False`, and the goal is gone
              first
                | done
                | (subst hsh;
                   first
                     | (simp [Gabbro.Body.Value.hasShape]; done)
                     -- a ranged place: the bounds, by the arithmetic the context carries
                     | (simp [Gabbro.Body.Value.hasShape]; gabbro_bits; omega)
                     | (apply Gabbro.Body.WF_read <;> first | assumption | gabbro_assumption | rfl)
                     -- a value read from another ranged place: its witness, then the bounds
                     | (simp [Gabbro.Body.Value.hasShape, *]; gabbro_bits; omega)
                     | (simp_all [Gabbro.Body.Value.hasShape]; gabbro_bits; omega)
                     -- and what none of these closes is left reduced, for the person
                     | simp [Gabbro.Body.Value.hasShape]))))

/-- **`gabbro_shape Γ` closes `∃ n, σ p = .int n` (and the bool, sum and option forms)
    from a well-typed world** -- what a routine's answer read from a place owes to the
    promise's shape clause. The place's shape is decided by `rfl` over the typing. -/
syntax "gabbro_shape" ident : tactic
open Lean Elab Tactic Meta in
/-- Every read `σ p` of a world in `e` -- `State.world s` applied to a closed place. -/
partial def GabbroMeta.collectReads (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app fn p =>
      -- a state's world -- NOT a world with stores on it: a read through a store is first
      -- decided by `gabbro_split` (the same place, or another), and only what is left is a
      -- read of the state's world; a witness taken before the split would hide the store
      let isWorld := fn.isAppOfArity ``Gabbro.Body.State.world 1
        || (match fn with | .proj ``Gabbro.Body.State 0 _ => true | _ => false)
      if isWorld && !fn.hasLooseBVars && !p.hasLooseBVars then
        acc.modify (·.push (fn, p))
      go fn
      go p
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_shape $Γ:ident) => do
    let g ← getMainGoal
    -- the reads of the goal, and of the hypotheses: an instantiated invariant reads the
    -- slot the body touched, and its witness is what lets the two be compared
    let reads ← g.withContext do
      let mut all ← GabbroMeta.collectReads (← instantiateMVars (← g.getType))
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        all := all ++ (← GabbroMeta.collectReads (← instantiateMVars d.type))
      -- each read once, and not one that already has its witness (`σ p = .int n`)
      let lctx ← getLCtx
      let witnessed (σ p : Lean.Expr) : Bool := lctx.any fun d =>
        !d.isImplementationDetail && d.type.isAppOfArity ``Eq 3
          && d.type.getAppArgs[1]! == mkApp σ p
      let mut uniq : Array (Lean.Expr × Lean.Expr) := #[]
      for r in all do
        if uniq.size ≥ 16 then break
        if witnessed r.1 r.2 then continue
        unless uniq.any (fun u => u.1 == r.1 && u.2 == r.2) do uniq := uniq.push r
      pure uniq
    let mut opened := false
    for (σ, p) in reads do
      let σs ← (← getMainGoal).withContext do Term.exprToSyntax σ
      let ps ← (← getMainGoal).withContext do Term.exprToSyntax p
      for l in [``Gabbro.Body.WF_int, ``Gabbro.Body.WF_intIn, ``Gabbro.Body.WF_bool, ``Gabbro.Body.WF_sum, ``Gabbro.Body.WF_opt] do
        let saved ← saveState
        try
          let w := mkIdent (← mkFreshUserName `hw)
          let ls := mkIdent l
          -- `rfl` decides the shape: a wrong lemma fails to elaborate and is skipped
          if l == ``Gabbro.Body.WF_sum then
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps _ ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          else if l == ``Gabbro.Body.WF_intIn then
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps _ _ ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          else
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          GabbroMeta.openHyp w.getId 4
          opened := true
          break
        catch _ =>
          saved.restore
    if opened then
      evalTactic (← `(tactic| all_goals (try (simp [*]; done))))


open Lean Elab Tactic Meta in
/-- Every `ρ f t` in `e` where `ρ` is a local of type `Env` -- with `t` closed (no loose
    bound variables), because only a closed state can be handed to a contract. -/
partial def GabbroMeta.collectCalls (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isFVar && args.size ≥ 2 && !args[0]!.hasLooseBVars && !args[1]!.hasLooseBVars then
        let ty ← whnf (← inferType fn)
        if (← isDefEq ty (mkConst ``Gabbro.Body.Env)) then
          acc.modify (·.push (fn, args[0]!, args[1]!))
      for a in args do go a
      go fn
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get


open Lean Elab Tactic Meta in
/-- **`gabbro_calls Γ [lemmas]` -- the composition, applied.** For every `ρ f t` the goal
    mentions and every hypothesis `Contract ρ f pre post` or `LoopRule ρ f wf inv`, the
    instance at `t` is added as a hypothesis; its precondition is tried (the well-typed
    world by `gabbro_wf`, the rest by the simp set) and stays as a goal where it is the
    person's -- a `requires` the model cannot compute is exactly the `V` duty. The instance
    is then simplified with the same set, so its clauses become rewrites. -/
elab "gabbro_calls" Γ:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [0:12] do
    -- an instance that says `False` (a callee that never returns) closes the goal
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let calls ← g.withContext do
      GabbroMeta.collectCalls (← instantiateMVars (← g.getType))
    -- **innermost first**: a call whose state is another call's answer needs that one's
    -- instance in the context of its own precondition -- and a hole opened earlier does
    -- not see a hypothesis added later
    let calls := calls.qsort (fun a b => a.2.2.approxDepth < b.2.2.approxDepth)
    let mut progress := false
    for (ρ, f, t) in calls do
      if (← getGoals).isEmpty then return
      let key := mkApp2 ρ f t
      -- in the goal's context: `isDefEq` on a state expression reads its variables --
      -- and a call instantiated by an EARLIER pass left its mark (`gabbro_seen : c = c`),
      -- so that a second pass does not instantiate (and open, and split) it again
      -- (per GOAL, by the mark, and not per invocation: a sibling goal an opening left
      -- has no instance yet, and gets its own)
      let already ← (← getMainGoal).withContext do
        let lctx ← getLCtx
        lctx.anyM fun d => do
          if d.isImplementationDetail then return false
          let ty ← instantiateMVars d.type
          if ty.isAppOfArity ``Eq 3 && d.userName.toString.startsWith "gabbro_seen" then
            isDefEq ty.getAppArgs[1]! key
          else
            return false
      if already then continue
      let decls ← (← getMainGoal).withContext do
        let lctx ← getLCtx
        let mut out : Array (LocalDecl × Nat) := #[]
        for d in lctx do
          if d.isImplementationDetail then continue
          let ty ← instantiateMVars d.type
          if ty.isAppOfArity ``Gabbro.Body.Contract 4 then
            let a := ty.getAppArgs
            if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 1)
          else if ty.isAppOfArity ``Gabbro.Body.LoopRule 4 then
            let a := ty.getAppArgs
            if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 2)
          -- **the rule of a loop that counts its passes** (agent b, 2026-09-08): a third
          -- premise, that the counter stands at zero -- the `bindName` right before the loop
          else if ty.isAppOfArity ``Gabbro.Body.LoopRuleP 5 then
            let a := ty.getAppArgs
            if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 3)
          -- the bounded self-contract: two holes as well -- the precondition and `Below`
          else if ty.isAppOfArity ``Gabbro.Body.ContractBelow 6 then
            let a := ty.getAppArgs
            if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 2)
          -- the bounded contract of a cycle member: the member is a literal, its name first
          else if ty.isAppOfArity ``Gabbro.Body.ContractBelowM 4 then
            let a := ty.getAppArgs
            let m := a[1]!
            if m.isAppOfArity ``Gabbro.Body.Member.mk 5 then
              if (← isDefEq a[0]! ρ) && (← isDefEq m.getAppArgs[0]! f) then out := out.push (d, 2)
        pure out
      for (d, nholes) in decls do
        -- one instance that cannot be built is skipped, not the whole composition
        let saved ← saveState
        try
          let c ← (← getMainGoal).withContext do Term.exprToSyntax d.toExpr
          let tt ← (← getMainGoal).withContext do Term.exprToSyntax t
          let hn := mkIdent (← mkFreshUserName `hc)
          let before ← getGoals
          let lctxBefore ← (← getMainGoal).withContext getLCtx
          if nholes == 3 then
            evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_ ?_))
          else if nholes == 2 then
            evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_))
          else
            evalTactic (← `(tactic| have $hn := $c $tt ?_))
          let after ← getGoals
          let main := after[0]!
          let holes := after.filter (fun m => m != main && !(before.contains m))
          -- the mark, on the goal that holds the instance (and so on everything opened
          -- from it), before the opening -- not on a sibling that never got it
          let ks ← main.withContext do Term.exprToSyntax key
          let mark := mkIdent (← mkFreshUserName `gabbro_seen)
          setGoals [main]
          evalTactic (← `(tactic| have $mark : $ks = $ks := rfl))
          let main ← getMainGoal
          -- the precondition: the well-typed world and what computes; the rest stays
          let mut rest : List MVarId := []
          for h in holes do
            setGoals [h]
            -- closed whole where it can be; `Below` by computation and arithmetic; else
            -- reduced as far as the simp set goes, and left
            evalTactic (← `(tactic| try (first
              | (simp only [$ts,*]; (try apply And.intro) <;> first | gabbro_wf $Γ | (gabbro_simp_hyps [$ts,*]; done))
              | (gabbro_simp_hyps [$ts,*]; done)
              | (gabbro_simp_hyps [$ts,*]; omega)
              | (simp only [$ts,*]; (try apply And.intro) <;> first | gabbro_wf $Γ | (gabbro_simp_hyps [$ts,*]; done) | skip))))
            -- what a hole leaves is kept -- every hole's, not only the last one's
            rest := rest ++ (← getGoals)
          setGoals ([main] ++ rest ++ (after.filter (fun m => m != main && before.contains m)))
          -- the instance, simplified into rewrites
          evalTactic (← `(tactic| try simp only [$ts,*, Gabbro.Body.Contract, Gabbro.Body.LoopRule, Gabbro.Body.LoopRuleP, Gabbro.Body.ContractBelow, Gabbro.Body.ContractBelowM] at $hn:ident))
          evalTactic (← `(tactic| try simp [$ts,*, ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
            Gabbro.Body.eval, Gabbro.Body.binop, Gabbro.Body.unop, Gabbro.Body.bindLocal, Gabbro.Body.bindAll] at $hn:ident))
          -- and opened: the call's answer, the invariants, every clause as its own fact
          evalTactic (← `(tactic| try gabbro_open $hn:ident))
          -- **and the goal learns the answer at once**: the next call outward reads this
          -- one's answer through a `match`, and only with `(ρ f t).2 = some v` rewritten
          -- is its state closed -- a call under a `match` arm has a loose variable and is
          -- not collected. So the facts the opening added are used as rewrites on the goal
          -- here, in the same round, and not in a later step of the pipeline
          if !(← getGoals).isEmpty then
            let news ← (← getMainGoal).withContext do
              let mut out : Array (TSyntax `term) := #[]
              for d in ← getLCtx do
                if d.isImplementationDetail then continue
                if lctxBefore.contains d.fvarId then continue
                if (← instantiateMVars d.type).isAppOfArity ``Eq 3 then
                  out := out.push (← Term.exprToSyntax d.toExpr)
              pure out
            if !news.isEmpty then
              let lems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← news.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:term)
              -- (with the bindings and stores at their names: the instance was built
              -- over the reduced state, and the goal has to show the same state)
              evalTactic (← `(tactic| try simp only [$lems,*, Gabbro.Body.bindLocal_here, Gabbro.Body.bindLocal_elsewhere,
                Gabbro.Body.store_here, Gabbro.Body.store_elsewhere]))
          progress := true
          if (← getGoals).isEmpty then return
        catch ex =>
          saved.restore
          logInfo m!"gabbro_calls: skipped an instance: {ex.toMessageData}"
    if !progress then break

open Lean.Parser.Tactic in
/-- `gabbro_simp_at h [lemmas]` -- the model's simp set, at a hypothesis: what turns an
    opened invariant or an instantiated contract into rewrites. -/
macro "gabbro_simp_at" h:ident "[" ts:simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [$ts,*] at $h:ident); try simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier,
                  Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*] at $h:ident))

open Lean Elab Tactic Meta in
/-- Every `store σ p v q` in `e` with `p` and `q` closed and not syntactically equal --
    the reads the model could not decide, because whether two indices coincide is a
    fact about the program and not about the form. -/
partial def GabbroMeta.collectStores (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Gabbro.Body.store 4 then
        let a := e.getAppArgs
        let p := a[1]!
        let q := a[3]!
        if !p.hasLooseBVars && !q.hasLooseBVars && p != q then
          acc.modify (·.push (q, p))
      for a in e.getAppArgs do go a
      go e.getAppFn
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

open Lean Elab Tactic Meta in
/-- **`gabbro_split` -- the case split on every undecided read.** For every `store σ p v q`
    the goal still holds, `q = p` or `q ≠ p`; in the first the read is the stored value, in
    the second the old one. Which of the two holds is the person's logic; that a split is
    what stands between the goal and it is not. -/
syntax "gabbro_split" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_split) => do
  let g ← getMainGoal
  let stores ← g.withContext do
    GabbroMeta.collectStores (← instantiateMVars (← g.getType))
  if stores.isEmpty then return
  let (q, p) := stores[0]!
  let qs ← g.withContext do Term.exprToSyntax q
  let ps ← g.withContext do Term.exprToSyntax p
  let hn := mkIdent (← mkFreshUserName `hq)
  -- **Two places that differ in carrier or field are different, and no split is needed**
  -- -- `slot "Faeden" x "gruende"` is never `slot "Endpunkte" e "wartet"`; the case split
  -- is for the same field at two indices.
  let lit (e : Lean.Expr) : Option String := match e with
    | .lit (.strVal x) => some x
    | _ => none
  let differ : Bool :=
    if q.isAppOfArity ``Gabbro.Body.Place.slot 3 && p.isAppOfArity ``Gabbro.Body.Place.slot 3 then
      let qa := q.getAppArgs; let pa := p.getAppArgs
      match lit qa[0]!, lit qa[2]!, lit pa[0]!, lit pa[2]! with
      | some c1, some f1, some c2, some f2 => c1 != c2 || f1 != f2
      | _, _, _, _ => false
    else if q.isAppOfArity ``Gabbro.Body.Place.global 1 && p.isAppOfArity ``Gabbro.Body.Place.global 1 then
      match lit q.getAppArgs[0]!, lit p.getAppArgs[0]! with
      | some a, some b => a != b
      | _, _ => false
    else
      -- a slot against a global, a field against a slot: different constructors
      (q.getAppFn.constName? != p.getAppFn.constName?) && q.getAppFn.isConst && p.getAppFn.isConst
  if differ then
    GabbroMeta.haveClosed (← `(tactic| have $hn : $qs ≠ $ps := ?_)) (← `(tactic| simp))
    evalTactic (← `(tactic| all_goals (try simp only [Gabbro.Body.store_elsewhere _ _ _ _ $hn:ident])))
    evalTactic (← `(tactic| all_goals (try gabbro_split)))
    return
  evalTactic (← `(tactic| by_cases $hn : $qs = $ps))
  evalTactic (← `(tactic| all_goals (try (first
    | (subst $hn; simp only [Gabbro.Body.store_here])
    | (simp only [$hn:ident, Gabbro.Body.store_here])
    | (simp only [Gabbro.Body.store_elsewhere _ _ _ _ $hn:ident])))))
  -- the split hypothesis, read as what it says about the INDICES: `slot T k f = slot T j f`
  -- is `k = j`, and that is the form the person's argument (and `omega`) reads
  evalTactic (← `(tactic| all_goals (try simp only [Gabbro.Body.Place.slot.injEq,
    Gabbro.Body.Place.field.injEq, Gabbro.Body.Place.global.injEq, eq_self_iff_true,
    and_true, true_and, not_and] at $hn:ident)))
  evalTactic (← `(tactic| all_goals (try gabbro_split)))

open Lean Elab Tactic Meta in
/-- Every `decide p` in `e` with `p` closed -- the conditions of the program's `if`s and
    comparisons, which `simp` cannot decide because they are about the values and not
    about the form. -/
partial def GabbroMeta.collectDecides (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Decidable.decide 2 then
        let p := e.getAppArgs[0]!
        if !p.hasLooseBVars && !p.hasMVar then
          acc.modify (·.push p)
      -- the condition of an `if` (a `bindLocal` on names, a `pickTag` on a case name)
      else if e.isAppOfArity ``ite 5 then
        let c := e.getAppArgs[1]!
        if !c.hasLooseBVars && !c.hasMVar && c.hasFVar then
          acc.modify (·.push c)
      -- a boolean READ (`Value.bool b`, `b` a variable the well-typed world gave) is a
      -- condition too: `b = true` or not
      else if e.isAppOfArity ``Gabbro.Body.Value.bool 1 then
        let b := e.getAppArgs[0]!
        -- a variable, or a term over one (`!b`, `b && c`) -- not a literal, and not a
        -- `decide`, which is collected as the proposition it decides
        if !b.hasLooseBVars && !b.hasMVar && !b.isConstOf ``Bool.true && !b.isConstOf ``Bool.false
            && !b.isAppOfArity ``Decidable.decide 2 && b.hasFVar then
          acc.modify (·.push (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)))
      for a in e.getAppArgs do go a
      go e.getAppFn
    -- a boolean variable on its own (`#returned`, a flag) is a condition too
    | .fvar _ =>
      if (← inferType e).isConstOf ``Bool then
        acc.modify (·.push (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e (mkConst ``Bool.true)))
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

open Lean Elab Tactic Meta in
/-- **`gabbro_cases n [lemmas]` -- the program's control flow, as a case split.** For
    every condition the goal still holds as `decide p`, `p` or `¬ p`, and the branch is
    taken; at most `n` splits deep, because every split doubles the goals. This is the
    split a person would write by hand before every `if` of the body; which branch holds
    what is their logic, that the split stands before it is not. -/
syntax "gabbro_cases" num "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_cases $n:num [$ts,*]) => do
  let depth := n.getNat
  if depth == 0 then return
  let g ← getMainGoal
  let ps ← g.withContext do
    let all ← GabbroMeta.collectDecides (← instantiateMVars (← g.getType))
    -- a condition already decided by a hypothesis (`p` or `¬ p`) is not split again --
    -- that is what bounds the recursion
    let lctx ← getLCtx
    all.filterM fun p => do
      let np := mkNot p
      -- `¬ a < b` reads, once `simp_all` has been over it, as `b ≤ a` -- and `¬ a ≤ b`
      -- as `b < a`: the normalised form of the other branch decides the condition too
      let flipped : Option Lean.Expr ←
        try
          if p.isAppOfArity ``LT.lt 4 then
            let a := p.getAppArgs
            pure (some (← mkAppM ``LE.le #[a[3]!, a[2]!]))
          else if p.isAppOfArity ``LE.le 4 then
            let a := p.getAppArgs
            pure (some (← mkAppM ``LT.lt #[a[3]!, a[2]!]))
          else pure none
        catch _ => pure none
      let decided ← lctx.anyM fun d => do
        if d.isImplementationDetail then return false
        let ty ← instantiateMVars d.type
        if (← isDefEq ty p) || (← isDefEq ty np) then return true
        match flipped with
        | some f => isDefEq ty f
        | none => return false
      return !decided
  if ps.isEmpty then return
  let p := ps[0]!
  let pstx ← g.withContext do Term.exprToSyntax p
  let hn := mkIdent (← mkFreshUserName `hcase)
  evalTactic (← `(tactic| by_cases $hn : $pstx))
  -- the decision itself, as an equation of the `Bool` the program reads: `decide p =
  -- true` / `= false` -- stated, not left to `simp` to see through the instance (measured
  -- 2026-09-08, `58`: a `¬ x < y` in the context and a `decide (x < y)` in the goal, and
  -- the goal stood)
  evalTactic (← `(tactic| all_goals (try simp only [decide_eq_true $hn:ident])))
  evalTactic (← `(tactic| all_goals (try simp only [decide_eq_false $hn:ident])))
  -- the branch is taken cheaply: the condition rewritten, closed decisions evaluated,
  -- the `match` on the outcome reduced -- the model's full simp set runs once, later
  evalTactic (← `(tactic| all_goals (try simp only
    [$hn:ident, $ts,*, Gabbro.Body.bindLocal, Gabbro.Body.bindAll, Gabbro.Body.eval,
     Bool.not_eq_true,
     decide_true, decide_false, decide_eq_true_eq, decide_eq_false_iff_not, decide_not,
     eq_self_iff_true, Bool.not_true, Bool.not_false, Bool.true_and, Bool.and_true,
     Bool.false_and, Bool.and_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, if_true, if_false, not_false_eq_true, not_true_eq_false])))
  let n' := Syntax.mkNumLit (toString (depth - 1))
  evalTactic (← `(tactic| all_goals (try gabbro_cases $n' [$ts,*])))

open Lean Elab Tactic Meta in
/-- **`gabbro_try n tac` runs `tac` under a budget of `n` thousand heartbeats, and where
    `tac` fails OR runs out of the budget the state is restored** -- the goal then goes to
    the next step, and at the end to the person, instead of the theorem going red. A plain
    `try` would not do: a heartbeat timeout is a runtime exception it does not catch, and a
    `set_option maxHeartbeats … in` inside a tactic block changes the options but not the
    limit the check reads (`Core.Context.maxHeartbeats`, measured 2026-09-07). -/
elab "gabbro_try " n:num tac:tactic : tactic => do
  let s ← saveState
  -- `n` is in the unit of the `maxHeartbeats` option (thousands of raw heartbeats)
  let budget := n.getNat * 1000 * 1000
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) <|
      Core.withCurrHeartbeats <| evalTactic tac)
    (fun _ => s.restore)

/-- Every `a.tdiv b` / `a.tmod b` (closed) in `e` -- `true` for a division. -/
partial def GabbroMeta.collectDivMod (e : Lean.Expr) (acc : Array (Bool × Lean.Expr × Lean.Expr)) :
    Array (Bool × Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectDivMod x a) (GabbroMeta.collectDivMod fn acc)
    if args.size == 2 && !args[0]!.hasLooseBVars && !args[1]!.hasLooseBVars then
      if fn.isConstOf ``Int.tdiv then acc.push (true, args[0]!, args[1]!)
      else if fn.isConstOf ``Int.tmod then acc.push (false, args[0]!, args[1]!)
      else acc
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectDivMod b acc
  | .letE _ _ v b _ => GabbroMeta.collectDivMod b (GabbroMeta.collectDivMod v acc)
  | .mdata _ b => GabbroMeta.collectDivMod b acc
  | .proj _ _ b => GabbroMeta.collectDivMod b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_divmod` -- the bounds of every truncated division and remainder in the goal.**
    `omega` reads `/` and `%` only by a literal; a `summe / n` over a variable `n` is opaque
    to it, and a declared range on the quotient (`0 ≤ summe / n ≤ 1000000`) was the person's.
    For every `a.tdiv b` and `a.tmod b` the goal mentions, the facts `0 ≤ a → 0 ≤ b → 0 ≤
    a.tdiv b`, `0 ≤ a → a.tdiv b ≤ a`, `0 ≤ a → 0 ≤ a.tmod b`, `0 < b → a.tmod b < b` are
    added where their premises are arithmetic the context already decides (`omega`); a fact
    whose premise is not is left out, not left open. -/
elab "gabbro_divmod" : tactic => do
  let g ← getMainGoal
  -- in the goal and in the hypotheses: a split condition (`hcase`) carries the term too
  let terms ← g.withContext do
    let mut acc := GabbroMeta.collectDivMod (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectDivMod (← instantiateMVars d.type) acc
    pure acc
  let close ← `(tactic| first | assumption | omega)
  -- each term once: the same quotient stands in the goal and in three hypotheses
  let terms := terms.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2.1 == t.2.1 && u.2.2 == t.2.2) then acc else acc.push t) #[]
  for (isDiv, a, b) in terms do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    let facts : Array (TSyntax `tactic) ←
      if isDiv then
        pure #[← `(tactic| have := @Int.tdiv_nonneg $as $bs ?_ ?_),
               ← `(tactic| have := Int.tdiv_le_self (a := $as) $bs ?_)]
      else
        pure #[← `(tactic| have := Int.tmod_nonneg (a := $as) $bs ?_),
               ← `(tactic| have := Int.tmod_lt_of_pos $as (b := $bs) ?_)]
    for f in facts do
      let saved ← saveState
      try
        GabbroMeta.haveClosed f close
      catch _ =>
        saved.restore

/-- Every closed `a * b` over `Int` in `e`. -/
partial def GabbroMeta.collectMul (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr)) :
    Array (Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectMul x a) (GabbroMeta.collectMul fn acc)
    if fn.isConstOf ``HMul.hMul && args.size == 6 && args[0]!.isConstOf ``Int
        && !args[4]!.hasLooseBVars && !args[5]!.hasLooseBVars then
      acc.push (args[4]!, args[5]!)
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectMul b acc
  | .letE _ _ v b _ => GabbroMeta.collectMul b (GabbroMeta.collectMul v acc)
  | .mdata _ b => GabbroMeta.collectMul b acc
  | .proj _ _ b => GabbroMeta.collectMul b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_mul` -- the bounds of every product in the goal.** `omega` is linear: a
    `versatz * faktor` over two variables is an atom to it, and the declared range of a sum
    that holds such a product (`basis + versatz * faktor ≤ 2^64 - 1`) -- the very arithmetic
    the checker decided over the operands' ranges -- was the person's. For every `a * b`
    the goal mentions: `0 ≤ a * b` where both factors are non-negative, and `a * b ≤ A * B`
    where the context bounds each factor by a literal (`a ≤ A`, `b ≤ B`) -- each fact only
    where `omega` closes its premises. -/
elab "gabbro_mul" : tactic => do
  let g ← getMainGoal
  let prods ← g.withContext do
    let mut acc := GabbroMeta.collectMul (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectMul (← instantiateMVars d.type) acc
    pure acc
  let close ← `(tactic| first | assumption | omega)
  -- the literal upper bound of `x` the context holds, if any: a hypothesis `x ≤ A`
  let upper (x : Lean.Expr) : TacticM (Option (TSyntax `term)) := do
    (← getMainGoal).withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if ty.isAppOfArity ``LE.le 4 && ty.getAppArgs[0]!.isConstOf ``Int then
          let a := ty.getAppArgs[2]!
          let b := ty.getAppArgs[3]!
          if (← isDefEq a x) && b.isAppOfArity ``OfNat.ofNat 3 then
            return some (← Term.exprToSyntax d.toExpr)
      return none
  let prods := prods.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2 == t.2) then acc else acc.push t) #[]
  for (a, b) in prods do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    let saved ← saveState
    try
      GabbroMeta.haveClosed (← `(tactic| have := @Int.mul_nonneg $as $bs ?_ ?_)) close
    catch _ => saved.restore
    if let (some ha, some hb) := (← upper a, ← upper b) then
      let saved ← saveState
      try
        GabbroMeta.haveClosed (← `(tactic| have := Int.mul_le_mul $ha $hb ?_ ?_)) close
      catch _ => saved.restore

open Lean Elab Tactic Meta in
/-- **`gabbro_values` -- a callee's answer of a shape the model does not carry, by cases.**
    A `let x = f(a) else (e) { … }` reads the answer as `match some v with | reason e => …
    | v => …`, and where `f`'s answer has no shape (a record value, a token) the promise
    only says `∃ v, r = some v`: the `match` stands on a variable. It is split by its
    constructors here -- each arm is one program path, and the other steps close them. -/
elab "gabbro_values" : tactic => do
  let g ← getMainGoal
  let vs ← g.withContext do
    let e ← instantiateMVars (← g.getType)
    let mut out : Array Lean.FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if d.type.isConstOf ``Gabbro.Body.Value && e.containsFVar d.fvarId then
        out := out.push d.fvarId
    pure out
  for v in vs.toList.take 2 do
    let vs ← (← getMainGoal).withContext do Term.exprToSyntax (mkFVar v)
    evalTactic (← `(tactic| all_goals (try cases $vs:term)))

open Lean.Parser.Tactic in
/-- **The pipeline** -- what `gabbro_auto` runs before it gives up on a goal: the model's
    simp set, the control-flow split, the composition over the calls, the well-typed world,
    the split on undecided reads, `simp_all`, and the arithmetic. Every step runs under its
    own budget (`gabbro_try`), so that no step can take the theorem down with it. -/
macro "gabbro_pipeline" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_try 300 (gabbro_simp [$ts,*]);
             gabbro_try 300 (all_goals (try gabbro_cases 4 [$ts,*]));
             gabbro_try 600 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 100 (all_goals (try gabbro_open_hyps));
             gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_forall [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 50 (all_goals (try (repeat' apply And.intro)));
             gabbro_try 50 (all_goals (try intros));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             -- the witnesses `gabbro_shape` opened are new conditions and new indices --
             -- and a branch opened by a call's answer may hold a call of its own
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_calls $t [$ts,*]));
             -- an answer without a shape, by its constructors -- and the call after it
             gabbro_try 100 (all_goals (try gabbro_values));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 100 (all_goals (try gabbro_values));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_forall [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 50 (all_goals (try (repeat' apply And.intro)));
             gabbro_try 50 (all_goals (try intros));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done)));
             gabbro_try 300 (all_goals (try (gabbro_split <;> (try intros) <;> (try (simp [$ts,*, *]; done)))));
             gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done)));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             -- a witness named twice (`x = x'`, a case name `"Kurz" = w`) is one name --
             -- and two case names for one value are a contradiction `simp_all` then sees
             gabbro_try 50 (all_goals (try subst_vars));
             -- from here on WITHOUT the caller's list: `simp_all` clears a hypothesis it
             -- has used up (`hall`), and a name in the list that is gone fails the step
             gabbro_try 600 (all_goals (try simp_all));
             -- what `simp_all` exposed: reads at the indices in play, stores at them,
             -- instances one binder further in -- twice, because each round opens the next
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             -- a store whose value a late witness names is well-typed by that witness
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             -- a condition a late witness made decidable (`narrow i to 0 ..< hinterlegt`
             -- reads a global whose witness came with `gabbro_shape`) is split here again
             gabbro_try 200 (all_goals (try gabbro_cases 3 []));
             gabbro_try 300 (all_goals (try simp_all));
             gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros))));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             gabbro_try 300 (all_goals (try simp_all));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros))));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             gabbro_try 300 (all_goals (try simp_all));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             -- the bounds of a division or remainder by a variable, then the arithmetic
             gabbro_try 100 (all_goals (try gabbro_divmod));
             gabbro_try 100 (all_goals (try gabbro_mul));
             gabbro_try 100 (all_goals (try gabbro_bits));
             gabbro_try 100 (all_goals (try omega))))


/-! ### The measuring copy of the pipeline (agent b, 2026-09-08)

    `gabbro_pipeline_b` is `gabbro_pipeline` with every step wrapped in `gabbro_timed`, which
    logs the step's wall time. It exists so that "which step burns the seconds" is a
    measurement and not a guess; nothing generated uses it, and it is never in a proof. -/

open Lean Elab Tactic in
/-- Run a tactic and log how long it took, under a name. -/
elab "gabbro_timed" nm:str tac:tactic : tactic => do
  let t0 ← IO.monoMsNow
  evalTactic tac
  let t1 ← IO.monoMsNow
  logInfo m!"GTIME {nm.getString} {t1 - t0}"

open Lean.Parser.Tactic in
macro "gabbro_pipeline_b" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_timed "s00" (gabbro_try 300 (gabbro_simp [$ts,*]));
             gabbro_timed "s01" (gabbro_try 300 (all_goals (try gabbro_cases 4 [$ts,*])));
             gabbro_timed "s02" (gabbro_try 600 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s03" (gabbro_try 100 (all_goals (try gabbro_open_hyps)));
             gabbro_timed "s04" (gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s05" (gabbro_try 300 (all_goals (try gabbro_forall [$ts,*])));
             gabbro_timed "s06" (gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s07" (gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*])));
             gabbro_timed "s08" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s09" (gabbro_try 50 (all_goals (try (repeat' apply And.intro))));
             gabbro_timed "s10" (gabbro_try 50 (all_goals (try intros)));
             gabbro_timed "s11" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s12" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             -- the witnesses `gabbro_shape` opened are new conditions and new indices --
             -- and a branch opened by a call's answer may hold a call of its own
             gabbro_timed "s13" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s14" (gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*])));
             gabbro_timed "s15" (gabbro_try 200 (all_goals (try gabbro_calls $t [$ts,*])));
             -- an answer without a shape, by its constructors -- and the call after it
             gabbro_timed "s16" (gabbro_try 100 (all_goals (try gabbro_values)));
             gabbro_timed "s17" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s18" (gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s19" (gabbro_try 100 (all_goals (try gabbro_values)));
             gabbro_timed "s20" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s21" (gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s22" (gabbro_try 200 (all_goals (try gabbro_forall [$ts,*])));
             gabbro_timed "s23" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s24" (gabbro_try 50 (all_goals (try (repeat' apply And.intro))));
             gabbro_timed "s25" (gabbro_try 50 (all_goals (try intros)));
             gabbro_timed "s26" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s27" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             gabbro_timed "s28" (gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done))));
             gabbro_timed "s29" (gabbro_try 300 (all_goals (try (gabbro_split <;> (try intros) <;> (try (simp [$ts,*, *]; done))))));
             gabbro_timed "s30" (gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done))));
             gabbro_timed "s31" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             -- a witness named twice (`x = x'`, a case name `"Kurz" = w`) is one name --
             -- and two case names for one value are a contradiction `simp_all` then sees
             gabbro_timed "s32" (gabbro_try 50 (all_goals (try subst_vars)));
             -- from here on WITHOUT the caller's list: `simp_all` clears a hypothesis it
             -- has used up (`hall`), and a name in the list that is gone fails the step
             gabbro_timed "s33" (gabbro_try 600 (all_goals (try simp_all)));
             -- what `simp_all` exposed: reads at the indices in play, stores at them,
             -- instances one binder further in -- twice, because each round opens the next
             gabbro_timed "s34" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             -- a store whose value a late witness names is well-typed by that witness
             gabbro_timed "s35" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             -- a condition a late witness made decidable (`narrow i to 0 ..< hinterlegt`
             -- reads a global whose witness came with `gabbro_shape`) is split here again
             gabbro_timed "s36" (gabbro_try 200 (all_goals (try gabbro_cases 3 [])));
             gabbro_timed "s37" (gabbro_try 300 (all_goals (try simp_all)));
             gabbro_timed "s38" (gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros)))));
             gabbro_timed "s39" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             gabbro_timed "s40" (gabbro_try 300 (all_goals (try simp_all)));
             gabbro_timed "s41" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             gabbro_timed "s42" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s43" (gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros)))));
             gabbro_timed "s44" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             gabbro_timed "s45" (gabbro_try 300 (all_goals (try simp_all)));
             gabbro_timed "s46" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             -- the bounds of a division or remainder by a variable, then the arithmetic
             gabbro_timed "s47" (gabbro_try 100 (all_goals (try gabbro_divmod)));
             gabbro_timed "s48" (gabbro_try 100 (all_goals (try gabbro_mul)));
             gabbro_timed "s49" (gabbro_try 100 (all_goals (try gabbro_bits)));
             gabbro_timed "s50" (gabbro_try 100 (all_goals (try omega)))))

open Lean.Parser.Tactic in
macro "gabbro_auto" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_pipeline [$ts,*] using $t; all_goals sorry))

open Lean.Parser.Tactic in
/-- `gabbro_auto?` -- the same, and it PRINTS what is left before the `sorry`. For a
    person who wants to see their own logic before writing it. -/
macro "gabbro_auto?" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_pipeline [$ts,*] using $t; trace_state; all_goals sorry))

namespace Gabbro.Body

/-! ## 8. Recursion INSIDE a loop -- the induction and the loop rule in one step
     (agent a, 2026-09-08)

    `contract_of_duty_rec` runs the induction over the `decreases` around the routine's
    BODY; `looprule_of_body_in` turns one pass of a loop into that loop's rule. A routine
    that calls itself from inside its own loop needs both at once, and the order matters:
    the loop rule has to be built INSIDE the induction, because the pass needs the bounded
    self-contract, and only the induction hands one down.

    **What the pass may assume, and what it owes for it.** It may assume `ContractBelow ρ f
    e s0 …` -- the routine's own contract on every state strictly below the ROUTINE'S ENTRY
    state `s0` in the measure. That is the only bound the induction has. But a loop rule is
    stated over an arbitrary pass state, and nothing ties that state to `s0` -- so the pass
    also owes that the measure has not moved: `eval t' e = eval s0 e`. It is carried across
    the passes as part of the loop's state predicate, exactly where `looprule_of_body_in`
    carries the well-typed world.

    **Why the second half is not decoration.** Without it a pass could lower the measure and
    then call the routine "below" a bound that no longer holds -- the assumption would be
    about a state the loop has left. With it, the bound the induction proved is the bound
    every pass still stands on.
-/

/-- **A contract holds below every state.** The one direction that is free: what holds for
    every state holds for the states below one. Used after the induction, to hand the loop
    its own rule under the plain well-typed world. -/
theorem contractBelow_of_contract (ρ : Env) (f : String) (e : Expr) (s : State)
    (pre : State → Prop) (post : State → State → Option Value → Prop)
    (h : Contract ρ f pre post) : ContractBelow ρ f e s pre post :=
  fun t' ht' _ => h t' ht'

/-- **The contract of a routine whose recursive call stands inside ONE ranged loop.**
    `hb` is the loop's pass, `hd` the routine's body; the induction over `e` and the
    induction over the passes are composed here once, so that no person writes either. -/
theorem contract_of_duty_rec_loop_in
    (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (wf : State → Prop)
    (id : String) (lbody : List Stmt) (v : String) (lo hi : Int) (inv : Expr)
    (hr : Runs ρ f body)
    (hl : RunsLoopIn ρ id lbody v lo hi)
    (hb : ∀ (s0 : State), pre s0 → ContractBelow ρ f e s0 pre post →
      ∀ (t : State) (k : Int), lo ≤ k → k < hi → wf t → eval t e = eval s0 e →
        eval t inv = some (.bool true) →
        ∃ t', finalState (exec ρ lbody { t with local' := bindLocal t.local' v (.int k) })
                = some t'
              ∧ (wf t' ∧ eval t' e = eval s0 e) ∧ eval t' inv = some (.bool true))
    (hd : ∀ t, pre t → ContractBelow ρ f e t pre post →
        LoopRule ρ id (fun u => wf u ∧ eval u e = eval t e) inv →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post :=
  contract_of_duty_rec ρ f body pre post e hr (fun t ht hcb =>
    hd t ht hcb
      (looprule_of_body_in ρ id (fun u => wf u ∧ eval u e = eval t e) inv lbody v lo hi hl
        (fun u k hlo hhi hu hiv => hb t ht hcb u k hlo hhi hu.1 hu.2 hiv)))


end Gabbro.Body
