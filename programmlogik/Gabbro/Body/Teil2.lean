module

public import Lean
public import Gabbro.Body.Teil1

@[expose] public section

namespace Gabbro.Body

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
    | none => simp only [andBool, reduceCtorEq] at h
    | some v =>
      cases y with
      | none => simp only [andBool, reduceCtorEq] at h
      | some w =>
        cases v <;> cases w <;> simp only [andBool, reduceCtorEq, Option.some.injEq, Value.bool.injEq, Bool.and_eq_true] at h
        rename_i a b
        simp only [h.1, h.2, and_self]
  · intro ⟨hx, hy⟩
    simp only [hx, hy, andBool_some, Bool.and_self]

/-- **A disjunction that evaluates to true**: both halves are truth values, and one is true. -/
theorem orBool_true_iff (x y : Option Value) :
    orBool x y = some (.bool true)
      ↔ ∃ a b, x = some (.bool a) ∧ y = some (.bool b) ∧ (a || b) = true := by
  constructor
  · intro h
    cases x with
    | none => simp only [orBool, reduceCtorEq] at h
    | some v =>
      cases y with
      | none => simp only [orBool, reduceCtorEq] at h
      | some w =>
        cases v <;> cases w <;> simp only [orBool, reduceCtorEq, Option.some.injEq, Value.bool.injEq, Bool.or_eq_true] at h
        rename_i a b
        exact ⟨a, b, rfl, rfl, by simpa using h⟩
  · intro ⟨a, b, hx, hy, hab⟩
    simp only [hx, hy, orBool_some, hab]

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
  simp only [binop, ↓reduceIte, and_self]

/-- **A negative operand gets a bit operation stuck** -- all five of them, on either side.
    This is the refusal the model makes instead of guessing a width. -/
theorem a_negative_operand_stops_the_bits (a : Int) (h : a < 0) :
    binop .band (.int a) (.int 1) = none ∧ binop .band (.int 1) (.int a) = none
    ∧ binop .bor (.int a) (.int 1) = none ∧ binop .bxor (.int a) (.int 1) = none
    ∧ binop .shl (.int a) (.int 1) = none ∧ binop .shr (.int a) (.int 1) = none
    ∧ binop .shl (.int 1) (.int a) = none ∧ binop .shr (.int 1) (.int a) = none := by
  simp only [binop, bits, Int.not_le.mpr h, Int.zero_le_ofNat, and_true, ↓reduceIte, and_false, and_self]

/-- **The shifts are a multiplication and a division**, under the guard and under the `M104`
    booking the arm names. Stated in general and not on an example, because it is the claim
    the booking rests on. -/
theorem a_shift_is_arithmetic (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    binop .shl (.int a) (.int b) = some (.int (a * 2 ^ b.toNat))
    ∧ binop .shr (.int a) (.int b) = some (.int (a.tdiv (2 ^ b.toNat))) := by
  simp only [binop, ha, hb, and_self, ↓reduceIte]

/-- **Where a mask answers at all, it answers with a non-negative number.** That is the
    half of the width-independence claim this file can state on its own; that the result
    also fits the DECLARED range is `M104`'s half, and `typen::bitweise` computes it. -/
theorem a_mask_stays_non_negative (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ n : Nat, binop .band (.int a) (.int b) = some (.int (n : Int)) := by
  exact ⟨a.toNat &&& b.toNat, by simp only [binop, bits, ha, hb, and_self, ↓reduceIte]⟩

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
  | zero => rw [chase_zero]; simp only [decide_true]
  | succ n => rw [chase_succ]; simp only [↓reduceIte]

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
    · simp only [hk, ↓reduceIte]
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
  | zero => simp only [allBelow_zero, Nat.not_lt_zero, false_implies, implies_true]
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
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
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
        | zero => exact ⟨false, by simp only [anyBelow_zero]⟩
        | succ m ihm =>
          obtain ⟨a, ha⟩ := ihm (fun j hj => hall j (Nat.lt_succ_of_lt hj))
          obtain ⟨c, hc⟩ := hall m (Nat.lt_succ_of_lt (Nat.lt_succ_self m))
          exact ⟨a || c, by rw [anyBelow_succ, ha, hc]⟩
      obtain ⟨a, ha⟩ := this
      rw [anyBelow_succ, ha, h]
      simp only [Bool.or_true]

/-- The chain as a relation -- `hier`/`hoeher`, the same two rules `Table_Ops_Erhaltung.thy`
    calls `ueber`. -/
inductive Reaches (σ : World) (c via : String) : Int → Int → Prop
  | here (k : Int) : Reaches σ c via k k
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
    subst h; exact .here k
  | succ n ih =>
    intro k h
    rw [chase_succ] at h
    split at h
    · rename_i hk; subst hk; exact .here k
    · split at h
      · rename_i m hm; exact .hoeher k m to hm (ih m h)
      · simp only [Option.some.injEq, Value.bool.injEq, Bool.false_eq_true] at h
      · simp only [reduceCtorEq] at h

/-- **And a real chain is found with enough fuel** -- one unit per edge. -/
theorem chase_of_reaches (σ : World) (c via : String) (k to : Int)
    (r : Reaches σ c via k to) : ∃ n, chase σ c via to k n = some (.bool true) := by
  induction r with
  | here k => exact ⟨0, by rw [chase_zero]; simp only [decide_true]⟩
  | hoeher k m n h _ ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨f + 1, ?_⟩
    rw [chase_succ]
    split
    · rfl
    · simp only [h, hf]

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
  simp only [eval, Option.some.injEq, Value.bool.injEq]

theorem shape_int (s : State) (n : String) (h : eval s (.hasShape n .int) = some (.bool true)) :
    ∃ k, s.local' n = .int k := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp only [Value.hasShape, hv, Value.int.injEq, exists_eq', Bool.false_eq_true] at h ⊢

/-- A local of a ranged type: its witness and its bounds. -/
theorem shape_intIn (s : State) (n : String) (lo hi : Int)
    (h : eval s (.hasShape n (.intIn lo hi)) = some (.bool true)) :
    ∃ k, s.local' n = .int k ∧ lo ≤ k ∧ k ≤ hi := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp only [Value.hasShape, hv, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq, exists_eq_left', Bool.false_eq_true] at h ⊢
  exact h

theorem shape_bool (s : State) (n : String) (h : eval s (.hasShape n .bool) = some (.bool true)) :
    ∃ b, s.local' n = .bool b := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp only [Value.hasShape, hv, Bool.false_eq_true, Value.bool.injEq, exists_eq'] at h ⊢

theorem shape_opt (s : State) (n : String) (h : eval s (.hasShape n .opt) = some (.bool true)) :
    s.local' n = .absent ∨ ∃ k, s.local' n = .present k := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp only [Value.hasShape, hv, Bool.false_eq_true, reduceCtorEq, exists_const, or_false, Value.present.injEq, exists_eq', or_true] at h ⊢

theorem shape_sum (s : State) (n : String) (cs : List (String × Option (Option (Int × Int))))
    (h : eval s (.hasShape n (.sum cs)) = some (.bool true)) :
    ∃ t p, s.local' n = .tagged t p ∧ Shape.caseOk cs t p = true := by
  simp only [eval, Option.some.injEq, Value.bool.injEq] at h
  cases hv : s.local' n <;> simp only [Value.hasShape, hv, Bool.false_eq_true, Value.tagged.injEq] at h ⊢
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
  simp only [eval, hk, binop, Option.some.injEq, Value.bool.injEq, decide_eq_true_eq] at hlo hhi
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

end Gabbro.Body
