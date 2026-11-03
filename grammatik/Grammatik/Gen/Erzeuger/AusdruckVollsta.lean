/-
  File:      Grammatik/Gen/Erzeuger/AusdruckVollst.lean
  Subject:   The COMPLETENESS of the expression clauses (`exprS_vollst`: an expression of size `k` is among the
             items of size `k`, given the expressions of the sizes below), the TABLE of the expressions of one
             context by size (`genE`), and its completeness (`genE_vollst`): every typed expression of size at
             most `n` is in the bucket of its size. The proof cases on the term; a constructor without a clause
             stops the build, so new syntax shows up as a gap by itself.
-/
module
public import Grammatik.Gen.Erzeuger.Ausdruck
@[expose] public section


namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}

/-- Every expression of size below `k` is in the stream, in the bucket of its size. -/
def Unter (E : Sz (SE D Γ Λ)) (k : Nat) : Prop :=
  ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e < k → (⟨τ, e⟩ : SE D Γ Λ) ∈ E (groesseExpr e)

/-- The oracle of the quantifier bodies holds every expression of size below `k`, at every context, for every
    bound that reaches its size. -/
def QUnter (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) (k : Nat) : Prop :=
  ∀ (n : Nat) (Γ' : Ctx) (τ : Ty) (e : Expr D Γ' Λ τ), groesseExpr e < k → groesseExpr e ≤ n →
    (⟨τ, e⟩ : SE D Γ' Λ) ∈ Q Γ' n (groesseExpr e)


/-- The expression of a sum payload. -/
def _root_.Gabbro.Grammatik.NutzlastExpr.teile {o : Option Ty} : NutzlastExpr D Γ Λ o → List (SE D Γ Λ)
  | .empty => []
  | .val e => [⟨_, e⟩]

/-- The immediate subexpressions of an expression in its own context (the quantifier bodies are in another one). -/
def _root_.Gabbro.Grammatik.Expr.teile {τ : Ty} : Expr D Γ Λ τ → List (SE D Γ Λ)
  | .slot _ _ i _ | .oldS _ _ i _ | .getBytes _ _ _ _ i _ _ _ => [⟨_, i⟩]
  | .thru p _ _ _ i _ => [⟨_, p⟩, ⟨_, i⟩]
  | .thruOwn p _ _ _ i _ _ _ _ _ _ => [⟨_, p⟩, ⟨_, i⟩]
  | .widen _ _ e | .some e | .istSome e => [⟨_, e⟩]
  | .neg a | .not a => [⟨_, a⟩]
  | .slotRef r _ _ _ _ _ => [⟨_, r⟩]
  | .refEq a b => [⟨_, a⟩, ⟨_, b⟩]
  | .add a b | .sub a b | .mul a b | .div _ _ a b | .rem _ _ a b | .sdiv _ a b | .srem _ a b
  | .band _ _ a b | .bor _ _ _ _ _ a b | .bxor _ _ _ _ _ a b | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b
  | .lt a b | .le a b | .eq a b | .fllt a b | .flle a b | .and a b | .or a b | .reaches _ _ _ a b _ => [⟨_, a⟩, ⟨_, b⟩]
  | .case _ _ nutz => nutz.teile
  | _ => []

/-- The quantifier body of an expression, with its context. -/
def _root_.Gabbro.Grammatik.Expr.qteil {τ : Ty} : Expr D Γ Λ τ → Option (Σ Γ' : Ctx, SE D Γ' Λ)
  | .forallSlots _ body _ | .existsSlots _ body _ => some ⟨_, ⟨_, body⟩⟩
  | _ => none

/-- The immediate subexpressions of `e` are in the stream, in the buckets of their sizes. -/
def TeileIn (E : Sz (SE D Γ Λ)) {τ : Ty} (e : Expr D Γ Λ τ) : Prop :=
  ∀ x ∈ e.teile, x ∈ E (groesseExpr x.2)

/-- The quantifier body of `e` is in the oracle, in the bucket of its size, for the bound of its size. -/
def QTeileIn (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) {τ : Ty} (e : Expr D Γ Λ τ) : Prop :=
  ∀ x ∈ e.qteil, x.2 ∈ Q x.1 (groesseExpr x.2.2) (groesseExpr x.2.2)

theorem nutz_teile_kleiner {o : Option Ty} (x : NutzlastExpr D Γ Λ o) :
    ∀ y ∈ x.teile, groesseExpr y.2 < groesseNutz x := by
  cases x <;> simp only [NutzlastExpr.teile, List.not_mem_nil, groesseNutz, Nat.lt_one_iff, false_implies, implies_true, List.mem_cons, or_false, forall_eq, Nat.lt_add_left_iff_pos, Nat.lt_add_one]

theorem teile_kleiner {τ : Ty} (e : Expr D Γ Λ τ) : ∀ x ∈ e.teile, groesseExpr x.2 < groesseExpr e := by
  cases e <;> simp only [Expr.teile, List.not_mem_nil, groesseExpr, false_implies, implies_true, Nat.lt_one_iff, List.mem_cons, or_false, forall_eq, Nat.lt_add_left_iff_pos, Nat.lt_add_one, forall_eq_or_imp, List.get_eq_getElem] <;> (try omega)
  case case nutz => intro x hx; have := nutz_teile_kleiner nutz x hx; omega

theorem qteil_kleiner {τ : Ty} (e : Expr D Γ Λ τ) : ∀ x ∈ e.qteil, groesseExpr x.2.2 < groesseExpr e := by
  cases e <;> simp only [Expr.qteil, Option.mem_def, reduceCtorEq, groesseExpr, false_implies, implies_true, Nat.lt_one_iff, List.get_eq_getElem, Option.some.injEq, forall_eq', Nat.lt_add_left_iff_pos, Nat.lt_add_one]

theorem teileIn_of {E : Sz (SE D Γ Λ)} {τ : Ty} {e : Expr D Γ Λ τ} (h : Unter E (groesseExpr e)) : TeileIn E e :=
  fun x hx => h x.1 x.2 (teile_kleiner e x hx)

theorem qteileIn_of {Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)} {τ : Ty} {e : Expr D Γ Λ τ}
    (h : QUnter Q (groesseExpr e)) : QTeileIn Q e :=
  fun x hx => h _ x.1 x.2.1 x.2.2 (qteil_kleiner e x hx) (Nat.le_refl _)

theorem mem_dif {P : Prop} [Decidable P] {α : Type} {g : P → α} (h : P) :
    g h ∈ (if h' : P then [g h'] else []) := by
  rw [dif_pos h]; simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem groesseExpr_pos {τ : Ty} (e : Expr D Γ Λ τ) : 1 ≤ groesseExpr e := by
  cases e <;> simp only [groesseExpr, unendlich] <;> omega

theorem mem_nutzS {E : Sz (SE D Γ Λ)} {o : Option Ty} (x : NutzlastExpr D Γ Λ o)
    (hE : ∀ y ∈ x.teile, y ∈ E (groesseExpr y.2)) : x ∈ nutzS E o (groesseNutz x) := by
  cases x with
  | empty => exact Sz.mem_blatt (by simp only [List.mem_cons, List.not_mem_nil, or_false])
  | val e =>
    simp only [groesseNutz]
    have he : (⟨_, e⟩ : SE D Γ Λ) ∈ E (groesseExpr e) := hE ⟨_, e⟩ (by simp only [NutzlastExpr.teile, List.mem_cons, List.not_mem_nil, or_false])
    have hm : NutzlastExpr.val e ∈ nutzS E (some _) (groesseExpr e + 1) :=
      Sz.mem_knoten (Sz.mem_map (f := NutzlastExpr.val) (mem_tyS he))
    exact Sz.mem_cast hm (by omega)

/-- Close `x ∈ exprS ...` from `hc : x ∈ clause k`. -/
macro "ausd " c:term ", " h:term : tactic =>
  `(tactic| exact Sz.mem_alle (c := $c) (by simp) $h)


end Gabbro.Grammatik.Gen
