/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Ausdruck.lean
  Subject:   The expressions ONE PER KEY. An expression is seen by the cells only through its type and the carriers it
             reads (`Expr.orte`), so the table of the expressions keeps, size after size, one expression per key
             (`genEK`), and every expression has a REPRESENTATIVE in it: same type, the same carriers read, not larger
             (`genEK_rep`). The proof replaces the parts of an expression by their representatives (`ersetzeE`, one
             case per constructor) and finds the result in the clause stream (`exprS_vollst`).
-/
import Grammatik.Gen.Erzeuger.AusdruckVollst
import Grammatik.Gen.Erzeuger.Entdoppelt
import Grammatik.Kern.Semantik.Semantik.T1
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T1

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}

/-- The carriers of the declaration, in a fixed order. -/
def traegerAlle : List (D.Tab ⊕ D.Glob) := (Aufz.tab (D := D)).map Sum.inl ++ (Aufz.glob (D := D)).map Sum.inr

theorem mem_traegerAlle (c : D.Tab ⊕ D.Glob) : c ∈ traegerAlle := by
  cases c with
  | inl t => exact List.mem_append_left _ (List.mem_map_of_mem (Aufz.tab_mem t))
  | inr g => exact List.mem_append_right _ (List.mem_map_of_mem (Aufz.glob_mem g))

/-- **The key of an expression**: its type and which carriers it reads. -/
def eSchl (x : SE D Γ Λ) : Ty × List Bool := (x.1, traegerAlle.map fun c => istIn x.2.orte c)

/-- `e'` stands for `e`: it reads the same carriers and is not larger. -/
structure GlE {τ : Ty} (e' e : Expr D Γ Λ τ) : Prop where
  orte : ∀ c, c ∈ e'.orte ↔ c ∈ e.orte
  groesse : groesseExpr e' ≤ groesseExpr e

theorem GlE.refl {τ : Ty} (e : Expr D Γ Λ τ) : GlE e e := ⟨fun _ => Iff.rfl, Nat.le_refl _⟩

theorem GlE.trans {τ : Ty} {a b c : Expr D Γ Λ τ} (h1 : GlE a b) (h2 : GlE b c) : GlE a c :=
  ⟨fun x => (h1.orte x).trans (h2.orte x), Nat.le_trans h1.groesse h2.groesse⟩

/-- Equal keys read the same carriers. -/
theorem orte_of_eSchl {τ : Ty} {e' e : Expr D Γ Λ τ} (h : eSchl (⟨τ, e'⟩ : SE D Γ Λ) = eSchl ⟨τ, e⟩) (c : D.Tab ⊕ D.Glob) :
    c ∈ e'.orte ↔ c ∈ e.orte := by
  have h2 := (List.map_inj_left.1 (Prod.mk.inj h).2) c (mem_traegerAlle c)
  rw [← istIn_iff, ← istIn_iff (l := e.orte), h2]

/-- The payload of a sum, its expression replaced by a representative. -/
theorem ersetzeN (P : SE D Γ Λ → Prop) {o : Option (Int × Int)} (x : NutzlastExpr D Γ Λ o)
    (h : ∀ y ∈ x.teile, ∃ y' : Expr D Γ Λ y.1, P ⟨y.1, y'⟩ ∧ GlE y' y.2) :
    ∃ x' : NutzlastExpr D Γ Λ o, (∀ c, c ∈ x'.orte ↔ c ∈ x.orte) ∧ groesseNutz x' ≤ groesseNutz x ∧
      ∀ y ∈ x'.teile, P y := by
  cases x with
  | empty => exact ⟨.empty, fun _ => Iff.rfl, Nat.le_refl _, by simp only [NutzlastExpr.teile, List.not_mem_nil, false_implies, implies_true]⟩
  | num e =>
    obtain ⟨e', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y e := h ⟨_, e⟩ (by simp only [NutzlastExpr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.num e', fun c => by simp only [NutzlastExpr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseNutz]; omega, by simp only [NutzlastExpr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1]⟩

set_option maxHeartbeats 4000000 in
/-- **Replacing the parts.** If every immediate part of `e` and its quantifier body have representatives satisfying
    `P` and `PQ`, then `e` has a representative whose parts satisfy them. -/
theorem ersetzeE (P : SE D Γ Λ → Prop) (PQ : (Σ Γ' : Ctx, SE D Γ' Λ) → Prop) {τ : Ty} (e : Expr D Γ Λ τ)
    (h : ∀ x ∈ e.teile, ∃ y : Expr D Γ Λ x.1, P ⟨x.1, y⟩ ∧ GlE y x.2)
    (hq : ∀ x ∈ e.qteil, ∃ y : Expr D x.1 Λ x.2.1, PQ ⟨x.1, ⟨x.2.1, y⟩⟩ ∧ GlE y x.2.2) :
    ∃ e' : Expr D Γ Λ τ, GlE e' e ∧ (∀ x ∈ e'.teile, P x) ∧ (∀ x ∈ e'.qteil, PQ x) := by
  cases e with
  | add a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.add a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | sub a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.sub a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | mul a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.mul a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | div h0 h1 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.div h0 h1 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | rem h0 h1 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.rem h0 h1 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | sdiv q0 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.sdiv q0 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | srem q0 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.srem q0 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | band h0 h1 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.band h0 h1 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | bor w h0 h1 h2 h3 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.bor w h0 h1 h2 h3 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | bxor w h0 h1 h2 h3 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.bxor w h0 h1 h2 h3 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | shl w h0 h1 h2 h3 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.shl w h0 h1 h2 h3 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | shr w h0 h1 h2 h3 a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.shr w h0 h1 h2 h3 a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | lt a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.lt a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | le a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.le a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | eq a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.int.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.eq a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | fllt a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.fl.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.fl.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.fllt a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | flle a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.fl.injEq, List.not_mem_nil, or_false, true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, Ty.fl.injEq, List.not_mem_nil, or_false, or_true])
    exact ⟨.flle a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | and a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  or_true])
    exact ⟨.and a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | or a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  or_true])
    exact ⟨.or a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | slot t f i hL =>
    obtain ⟨i', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y i := h ⟨_, i⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.slot t f i' hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | oldS t f i hL =>
    obtain ⟨i', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y i := h ⟨_, i⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.oldS t f i' hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | getBytes t f hf n i hlo hhi hL =>
    obtain ⟨i', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y i := h ⟨_, i⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.getBytes t f hf n i' hlo hhi hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | widen q1 q2 e =>
    obtain ⟨e', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y e := h ⟨_, e⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.widen q1 q2 e', ⟨fun c => by simp only [Expr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | neg a =>
    obtain ⟨a', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.neg a', ⟨fun c => by simp only [Expr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | not a =>
    obtain ⟨a', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.not a', ⟨fun c => by simp only [Expr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | some e =>
    obtain ⟨e', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y e := h ⟨_, e⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.some e', ⟨fun c => by simp only [Expr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | istSome e =>
    obtain ⟨e', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y e := h ⟨_, e⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.istSome e', ⟨fun c => by simp only [Expr.orte, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | thru p t ht f i hL =>
    obtain ⟨p', hp, gp⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y p := h ⟨_, p⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, false_and, List.not_mem_nil, or_self,
  or_false])
    obtain ⟨i', hi, gi⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y i := h ⟨_, i⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, false_and, List.not_mem_nil, or_false,
  or_true])
    exact ⟨.thru p' t ht f i' hL, ⟨fun c => by simp only [Expr.orte, List.mem_append, gp.orte c, List.mem_cons, gi.orte c],
      by have := gp.groesse; have := gi.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, hp, forall_eq, hi,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | refEq a b =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  or_true])
    exact ⟨.refEq a' b', ⟨fun c => by simp only [Expr.orte, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | slotRef r t ht ho f hL =>
    obtain ⟨r', h1, g1⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y r := h ⟨_, r⟩ (by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false])
    exact ⟨.slotRef r' t ht ho f hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, g1.orte c],
      by have := g1.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq, h1], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | reaches t f hf a b hL =>
    obtain ⟨a', ha, ga⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y a := h ⟨_, a⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  true_or])
    obtain ⟨b', hb, gb⟩ : ∃ y, P ⟨_, y⟩ ∧ GlE y b := h ⟨_, b⟩ (by simp only [Expr.teile, List.mem_cons, Sigma.mk.injEq, heq_eq_eq, true_and, List.not_mem_nil, or_false,
  or_true])
    exact ⟨.reaches t f hf a' b' hL, ⟨fun c => by simp only [Expr.orte, List.cons_append, List.mem_cons, List.mem_append, ga.orte c, gb.orte c],
      by have := ga.groesse; have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, ha, forall_eq, hb,
  and_self], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | case cs i nutz =>
    obtain ⟨n', g1, g2, h1⟩ := ersetzeN P nutz fun y hy => h y (by simpa [Expr.teile] using hy)
    exact ⟨.case cs i n', ⟨fun c => by simp only [Expr.orte, List.get_eq_getElem, g1 c], by simp only [groesseExpr]; omega⟩,
      by simpa [Expr.teile] using h1, by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩
  | forallSlots t body hL =>
    obtain ⟨b', hb, gb⟩ : ∃ y, PQ ⟨_, ⟨_, y⟩⟩ ∧ GlE y body := hq ⟨_, ⟨_, body⟩⟩ (by simp only [Expr.qteil, Option.mem_def])
    exact ⟨.forallSlots t b' hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, gb.orte c],
      by have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.not_mem_nil, false_implies, implies_true], by simpa [Expr.qteil] using hb⟩
  | existsSlots t body hL =>
    obtain ⟨b', hb, gb⟩ : ∃ y, PQ ⟨_, ⟨_, y⟩⟩ ∧ GlE y body := hq ⟨_, ⟨_, body⟩⟩ (by simp only [Expr.qteil, Option.mem_def])
    exact ⟨.existsSlots t b' hL, ⟨fun c => by simp only [Expr.orte, List.mem_cons, gb.orte c],
      by have := gb.groesse; simp only [groesseExpr]; omega⟩,
      by simp only [Expr.teile, List.not_mem_nil, false_implies, implies_true], by simpa [Expr.qteil] using hb⟩
  | _ => exact ⟨_, GlE.refl _, by simp only [Expr.teile, List.not_mem_nil, false_implies, implies_true], by simp only [Expr.qteil, Option.mem_def, reduceCtorEq, false_implies, implies_true]⟩

end Gabbro.Grammatik.Gen
