/-
  File:      Grammatik/X86/InvariantenOpt.lean
  Subject:   Invariant-derived optimisation legality over ACTUAL source semantics.

  This file states and proves generic optimisation legality rules against the
  real typed source language (`Syntax.lean`: `Expr`/`Block`/`Stmt`) and its
  real world semantics (`Semantik.lean`: `eval`/`execBlock`/`execStmt`), for
  consumption by the later IR/certificate lane. No toy model: every rewrite
  is an executable function on source syntax, every correspondence a theorem
  over `eval`/`execBlock` with real table-writing witnesses.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86.InvariantenOpt

variable {D : Deklaration} {V : Vertrag D}
variable {Γ : Ctx} {Λ : List (Res D)}

/-- Literal extractor at GENERAL type: `some n` for `lit n`, `none`
    otherwise. Generalising the index is load-bearing: `cases` on a
    specific `.int lo hi` fails where declaration indices (`gtyp`, `typ`)
    leave unification stuck, while a free index unifies with every arm. -/
def alsLitOpt {τ : Ty} : Expr D Γ Λ τ → Option Int
  | .lit n => some n
  | _ => none

/-- Non-recursive literal-inequality test: no termination issue, no trust. -/
def litLeBool {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) : Bool :=
  match alsLitOpt a, alsLitOpt b with
  | some x, some y => decide (x ≤ y)
  | _, _ => false

/-- Non-recursive literal-equality test. -/
def litEqBool {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) : Bool :=
  match alsLitOpt a, alsLitOpt b with
  | some x, some y => decide (x = y)
  | _, _ => false

/-- A computable truth check for boolean source conditions: `wahr`,
    literal comparisons, and boolean combinations. A later certificate
    checker re-runs exactly this `Bool`; nothing is trusted from Rust.
    Top-level patterns only (the `Expr.orte` precedent), so the recursion
    is structural over direct subterms. -/
def isWahrAll : Expr D Γ Λ τ → Bool
  | .wahr => true
  | .le a b => litLeBool a b
  | .eq a b => litEqBool a b
  | .und a b => isWahrAll a && isWahrAll b
  | .oder a b => isWahrAll a || isWahrAll b
  | .nicht a => !isWahrAll a
  | _ => false

/-- What "the checker says true" means at ANY type: a true boolean value,
    and `False` elsewhere, so the soundness induction generalises over the
    type index (which fixed-`.bool` induction cannot). -/
def holdsBool (τ : Ty) (v : Wert D τ) : Prop :=
  match τ with
  | .bool => v = true
  | _ => False

def isWahr (c : Expr D Γ Λ .bool) : Bool := isWahrAll c

/-- Match inversion for the extractor: a successful extraction exhibits
    the literal, with its index equation. Proved by `cases` at the free
    index (where every arm unifies); each non-literal arm reduces the
    hypothesis to `False` definitionally. -/
theorem alsLitOpt_lit {τ : Ty} (e : Expr D Γ Λ τ) (y : Int)
    (h : alsLitOpt e = some y) :
    ∃ n : Int, ∃ hτ : τ = Ty.int n n, hτ ▸ e = Expr.lit n ∧ n = y := by
  revert h
  cases e
  case lit n =>
    intro h
    exact ⟨n, rfl, rfl, by simpa [alsLitOpt] using h⟩
  all_goals (intro h; simp_all [alsLitOpt])

/-- An extracted literal really is the value `eval` computes. -/
theorem eval_alsLit {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (x : Int)
    (σ₀ σ : World D) (ρ : Env D Γ) (h : alsLitOpt e = some x) :
    (eval σ₀ e σ ρ).n = x := by
  obtain ⟨n, hτ, he, hn⟩ := alsLitOpt_lit e x h
  subst hn
  injection hτ with hlo hhi
  have hlo' : n = lo := hlo.symm
  have hhi' : n = hi := hhi.symm
  subst hlo'
  subst hhi'
  cases hτ
  have heq : e = @Expr.lit D Γ Λ n := he
  subst heq
  rfl

/-- A successful literal-inequality check means the real `le` evaluates true. -/
theorem litLeBool_sound {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : litLeBool a b = true) : wahr? (eval σ₀ (.le a b) σ ρ) = true := by
  unfold litLeBool at h
  cases ha : alsLitOpt a with
  | none => simp [ha] at h
  | some x =>
    cases hb : alsLitOpt b with
    | none => simp [ha, hb] at h
    | some y =>
      simp only [ha, hb] at h
      have e1 : (eval σ₀ a σ ρ).n = x := eval_alsLit a x σ₀ σ ρ ha
      have e2 : (eval σ₀ b σ ρ).n = y := eval_alsLit b y σ₀ σ ρ hb
      have hdec : wahr? (eval σ₀ (.le a b) σ ρ) = decide (x ≤ y) := by
        simp only [eval, wahr?, e1, e2]
      rw [hdec]; exact h

/-- A successful literal-equality check means the real `eq` evaluates true. -/
theorem litEqBool_sound {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : litEqBool a b = true) : wahr? (eval σ₀ (.eq a b) σ ρ) = true := by
  unfold litEqBool at h
  cases hb : alsLitOpt b with
  | none =>
    cases ha : alsLitOpt a with
    | none => simp [ha, hb] at h
    | some _ => simp [ha, hb] at h
  | some y =>
    cases ha : alsLitOpt a with
    | none => simp [ha, hb] at h
    | some x =>
      simp only [ha, hb] at h
      have e1 : (eval σ₀ a σ ρ).n = x := eval_alsLit a x σ₀ σ ρ ha
      have e2 : (eval σ₀ b σ ρ).n = y := eval_alsLit b y σ₀ σ ρ hb
      have hdec : wahr? (eval σ₀ (.eq a b) σ ρ) = decide (x = y) := by
        simp only [eval, wahr?, e1, e2]
      rw [hdec]; exact h

/- CUTS:
   Only the computable check exists so far. Open: its soundness over `eval`;
   constant folding / `weiter` value lemmas; `pruefung`/`ite` elimination with
   exact trace transfer; the invariant-scoped rule (rest/sight/lock-move only,
   never inside a running writer or held section); the stability-gated
   redundant-load rule; cost/ghost-budget, call-log (`Folge`), fault and
   interleaving transfers; the non-degenerate table-writing witness.
-/

end Gabbro.Grammatik.X86.InvariantenOpt
