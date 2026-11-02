module

public import Grammatik.Kern.Syntax.Konst.Programm
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section

namespace Gabbro.Grammatik

/-! ## Exact literals for certified const values.

   A certified const call (`ConstCallCertificate`) denotes a value; the
   call-site substitution replaces the call by a closed literal
   expression denoting the SAME value. `ConstLit` is that exactness
   relation: integers by widened `Int` literals (G literals are native
   `Int`, so no sign special case is needed here; the source-level
   negative form `.un "-" (.lit n)` is the surface spelling of the
   same value), booleans by `tru`/`fls`, options by `none`/`some`.
   Products, arrays, strings and every other shape are refused: the
   pipeline substitutes only integer calls, and anything else keeps
   the program refused rather than weakening the guarantee. -/

/-- A certified value represented exactly by a closed literal expression. -/
inductive ConstLit (c : ConstProgram) : {Γ : Ctx} → {τ : Ty} → Wert c.D τ → Expr c.D Γ [] τ → Prop where
  | intLit {Γ : Ctx} {lo hi : Int} (v : Zahl lo hi) :
      ConstLit c (τ := .int lo hi) v (.widen v.lo_le v.le_hi (.lit v.n))
  | boolTru {Γ : Ctx} : ConstLit c (τ := .bool) true .tru
  | boolFls {Γ : Ctx} : ConstLit c (τ := .bool) false .fls
  | optNone {Γ : Ctx} {n : Int} : ConstLit c (τ := .opt n) none (.none n)
  | optSome {Γ : Ctx} {n : Int} (v : Zahl 0 (n - 1)) :
      ConstLit c (τ := .opt n) (some v) (.some (.widen v.lo_le v.le_hi (.lit v.n)))

/-- A literal evaluates to exactly the value it represents. -/
theorem constLit_exact (c : ConstProgram) {Γ : Ctx} {τ : Ty} {v : Wert c.D τ} {e : Expr c.D Γ [] τ}
    (h : ConstLit c v e) (σ : World c.D) (ρ : Env c.D Γ) : eval σ e σ ρ = v := by
  cases h with
  | intLit v => cases v with | mk n h1 h2 => rfl
  | boolTru => rfl
  | boolFls => rfl
  | optNone => rfl
  | optSome v => cases v with | mk n h1 h2 => rfl

/-- Literals read nothing: their place list is empty, so binding or
    reading them appends no trace event. -/
theorem constLit_orte (c : ConstProgram) {Γ : Ctx} {τ : Ty} {v : Wert c.D τ} {e : Expr c.D Γ [] τ}
    (h : ConstLit c v e) : e.orte = [] := by
  cases h with
  | intLit v => simp only [Expr.orte]
  | boolTru => simp only [Expr.orte]
  | boolFls => simp only [Expr.orte]
  | optNone => simp only [Expr.orte]
  | optSome v => simp only [Expr.orte]

end Gabbro.Grammatik
