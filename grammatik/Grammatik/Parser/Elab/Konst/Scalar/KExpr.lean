module
public import Grammatik.Parser.Elab.Konst.Scalar.Model
public import Grammatik.Kern.Syntax.Extensions.Zucker.Konstanten

@[expose] public section
namespace Gabbro.Grammatik.Konstanten

/-- Exact integer interpretation of the existing constant syntax. Unlike its historical
    natural-number table interpretation, subtraction retains negative integers. Bounds
    are checked by the typed G call and the canonical bounded candidate evaluator. -/
def KBinOp.evalInt : KBinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a.tdiv b
  | .mod, a, b => a.tmod b
  | .land, a, b => Int.ofNat (a.toNat &&& b.toNat)
  | .lor, a, b => Int.ofNat (a.toNat ||| b.toNat)
  | .xor, a, b => Int.ofNat (a.toNat ^^^ b.toNat)
  | .shl, a, b => a * 2 ^ b.toNat
  | .shr, a, b => a / 2 ^ b.toNat
  | .eq, a, b => if a == b then 1 else 0
  | .ne, a, b => if a != b then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .le, a, b => if a ≤ b then 1 else 0
  | .gt, a, b => if b < a then 1 else 0
  | .ge, a, b => if b ≤ a then 1 else 0
  | .and, a, b => if a == 0 || b == 0 then 0 else 1
  | .or, a, b => if a == 0 && b == 0 then 0 else 1

/-- Closed KExpr evaluation never supplies a default for an unresolved parameter,
    name or call. Quotation below closes typed parameters using the actual arguments. -/
def KExpr.evalInt : KExpr → Option Int
  | .lit n => some n
  | .una .not e => do
    let value ← e.evalInt
    pure (if value == 0 then 1 else 0)
  | .bin op a b => do
    pure (op.evalInt (← a.evalInt) (← b.evalInt))
  | .param | .konst _ | .ruf _ _ => none

/-- Exact signed literals are expressed using existing syntax; no constructor or
    natural-number interpretation changes are needed. -/
def KExpr.ofInt (value : Int) : KExpr :=
  if 0 ≤ value then .lit value.toNat
  else .bin .sub (.lit 0) (.lit (-value).toNat)

theorem KExpr.ofInt_eval (value : Int) : (KExpr.ofInt value).evalInt = some value := by
  unfold KExpr.ofInt
  split
  · rename_i h
    simp [KExpr.evalInt, Int.toNat_of_nonneg h]
  · rename_i h
    have hn : 0 ≤ -value := by omega
    simp [KExpr.evalInt, KBinOp.evalInt, Int.toNat_of_nonneg hn]

end Gabbro.Grammatik.Konstanten

namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Konstanten

/-- A closed constant expression together with its generic G denotation.
    This is indexed by the original typed body and arguments, never by a program name. -/
structure Quoted {D : Deklaration} {Γ : Ctx} {lo hi : Int}
    (args : Env D Γ) (body : Expr D Γ [] (.int lo hi)) where
  syntax : KExpr
  equation : ∀ before after,
    syntax.evalInt = some (eval before body after args).n

/-- Literal and parameter quotation retain exact signed values. -/
def quoteValue {D : Deklaration} {Γ : Ctx} {lo hi : Int}
    (args : Env D Γ) (body : Expr D Γ [] (.int lo hi)) (value : Int)
    (equation : ∀ before after, (eval before body after args).n = value) : Quoted args body :=
  ⟨KExpr.ofInt value, by intro before after; rw [equation, KExpr.ofInt_eval]⟩

/-- Generic KExpr-to-G denotation. Every certificate is produced by structural
    quotation, and the actual source replacement requires one. -/
theorem KExpr_to_G_denotation (quoted : Quoted args body) (before after : World D) :
    quoted.syntax.evalInt = some (eval before body after args).n :=
  quoted.equation before after

/-- Joint arithmetic witness, with a negative intermediate and exact value. -/
theorem KExpr_to_G_denotation_zeuge :
    let args : Env (declaration [] (.int (-10) 10)) [] := .nil
    let body : Expr (declaration [] (.int (-10) 10)) [] [] (.int (-3) (-3)) := .lit (-3)
    ∃ quoted : Quoted args body, quoted.syntax.evalInt = some (-3) := by
  dsimp only
  exact ⟨quoteValue .nil (.lit (-3)) (-3) (by intros; rfl), KExpr.ofInt_eval (-3)⟩

end Gabbro.Grammatik.Parser.Konst.Scalar
