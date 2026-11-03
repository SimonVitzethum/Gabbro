module
public import Grammatik.Parser.Elab.Konst.Scalar.KExpr

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Konstanten

/-- Composition of expression certificates, generic in the two operand intervals. -/
def quoteBinary {D : Deklaration} {Γ : Ctx} {la ha lb hb lo hi : Int}
    {args : Env D Γ} {a : Expr D Γ [] (.int la ha)} {b : Expr D Γ [] (.int lb hb)}
    (op : KBinOp) (left : Quoted args a) (right : Quoted args b)
    (body : Expr D Γ [] (.int lo hi))
    (meaning : ∀ before after, (eval before body after args).n =
      op.evalInt (eval before a after args).n (eval before b after args).n) : Quoted args body :=
  ⟨.bin op left.syntax right.syntax, by
    intro before after
    simp only [KExpr.evalInt, left.equation before after, right.equation before after]
    rw [meaning]
    rfl⟩

/-- Structural reification of the typed scalar body, at its actual checked arguments.
    Every recursive branch builds a denotation proof; the evaluator does not supply
    a guessed G literal. Unrepresented G forms retain a named refusal. -/
def quote {D : Deklaration} {Γ : Ctx} {lo hi : Int}
    (body : Expr D Γ [] (.int lo hi)) (args : Env D Γ) : Except String (Quoted args body) :=
  match body with
  | .lit value => .ok (quoteValue args (.lit value) value (by intros; rfl))
  | .var x => .ok (quoteValue args (.var x) (args.get x).n (by intros; rfl))
  | .widen hl hh value => do
    let quoted ← quote value args
    return ⟨quoted.syntax, by
      intro before after
      simpa only [eval, Zahl.weiter] using quoted.equation before after⟩
  | .neg value => do
    let quoted ← quote value args
    return ⟨.bin .sub (.lit 0) quoted.syntax, by
      intro before after
      simp only [KExpr.evalInt, quoted.equation before after]
      simp [KBinOp.evalInt, eval, Zahl.neg]⟩
  | .add a b => do
    return quoteBinary .add (← quote a args) (← quote b args) (.add a b) (by intros; rfl)
  | .sub a b => do
    return quoteBinary .sub (← quote a args) (← quote b args) (.sub a b) (by intros; rfl)
  | .mul a b => do
    return quoteBinary .mul (← quote a args) (← quote b args) (.mul a b) (by intros; rfl)
  | .div h0 h1 a b => do
    return quoteBinary .div (← quote a args) (← quote b args) (.div h0 h1 a b) (by intros; rfl)
  | .rem h0 h1 a b => do
    return quoteBinary .mod (← quote a args) (← quote b args) (.rem h0 h1 a b) (by intros; rfl)
  | .band h0 h1 a b => do
    return quoteBinary .land (← quote a args) (← quote b args) (.band h0 h1 a b) (by intros; rfl)
  | .bor w h0 h1 hw hw' a b => do
    return quoteBinary .lor (← quote a args) (← quote b args)
      (.bor w h0 h1 hw hw' a b) (by intros; rfl)
  | .bxor w h0 h1 hw hw' a b => do
    return quoteBinary .xor (← quote a args) (← quote b args)
      (.bxor w h0 h1 hw hw' a b) (by intros; rfl)
  | .shl w hw hw' h0 h1 a b => do
    return quoteBinary .shl (← quote a args) (← quote b args)
      (.shl w hw hw' h0 h1 a b) (by intros; rfl)
  | .shr w hw hw' h0 h1 a b => do
    return quoteBinary .shr (← quote a args) (← quote b args)
      (.shr w hw hw' h0 h1 a b) (by intros; rfl)
  | _ => .error "const KExpr quotation has no denotation rule for this G expression"

/-- Every successful quotation comes with the generic KExpr-to-G lemma. -/
theorem quote_denotes {D : Deklaration} {Γ : Ctx} {lo hi : Int}
    (body : Expr D Γ [] (.int lo hi)) (args : Env D Γ) (quoted : Quoted args body)
    (_ : quote body args = .ok quoted) (before after : World D) :
    quoted.syntax.evalInt = some (eval before body after args).n :=
  KExpr_to_G_denotation quoted before after

/-- The body, environment and quotation premises hold jointly on arithmetic with a parameter. -/
theorem quote_denotes_zeuge :
    let D := declaration [.int 0 10] (.int 0 20)
    let args : Env D [.int 0 10] := .cons ⟨3, by decide, by decide⟩ .nil
    let body : Expr D [.int 0 10] [] (.int 2 12) := .add (.var .here) (.lit 2)
    ∃ quoted : Quoted args body, quote body args = .ok quoted ∧
      quoted.syntax.evalInt = some 5 := by
  dsimp only
  let args : Env (declaration [.int 0 10] (.int 0 20)) [.int 0 10] :=
    .cons ⟨3, by decide, by decide⟩ .nil
  let body : Expr (declaration [.int 0 10] (.int 0 20)) [.int 0 10] [] (.int 2 12) :=
    .add (.var .here) (.lit 2)
  refine ⟨(quote body args).toOption.get (by decide), ?_, ?_⟩
  · rfl
  · rfl

end Gabbro.Grammatik.Parser.Konst.Scalar
