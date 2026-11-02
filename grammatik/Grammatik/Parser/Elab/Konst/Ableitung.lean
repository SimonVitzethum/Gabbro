module

public import Grammatik.Kern.Syntax.Konst.Rein
public import Grammatik.Parser.Item.ElementTief.Kopf.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Local names retain their mutability and exact typed context position. -/
abbrev ConstLocals (Γ : Ctx) := List (String × Bool × (Sigma fun τ => Var Γ τ))

/-- Structural expression provenance. No arbitrary pure-expression escape rule. -/
inductive ConstSourceExpr (c : ConstProgram) (locals : ConstLocals Γ) :
    SExpr → {τ : Ty} → Expr c.D Γ [] τ → Prop where
  | lit (n : Nat) : ConstSourceExpr c locals (.lit n) (.lit (Int.ofNat n))
  | tru : ConstSourceExpr c locals .tru .tru
  | fls : ConstSourceExpr c locals .fls .fls
  | variable (found : (name, mutable, ⟨τ, x⟩) ∈ locals) :
      ConstSourceExpr c locals (.variable name) (.var x)
  | neg : ConstSourceExpr c locals source e →
      ConstSourceExpr c locals (.un "-" source) (.neg e)
  | boolNot : ConstSourceExpr c locals source e →
      ConstSourceExpr c locals (.un "!" source) (.not e)
  | add : ConstSourceExpr c locals sa a → ConstSourceExpr c locals sb b →
      ConstSourceExpr c locals (.bin "+" sa sb) (.add a b)
  | sub : ConstSourceExpr c locals sa a → ConstSourceExpr c locals sb b →
      ConstSourceExpr c locals (.bin "-" sa sb) (.sub a b)
  | mul : ConstSourceExpr c locals sa a → ConstSourceExpr c locals sb b →
      ConstSourceExpr c locals (.bin "*" sa sb) (.mul a b)
  | boolAnd : ConstSourceExpr c locals sa a → ConstSourceExpr c locals sb b →
      ConstSourceExpr c locals (.bin "&&" sa sb) (.and a b)
  | boolOr : ConstSourceExpr c locals sa a → ConstSourceExpr c locals sb b →
      ConstSourceExpr c locals (.bin "||" sa sb) (.or a b)

 theorem ConstSourceExpr.rein (h : ConstSourceExpr c locals source e) : ConstExpr c e := by
  induction h with
  | lit => exact .pureLit
  | tru => exact .pureTru
  | fls => exact .pureFls
  | variable => exact .pureVar
  | neg _ ih => exact .pureNeg ih
  | boolNot _ ih => exact .pureNot ih
  | add _ _ ha hb => exact .pureAdd ha hb
  | sub _ _ ha hb => exact .pureSub ha hb
  | mul _ _ ha hb => exact .pureMul ha hb
  | boolAnd _ _ ha hb => exact .pureAnd ha hb
  | boolOr _ _ ha hb => exact .pureOr ha hb

/-- Return values preserve absence as well as presence of a source operand. -/
inductive ConstSourceResult (c : ConstProgram) (locals : ConstLocals Γ) :
    Option SExpr → {τ : Option Ty} → ErgExpr c.D Γ [] τ → Prop where
  | empty : ConstSourceResult c locals none .empty
  | val : ConstSourceExpr c locals source e →
      ConstSourceResult c locals (some source) (.val e)

 theorem ConstSourceResult.rein (h : ConstSourceResult c locals source value) :
    ConstResult c value := by
  cases h with
  | empty => exact .empty
  | val h => exact .val h.rein

/-- Extend lexical scope, preserving the positions of all outer locals. -/
def ConstLocals.extend (locals : ConstLocals Γ) (name : String) (mutable : Bool)
    (τ : Ty) : ConstLocals (τ :: Γ) :=
  (name, mutable, ⟨τ, .here⟩) :: locals.map (fun (n, m, ⟨t, x⟩) =>
    (n, m, ⟨t, .there x⟩))

/-- End-block provenance for returns and ordered mutable-local assignments.
    Unsupported forms have no derivation. -/
inductive ConstSourceEnd (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → SAnw → Endblock c.D V l Γ [] → Prop where
  | ret (value : ConstSourceResult c locals source e) :
      ConstSourceEnd c locals (.ret source) (.ret e h)
  | endRet (value : ConstSourceResult c locals source e) :
      ConstSourceEnd c locals (.block [] (some (SEnde.ret source))) (.ret e h)
  | set (found : (name, true, ⟨τ, x⟩) ∈ locals)
      (value : ConstSourceExpr c locals source e)
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals
        (.block (.set (.variable name) "=" source :: rest) ending)
        (.cons (.assignVar x e) body)
  | bind (value : ConstSourceExpr c locals source e)
      (tail : ConstSourceEnd c (locals.extend name mutable τ)
        (.block rest ending) body) :
      ConstSourceEnd c locals
        (.block (.bind mutable name none source :: rest) ending) (.bind e body)
  | condChain (condition : ConstSourceExpr c locals source test)
      (yesProof : ConstSourceEnd c locals yes yesBody)
      (tail : ConstSourceEnd c locals (.cond next branch chain fallback) noBody) :
      ConstSourceEnd c locals
        (.cond source yes (.elsif next branch :: chain) fallback)
        (.ite test yesBody noBody)
  | cond (condition : ConstSourceExpr c locals source test)
      (yesProof : ConstSourceEnd c locals yes yesBody)
      (noProof : ConstSourceEnd c locals no noBody) :
      ConstSourceEnd c locals (.cond source yes [] (some no)) (.ite test yesBody noBody)

 theorem ConstSourceEnd.rein (h : ConstSourceEnd c locals source body) :
    ConstEnd c body := by
  induction h with
  | ret value => exact .ret value.rein
  | endRet value => exact .ret value.rein
  | set _ value _ ih => exact .cons (.assignVar value.rein) ih
  | bind value _ ih => exact .bind value.rein ih
  | condChain condition _ _ hy hn => exact .ite condition.rein hy hn
  | cond condition _ _ hy hn => exact .ite condition.rein hy hn

/-- First source-signature slice: closed Boolean functions with absent clauses.
    More signatures require explicit typed parameter and clause derivations. -/
inductive ConstElaborates (items : List SItemTief) :
    {c : ConstProgram} → ConstScope c.D → SItemTief → (f : c.D.Fn) → Prop where
  | function {c : ConstProgram} {scope : ConstScope c.D} {sig : FnSig}
      {source : SAnw} {f : c.D.Fn}
      (member : SItemTief.fnT sig source ∈ items)
      (kind : sig.art = "const")
      (params : sig.params = []) (typedParams : c.D.params f = [])
      (result : sig.res = some (.atom "bool")) (typedResult : c.D.erg f = some .bool)
      (reasons : sig.fehler = none) (clauses : sig.klauseln = [])
      (resolved : (sig.name, c.sourceId f) ∈ scope.declarations)
      (requires : c.emptyEntry f ▸ c.P.requires f = .tru)
      (ensures : c.emptyExit f ▸ c.P.ensures f = .tru)
      (body : ConstSourceEnd c [] source (c.emptyEntry f ▸ c.P.rumpf f)) :
      ConstElaborates items scope (.fnT sig source) f

 theorem ConstElaborates.rein
    (h : ConstElaborates items (c := c) scope item f) :
    ConstEnd c (c.emptyEntry f ▸ c.P.rumpf f) := by
  cases h with
  | function _ _ _ _ _ _ _ _ _ _ _ body => exact body.rein

end Gabbro.Grammatik.Parser
