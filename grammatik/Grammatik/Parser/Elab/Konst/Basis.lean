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
  | var {name : String} {mutable : Bool} {τ : Ty} {x : Var Γ τ}
      (found : (name, mutable, (⟨τ, x⟩ : Sigma fun τ => Var Γ τ)) ∈ locals) :
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
  | var => exact .pureVar
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

end Gabbro.Grammatik.Parser
