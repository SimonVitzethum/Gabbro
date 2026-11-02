module

public import Grammatik.Parser.Elab.Konst.Dispatch

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Arguments retain source order and their exact canonical parameter types. -/
inductive ConstSourceArgs (c : ConstProgram) (locals : ConstLocals Γ) :
    List SExpr → {ts : List Ty} → Args c.D Γ [] ts → Prop where
  | empty : ConstSourceArgs c locals [] .nil
  | cons : ConstSourceExpr c locals source e → ConstSourceArgs c locals sources args →
      ConstSourceArgs c locals (source :: sources) (.cons e args)

 theorem ConstSourceArgs.rein (h : ConstSourceArgs c locals sources args) :
    ConstArgs c args := by
  induction h with
  | empty => exact .nil
  | cons v _ ih => exact .cons v.rein ih

/-- A direct call requires both resolved scope membership and source provenance. -/
structure ConstSourceCallee (items : List SItemTief) (c : ConstProgram)
    (scope : ConstScope c.D) (name : String) (f : c.D.Fn) : Prop where
  resolved : (name, c.sourceId f) ∈ scope.declarations
  item : SItemTief
  derivation : ConstElaborates items scope item f

/-- Calls followed by an already derived end block, including result binding. -/
inductive ConstSourceCallEnd (items : List SItemTief) (c : ConstProgram)
    (scope : ConstScope c.D) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    ConstLocals Γ → SAnw → Endblock c.D V l Γ [] → Prop where
  | statement (callee : ConstSourceCallee items c scope name f)
      (arguments : ConstSourceArgs c locals sources args)
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (resourceEq : nach c.D f [] = [])
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceCallEnd items c scope locals
        (.block (.call name sources :: rest) ending)
        (.cons (resourceEq ▸ Stmt.call c.D V f args hp hr) body)
  | binding (callee : ConstSourceCallee items c scope name f)
      (arguments : ConstSourceArgs c locals sources args)
      (he : c.D.erg f = some τ)
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (resourceEq : nach c.D f [] = [])
      (body : Endblock c.D V l (τ :: Γ) (nach c.D f []))
      (tail : ConstSourceEnd c (locals.extend binder mutable τ)
        (.block rest ending) (resourceEq ▸ body)) :
      ConstSourceCallEnd items c scope locals
        (.block (.bind mutable binder none (.call name sources) :: rest) ending)
        (.bindCall f args he hp hr body)

 theorem ConstSourceCallEnd.rein
    (h : ConstSourceCallEnd items c scope locals source body) : ConstEnd c body := by
  cases h with
  | statement _ arguments hp hr resourceEq tail =>
      exact .cons (.call _ _ hp hr resourceEq arguments.rein) tail.rein
  | binding _ arguments he hp hr resourceEq body tail =>
      exact .bindCall _ _ he hp hr resourceEq body arguments.rein tail.rein

end Gabbro.Grammatik.Parser
