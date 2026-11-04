module

public import Grammatik.Parser.Elab.Konst.Ableitung

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- A direct call requires both resolved scope membership and source provenance. -/
structure ConstSourceCallee (items : List SItemTief) (c : ConstProgram)
    (scope : ConstScope c.D) (name : String) (f : c.D.Fn) : Prop where
  resolved : (name, c.sourceId f) ∈ scope.declarations
  derivation : ∃ item, ConstElaborates items scope item f

/-- Calls followed by an already derived end block, including result binding. -/
inductive ConstSourceCallEnd (items : List SItemTief) (c : ConstProgram)
    (scope : ConstScope c.D) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    ConstLocals Γ → SAnw → Endblock c.D V l Γ [] → Prop where
  | statement {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name : String} {f : c.D.Fn} {sources : List SExpr}
      {args : Args c.D Γ [] (c.D.params f)} {rest : List SAnw} {ending : Option SEnde}
      {body : Endblock c.D V l Γ []}
      (callee : ConstSourceCallee items c scope name f)
      (arguments : ConstSourceArgs c locals sources args)
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (resourceEq : nach c.D f [] = [])
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceCallEnd items c scope locals
        (.block (.call name sources :: rest) ending)
        (.cons (Eq.rec (motive := fun output _ => Stmt c.D V l Γ [] output)
          (Stmt.call (D := c.D) (V := V) (l := l) f args hp hr) resourceEq) body)
  | binding {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name binder : String} {mutable : Bool} {τ : Ty} {f : c.D.Fn}
      {sources : List SExpr} {args : Args c.D Γ [] (c.D.params f)}
      {rest : List SAnw} {ending : Option SEnde}
      (callee : ConstSourceCallee items c scope name f)
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
