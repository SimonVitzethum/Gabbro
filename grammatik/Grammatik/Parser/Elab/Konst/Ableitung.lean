module

public import Grammatik.Parser.Elab.Konst.Dispatch
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil9

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- Arguments retain source order and their exact canonical parameter types. -/
inductive ConstSourceArgs (c : ConstProgram) (locals : ConstLocals Γ) :
    List SExpr → {ts : List Ty} → Args c.D Γ [] ts → Prop where
  | empty : ConstSourceArgs c locals [] .nil
  | cons {τ : Ty} {ts : List Ty} {source : SExpr} {sources : List SExpr}
      {e : Expr c.D Γ [] τ} {args : Args c.D Γ [] ts} : ConstSourceExpr c locals source e → ConstSourceArgs c locals sources args →
      ConstSourceArgs c locals (source :: sources) (.cons e args)

 theorem ConstSourceArgs.rein (h : ConstSourceArgs c locals sources args) :
    ConstArgs c args := by
  induction h with
  | empty => exact .nil
  | cons v _ ih => exact .cons v.rein ih

/-- End-block provenance for returns and ordered mutable-local assignments.
    Unsupported forms have no derivation. -/
inductive ConstSourceEnd (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → SAnw → Endblock c.D V l Γ [] → Prop where
  | ret {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {source : Option SExpr} {e : ErgExpr c.D Γ [] V.erg} {h : ([] : List (Res c.D)).Perm V.ende}
      (value : ConstSourceResult c locals source e) :
      ConstSourceEnd c locals (.ret source) (.ret e h)
  | endRet {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {source : Option SExpr} {e : ErgExpr c.D Γ [] V.erg} {h : ([] : List (Res c.D)).Perm V.ende}
      (value : ConstSourceResult c locals source e) :
      ConstSourceEnd c locals (.block [] (some (SEnde.ret source))) (.ret e h)
  | set {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name : String} {τ : Ty} {x : Var Γ τ} {source : SExpr} {e : Expr c.D Γ [] τ}
      {rest : List SAnw} {ending : Option SEnde} {body : Endblock c.D V l Γ []}
      (found : (name, true, ⟨τ, x⟩) ∈ locals)
      (value : ConstSourceExpr c locals source e)
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals
        (.block (.set (.variable name) "=" source :: rest) ending)
        (.cons (.assignVar x e) body)
  | bind {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name : String} {mutable : Bool} {τ : Ty} {source : SExpr} {e : Expr c.D Γ [] τ}
      {rest : List SAnw} {ending : Option SEnde} {body : Endblock c.D V l (τ :: Γ) []}
      (value : ConstSourceExpr c locals source e)
      (tail : ConstSourceEnd c (locals.extend name mutable τ)
        (.block rest ending) body) :
      ConstSourceEnd c locals
        (.block (.bind mutable name none source :: rest) ending) (.bind e body)
  | condChain {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {source : SExpr} {test : Expr c.D Γ [] .bool} {yes : SAnw} {next : SExpr} {branch : SAnw} {chain : List SAnw}
      {fallback : Option SAnw} {yesBody noBody : Endblock c.D V l Γ []}
      (condition : ConstSourceExpr c locals source test)
      (yesProof : ConstSourceEnd c locals yes yesBody)
      (tail : ConstSourceEnd c locals (.cond next branch chain fallback) noBody) :
      ConstSourceEnd c locals
        (.cond source yes (.elsif next branch :: chain) fallback)
        (.ite test yesBody noBody)
  | cond {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {source : SExpr} {test : Expr c.D Γ [] .bool} {yes no : SAnw}
      {yesBody noBody : Endblock c.D V l Γ []}
      (condition : ConstSourceExpr c locals source test)
      (yesProof : ConstSourceEnd c locals yes yesBody)
      (noProof : ConstSourceEnd c locals no noBody) :
      ConstSourceEnd c locals (.cond source yes [] (some no)) (.ite test yesBody noBody)
  | dispatch {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {cs : List (Option Ty)} {e : Expr c.D Γ [] (.sum cs)} {source : SExpr}
      {sources : List SAnw} {branches : Arms c.D V l Γ [] [] cs}
      {rest : List SAnw} {ending : Option SEnde} {body : Endblock c.D V l Γ []}
      (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceTagArms c (V := V) (l := l) locals sources branches)
      (sumInfo : USum)
      (shape : sumInfo.spec = cs)
      (indices : ∀ i arm, sources[i]? = some arm →
        ∃ label binder armBody, arm = .arm label binder armBody ∧
          sumInfo.cases.findIdx? (fun entry => strEq entry.1 label) = some i)
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals (.block (.cases source sources :: rest) ending)
        (.cons (.onTag e branches) body)
  | option {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {n : Int} {e : Expr c.D Γ [] (.opt n)} {source : SExpr} {name : String}
      {yes no : SAnw} {p : Block c.D V l (Ty.index n :: Γ) [] []}
      {a : Block c.D V l Γ [] []} {rest : List SAnw} {ending : Option SEnde}
      {body : Endblock c.D V l Γ []}
      (value : ConstSourceExpr c locals source e)
      (present : ConstSourceBlock c (V := V) (l := l) (locals.extend name false (.index n)) yes p)
      (absent : ConstSourceBlock c (V := V) (l := l) locals no a)
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals
        (.block (.cases source [.arm "Some" (some name) yes, .arm "None" none no] :: rest) ending)
        (.cons (.onOption e p a) body)
  | reason {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {n : Nat} {e : Expr c.D Γ [] (.why n)} {source : SExpr}
      {sources : List SAnw} {branches : GrundArms c.D V l Γ [] [] n}
      {rest : List SAnw} {ending : Option SEnde} {body : Endblock c.D V l Γ []}
      (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceReasonArms c (V := V) (l := l) locals sources branches)
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals (.block (.cases source sources :: rest) ending)
        (.cons (.onWhy e branches) body)
  | binding {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name binder : String} {mutable : Bool} {τ : Ty} {f : c.D.Fn}
      {sources : List SExpr} {args : Args c.D Γ [] (c.D.params f)}
      {rest : List SAnw} {ending : Option SEnde}
      (scope : ConstScope c.D)
      (resolved : (name, c.sourceId f) ∈ scope.declarations)
      (arguments : ConstSourceArgs c locals sources args)
      (he : c.D.erg f = some τ)
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (resourceEq : nach c.D f [] = [])
      (body : Endblock c.D V l (τ :: Γ) (nach c.D f []))
      (tail : ConstSourceEnd c (locals.extend binder mutable τ)
        (.block rest ending) (resourceEq ▸ body)) :
      ConstSourceEnd c locals
        (.block (.bind mutable binder none (.call name sources) :: rest) ending)
        (.bindCall f args he hp hr body)
  | call {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ}
      {name : String} {f : c.D.Fn}
      {sources : List SExpr} {args : Args c.D Γ [] (c.D.params f)}
      {rest : List SAnw} {ending : Option SEnde}
      {body : Endblock c.D V l Γ []}
      (scope : ConstScope c.D)
      (resolved : (name, c.sourceId f) ∈ scope.declarations)
      (arguments : ConstSourceArgs c locals sources args)
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (resourceEq : nach c.D f [] = [])
      (tail : ConstSourceEnd c locals (.block rest ending) body) :
      ConstSourceEnd c locals (.block (.call name sources :: rest) ending)
        (.cons (resourceEq ▸ Stmt.call c.D V f args hp hr) body)

 theorem ConstSourceEnd.rein (h : ConstSourceEnd c locals source body) :
    ConstEnd c body := by
  induction h with
  | ret value => exact .ret value.rein
  | endRet value => exact .ret value.rein
  | set _ value _ ih => exact .cons (.assignVar value.rein) ih
  | bind value _ ih => exact .bind value.rein ih
  | condChain condition _ _ hy hn => exact .ite condition.rein hy hn
  | cond condition _ _ hy hn => exact .ite condition.rein hy hn
  | dispatch v a _ _ _ _ ih => exact .cons (.onTag v.rein a.rein) ih
  | option v p a _ ih => exact .cons (.onOption v.rein p.rein a.rein) ih
  | reason v a _ ih => exact .cons (.onWhy v.rein a.rein) ih
  | binding _ _ arguments he hp hr resourceEq body _ ih =>
      exact .bindCall _ _ he hp hr resourceEq body arguments.rein ih
  | call _ _ arguments hp hr resourceEq _ ih =>
      exact .cons (.call _ _ hp hr resourceEq arguments.rein) ih

/-- Resolved aliases preserve the complete canonical type, including aggregates. -/
inductive ConstSourceType (scope : ConstScope D) : STyp → Ty → Prop where
  | named (found : (name, τ) ∈ scope.aliases) :
      ConstSourceType scope (.atom name) τ
  | boolean : ConstSourceType scope (.atom "bool") .bool

/-- Parameter provenance also constructs the immutable lexical context. -/
inductive ConstSourceParams (scope : ConstScope D) :
    List (String × STyp) → (ts : List Ty) → ConstLocals ts → Prop where
  | empty : ConstSourceParams scope [] [] []
  | cons {name : String} {source : STyp} {τ : Ty}
      {sources : List (String × STyp)} {ts : List Ty} {locals : ConstLocals ts}
      (typed : ConstSourceType scope source τ)
      (tail : ConstSourceParams scope sources ts locals) :
      ConstSourceParams scope ((name, source) :: sources) (τ :: ts)
        (locals.extend name false τ)

/-- Result signatures determine the ensures scope, including the void case. -/
inductive ConstSourceSignatureResult (scope : ConstScope D) (locals : ConstLocals Γ) :
    Option STyp → (result : Option Ty) → ConstLocals (ErgCtx Γ result) → Prop where
  | empty : ConstSourceSignatureResult scope locals none none locals
  | value (typed : ConstSourceType scope source τ) :
      ConstSourceSignatureResult scope locals (some source) (some τ)
        (locals.extend "result" false τ)

/-- Only predicate clauses belong to this source slice. -/
inductive ConstSourceClauses (c : ConstProgram) (entry : ConstLocals Γ)
    (exitLocals : ConstLocals Δ) :
    List SKlausel → Expr c.D Γ [] .bool → Expr c.D Δ [] .bool → Prop where
  | empty : ConstSourceClauses c entry exitLocals [] .tru .tru
  | predicates (pre : ConstSourceExpr c entry sourcePre pre)
      (post : ConstSourceExpr c exitLocals sourcePost post) :
      ConstSourceClauses c entry exitLocals
        [.needs sourcePre, .gives sourcePost] pre post

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
  | general {c : ConstProgram} {scope : ConstScope c.D} {sig : FnSig}
      {source : SAnw} {f : c.D.Fn}
      {locals : ConstLocals (c.D.params f)}
      {exitLocals : ConstLocals (ErgCtx (c.D.params f) (c.D.erg f))}
      (member : SItemTief.fnT sig source ∈ items)
      (kind : sig.art = "const")
      (params : ConstSourceParams scope sig.params (c.D.params f) locals)
      (result : ConstSourceSignatureResult scope locals sig.res (c.D.erg f) exitLocals)
      (reasons : sig.fehler = none)
      (resolved : (sig.name, c.sourceId f) ∈ scope.declarations)
      (clauses : ConstSourceClauses c locals exitLocals sig.klauseln
        (c.emptyEntry f ▸ c.P.requires f) (c.emptyExit f ▸ c.P.ensures f))
      (body : ConstSourceEnd c locals source (c.emptyEntry f ▸ c.P.rumpf f)) :
      ConstElaborates items scope (.fnT sig source) f

 theorem ConstElaborates.rein
    (h : ConstElaborates items (c := c) scope item f) :
    ConstEnd c (c.emptyEntry f ▸ c.P.rumpf f) := by
  cases h with
  | function _ _ _ _ _ _ _ _ _ _ _ body => exact body.rein
  | general _ _ _ _ _ _ _ body => exact body.rein

end Gabbro.Grammatik.Parser
