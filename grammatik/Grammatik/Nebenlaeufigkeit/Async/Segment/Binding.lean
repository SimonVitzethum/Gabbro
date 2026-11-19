module

public import Grammatik.Nebenlaeufigkeit.Async.GCost

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
  {Λ : List (Res D)} {τ storage : Ty}

@[expose] public def presentIndex (type : Ty) :
    Fin ([none, some type] : List (Option Ty)).length :=
  ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩

@[expose] public def presentValue (D : Deklaration) (type : Ty) (value : Wert D type) :
    Wert D (.sum [none, some type]) :=
  ⟨presentIndex type, value⟩

/-- Save into the exact declared optional frame field. Initialisation changes
    its tag to Present; all other saved fields are retained by prodSet. -/
@[expose] public def saveSlotExpr (types : TypeResolution) (f : AsyncFn)
    (frame : Expr D Γ Λ (frameType types f))
    (slot : FieldAt (frameFields types f) (.sum [none, some τ]))
    (value : Expr D Γ Λ τ) : Expr D Γ Λ (frameType types f) :=
  Expr.prodSet frame slot (Expr.case [none, some τ] (presentIndex τ) (NutzlastExpr.val value))

public theorem saveSlotExpr_eval (types : TypeResolution) (f : AsyncFn)
    (frame : Expr D Γ Λ (frameType types f))
    (slot : FieldAt (frameFields types f) (.sum [none, some τ]))
    (value : Expr D Γ Λ τ) (entry world : World D) (environment : Env D Γ) :
    eval entry (saveSlotExpr types f frame slot value) world environment =
      prodSetW (F := D.Fn) (passt := D.passt)
        (fs := frameFields types f)
        slot (eval entry frame world environment)
        (presentValue D τ (eval entry value world environment)) := rfl

/-- Bind the resolved source expression once, then construct the successor
    record from its value and the saved frame. The temporary binder is popped
    before control returns to the dispatcher. No expression is re-evaluated. -/
@[expose] public def evaluateBlock (expression : Expr D Γ Λ τ)
    (state : Var Γ storage) (successor : Expr D (τ :: Γ) Λ storage) :
    Block D V l Γ Λ Λ :=
  .bind expression (.cons (.assignVar (.there state) successor) .nil)

/-- Construction saves an initial child record and advances to its waiting
    phase using ordinary record expressions. It contains no child call. -/
@[expose] public def constructBlock (state : Var Γ storage)
    (successor : Expr D Γ Λ storage) : Block D V l Γ Λ Λ :=
  .cons (.assignVar state successor) .nil

/-- The precise ordinary expression transition, including G's read trace. -/
@[expose] public def evaluateExpression (expression : Expr D Γ Λ τ)
    (world : World D) (environment : Env D Γ) : Wert D τ × World D × Nat :=
  let read := world.lese Λ expression.orte
  (eval read expression read environment, read, kostenExpr expression)

/-- Exact G execution of an expression segment. The successor expression's
    reads are explicit too; generated record constructors should read only
    locals, but that fact is not silently assumed by this rule. -/
public theorem evaluateBlock_exec (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (expression : Expr D Γ Λ τ) (state : Var Γ storage)
    (successor : Expr D (τ :: Γ) Λ storage)
    (world : World D) (environment : Env D Γ) :
    (let read := world.lese Λ expression.orte
     let value := eval read expression read environment
     let after := read.lese Λ successor.orte
     execBlock O passes calls (evaluateBlock (V := V) (l := l) expression state successor) world environment =
       .ok after (environment.set state
         (eval after successor after (.cons value environment)))) := rfl

public theorem constructBlock_exec (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : Var Γ storage) (successor : Expr D Γ Λ storage)
    (world : World D) (environment : Env D Γ) :
    (let after := world.lese Λ successor.orte
     execBlock O passes calls (constructBlock (V := V) (l := l) state successor) world environment =
       .ok after (environment.set state (eval after successor after environment))) := rfl

public theorem evaluateBlock_cost (calls : D.Fn → Nat) (passes : Nat)
    (expression : Expr D Γ Λ τ) (state : Var Γ storage)
    (successor : Expr D (τ :: Γ) Λ storage) :
    kostenBlock 0 calls passes (evaluateBlock (V := V) (l := l) expression state successor) =
      2 + kostenExpr expression + (1 + kostenExpr successor + 1) := rfl

public theorem constructBlock_cost (calls : D.Fn → Nat) (passes : Nat)
    (state : Var Γ storage) (successor : Expr D Γ Λ storage) :
    kostenBlock 0 calls passes (constructBlock (V := V) (l := l) state successor) =
      1 + kostenExpr successor + 1 := rfl

public theorem evaluateBlock_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (expression : Expr D Γ Λ τ) (state : Var Γ storage)
    (successor : Expr D (τ :: Γ) Λ storage) :
    rufeB direct indirect forever
      (evaluateBlock (V := V) (l := l) expression state successor) = true := rfl

public theorem constructBlock_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (state : Var Γ storage) (successor : Expr D Γ Λ storage) :
    rufeB direct indirect forever (constructBlock (V := V) (l := l) state successor) = true := rfl

end Gabbro.Grammatik.Async.Segment
