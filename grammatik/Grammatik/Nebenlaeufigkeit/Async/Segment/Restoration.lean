module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Binding

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
  {Λ : List (Res D)} {τ : Ty}

/-- A generated impossible arm uses an ordinary checked narrowing failure.
    It grants no value, permission, or successful continuation. -/
@[expose] public def rejectBlock (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ : List (Res D)) : Block D V l Γ Λ Λ :=
  Block.narrowRequired (Expr.lit 0) 1 1 Block.nil

public theorem rejectBlock_exec (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (environment : Env D Γ) :
    execBlock O passes calls (rejectBlock D V l Γ Λ) world environment =
      Ausgang.logik Logik.kapazitaet := by
  cases world
  rfl

/-- Restore one live saved local into the ordinary arm context. Composing
    these binders restores a whole live context; their scope ends at the arm.
    Missing storage is a logical failure, rather than an invented value. -/
@[expose] public def restoreSlot (saved : Expr D Γ Λ (.sum [none, some τ]))
    (body : Block D V l (τ :: Γ) Λ Λ) : Block D V l Γ Λ Λ :=
  Block.cons (Stmt.onTag saved
    (Arms.cons (rejectBlock D V l Γ Λ) (Arms.cons body Arms.nil))) Block.nil

@[expose] public def absentValue (D : Deklaration) (type : Ty) :
    Wert D (.sum [none, some type]) :=
  ⟨⟨0, Nat.zero_lt_succ 1⟩, ()⟩

/-- Successful restoration uses exactly the saved payload and records the
    normal expression reads before executing the continuation. -/
public theorem restoreSlot_present (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (saved : Expr D Γ Λ (.sum [none, some τ]))
    (body : Block D V l (τ :: Γ) Λ Λ)
    (world : World D) (environment : Env D Γ) (value : Wert D τ)
    (present : eval (world.lese Λ saved.orte) saved (world.lese Λ saved.orte) environment =
      presentValue D τ value) :
    execBlock O passes calls (restoreSlot saved body) world environment =
      (execBlock O passes calls body (world.lese Λ saved.orte)
        (Env.cons value environment)).schrumpf := by
  have selected : execStmt O passes calls (Stmt.onTag saved
      (Arms.cons (rejectBlock D V l Γ Λ) (Arms.cons body Arms.nil))) world environment =
      (execBlock O passes calls body (world.lese Λ saved.orte)
        (Env.cons value environment)).schrumpf := by
    change execArms O passes calls
        (Arms.cons (rejectBlock D V l Γ Λ) (Arms.cons body Arms.nil))
        (eval (world.lese Λ saved.orte) saved (world.lese Λ saved.orte) environment)
        (world.lese Λ saved.orte) environment = _
    rw [present]
    rfl
  unfold restoreSlot
  rw [execBlock, selected]
  cases execBlock O passes calls body (world.lese Λ saved.orte)
    (Env.cons value environment) <;> rfl

public theorem restoreSlot_absent (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (saved : Expr D Γ Λ (.sum [none, some τ]))
    (body : Block D V l (τ :: Γ) Λ Λ)
    (world : World D) (environment : Env D Γ)
    (absent : eval (world.lese Λ saved.orte) saved (world.lese Λ saved.orte) environment =
      absentValue D τ) :
    execBlock O passes calls (restoreSlot saved body) world environment =
      Ausgang.logik Logik.kapazitaet := by
  have selected : execStmt O passes calls (Stmt.onTag saved
      (Arms.cons (rejectBlock D V l Γ Λ) (Arms.cons body Arms.nil))) world environment =
      Ausgang.logik Logik.kapazitaet := by
    change execArms O passes calls
        (Arms.cons (rejectBlock D V l Γ Λ) (Arms.cons body Arms.nil))
        (eval (world.lese Λ saved.orte) saved (world.lese Λ saved.orte) environment)
        (world.lese Λ saved.orte) environment = _
    rw [absent]
    exact rejectBlock_exec O passes calls (world.lese Λ saved.orte) environment
  unfold restoreSlot
  rw [execBlock, selected]

/-- Restoration never introduces a call gate. -/
public theorem restoreSlot_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (saved : Expr D Γ Λ (.sum [none, some τ]))
    (body : Block D V l (τ :: Γ) Λ Λ) :
    rufeB direct indirect forever (restoreSlot saved body) =
      rufeB direct indirect forever body := by
  change ((true && (rufeB direct indirect forever body && true)) && true) = _
  cases rufeB direct indirect forever body <;> rfl

/-- The bound source value is read back into a genuine G variable. -/
@[expose] public def restoreBoolBody (D : Deklaration) (V : Vertrag D) (l : Bool) :
    Block D V l [.bool, .bool] [] [] :=
  Block.cons (Stmt.assignVar (Var.there Var.here) (Expr.var Var.here)) Block.nil

end Gabbro.Grammatik.Async.Segment
