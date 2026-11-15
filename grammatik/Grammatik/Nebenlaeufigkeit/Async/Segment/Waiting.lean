module

public import Grammatik.Nebenlaeufigkeit.Async.Segment.Binding

namespace Gabbro.Grammatik.Async.Segment

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
  {Λ : List (Res D)} {cases : List (Option Ty)}

/-- Call the resolved child's generated poll directly, then dispatch its
    answer. The Pending arm must save the returned child record; the Ready
    arm saves the result and advances. Arms see both the poll answer and its
    selected payload. Resource changes are those of the real call signature. -/
@[expose] public def waitingBlock (childPoll : D.Fn)
    (arguments : Args D Γ Λ (D.params childPoll))
    (resultType : D.erg childPoll = some (.sum cases))
    (contract : RufPasst D V (D.signatur childPoll) Λ)
    (infallible : D.gruende childPoll = 0)
    (arms : Arms D V l (.sum cases :: Γ) (nach D childPoll Λ) Λ cases) :
    Block D V l Γ Λ Λ :=
  .bindCall childPoll arguments resultType contract infallible
    (.cons (.onTag (.var .here) arms) .nil)

/-- The call gate is exactly the named child poll and its answer arms. -/
public theorem waitingBlock_calls (direct : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (childPoll : D.Fn) (arguments : Args D Γ Λ (D.params childPoll))
    (resultType : D.erg childPoll = some (.sum cases))
    (contract : RufPasst D V (D.signatur childPoll) Λ)
    (infallible : D.gruende childPoll = 0)
    (arms : Arms D V l (.sum cases :: Γ) (nach D childPoll Λ) Λ cases) :
    rufeB direct indirect forever (waitingBlock (V := V) (l := l) childPoll arguments resultType contract infallible arms) =
      (direct childPoll && rufeArms direct indirect forever arms) := by
  simp only [waitingBlock, rufeB, rufeS, Bool.and_true]

/-- The ordinary cost includes argument evaluation, the actual callee's
    price, answer dispatch and the trailing empty block. -/
public theorem waitingBlock_cost (calls : D.Fn → Nat) (passes : Nat)
    (childPoll : D.Fn) (arguments : Args D Γ Λ (D.params childPoll))
    (resultType : D.erg childPoll = some (.sum cases))
    (contract : RufPasst D V (D.signatur childPoll) Λ)
    (infallible : D.gruende childPoll = 0)
    (arms : Arms D V l (.sum cases :: Γ) (nach D childPoll Λ) Λ cases) :
    kostenBlock 0 calls passes
      (waitingBlock (V := V) (l := l) childPoll arguments resultType contract infallible arms) =
      2 + kostenArgs arguments + calls childPoll + (2 + kostenArms 0 calls passes arms + 1) := rfl

/-- Successful ordinary G execution, with no invented callback execution
    rule. Failure outcomes remain the outcomes of the underlying call. -/
public theorem waitingBlock_exec (O : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (childPoll : D.Fn) (arguments : Args D Γ Λ (D.params childPoll))
    (resultType : D.erg childPoll = some (.sum cases))
    (contract : RufPasst D V (D.signatur childPoll) Λ)
    (infallible : D.gruende childPoll = 0)
    (arms : Arms D V l (.sum cases :: Γ) (nach D childPoll Λ) Λ cases)
    (world after : World D) (environment : Env D Γ)
    (answer : ErgVal D (D.erg childPoll))
    (success : calls childPoll (world.lese Λ arguments.orte)
      (evalArgs (world.lese Λ arguments.orte) arguments
        (world.lese Λ arguments.orte) environment) = .ok after answer) :
    execBlock O passes calls (waitingBlock (V := V) (l := l) childPoll arguments resultType contract infallible arms)
      world environment =
      (execArms O passes calls arms (ergWert resultType answer) after
        (.cons (ergWert resultType answer) environment)).schrumpf := by
  simp only [waitingBlock, execBlock]
  rw [success]
  simp only [execStmt, Expr.orte, World.lese,
    World.merke, List.map_nil, List.nil_append, eval, Env.get]
  cases execArms O passes calls arms (ergWert resultType answer) after
    (.cons (ergWert resultType answer) environment) <;> rfl

end Gabbro.Grammatik.Async.Segment
