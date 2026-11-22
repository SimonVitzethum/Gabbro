module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Dispatch
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Restore

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)} {l : Bool} {Γ : Ctx}
  {types : TypeResolution} {f : AsyncFn}

/-- A source argument uses the actual term and live bindings furnished
    by ordinary elaboration. -/
public structure CheckedArgument (elaboration : Elaboration D V Λ types f) (tag : Nat)
    (source : Parser.SExpr) where
  term : BoundExpression D Λ
  known : elaboration.expression source = some term
  restore : RestorePlan types f term.locals
  live : ∀ entry ∈ term.locals, entry.1 ∈ liveAt f (.running tag)

@[expose] public def checkArgument (elaboration : Elaboration D V Λ types f) (tag : Nat) (argument : Parser.SExpr) :
    Except String (CheckedArgument elaboration tag argument) := do
  match found : elaboration.expression argument with
  | none => throw "async: unresolved argument expression"
  | some term =>
    if live : term.locals.all (fun entry => decide (entry.1 ∈ liveAt f (.running tag))) = true then
      let restore ← restorePlanFor types f term.locals
      return ⟨term, found, restore, fun entry member => of_decide_eq_true (List.all_eq_true.mp live entry member)⟩
    else throw "async: argument expression uses an unavailable local"

/-- Bind the value of an argument once. Restored locals are visible only
    to the expression; the continuation receives a binding for the result
    and an embedding of its original scope. -/
@[expose] public def CheckedArgument.lower {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {source : Parser.SExpr} (checked : CheckedArgument elaboration tag source)
    (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) → Var Δ checked.term.result → Block D V l Δ Λ Λ) :
    Block D V l Γ Λ Λ :=
  restoreFrameBlock checked.restore saved
    (.bind (checked.term.expression.ren (keepLocal Γ))
      (body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here))

/-- The emitted local restoration and argument binder match exactly one
    semantic expression step, including its reads and new world. -/
public theorem CheckedArgument.lower_exec {elaboration : Elaboration D V Λ types f} {tag : Nat}
    {source : Parser.SExpr} (checked : CheckedArgument elaboration tag source)
    (saved : Var Γ (frameType types f))
    (body : ∀ {Δ : Ctx}, (∀ {τ : Ty}, Var Γ τ → Var Δ τ) → Var Δ checked.term.result → Block D V l Δ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D))
    (represented : FrameRep D types f (.running tag) frame (env.get saved)) :
    ∃ (scope : Env D (checked.term.locals.map Prod.snd)),
      localsEnv D checked.term.locals frame = some scope ∧
      let continuation := body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here
      let answer := evaluateExpression checked.term.expression world scope
      evaluateBound elaboration source frame world = (Value.typed checked.term.result answer.1, answer.2) ∧
      execBlock oracle passes calls (checked.lower saved body) world env =
        removeLocals (checked.term.locals.map Prod.snd)
          (execBlock oracle passes calls continuation answer.2.1 (.cons answer.1 (appendLocals scope env))).schrumpf := by
  obtain ⟨scope, localValues⟩ := checked.restore.locals_defined (.running tag) frame (env.get saved) represented checked.live
  refine ⟨scope, localValues, evaluateBound_resolved elaboration source checked.term checked.known frame scope
    localValues world, ?_⟩
  let embedded : ∀ {τ : Ty}, Var (checked.term.locals.map Prod.snd) τ →
      Var (checked.term.locals.map Prod.snd ++ Γ) τ := keepLocal Γ
  let expression := checked.term.expression.ren embedded
  let continuation : Block D V l (checked.term.result :: checked.term.locals.map Prod.snd ++ Γ) Λ Λ :=
    body (fun x => .there (prependLocal x (checked.term.locals.map Prod.snd))) .here
  have installed := restoreFrameBlock_rep checked.restore saved oracle passes calls world env frame (.running tag)
    represented (.bind expression continuation) scope checked.live localValues
  change execBlock oracle passes calls (checked.lower saved body) world env = _ at installed
  rw [installed]
  have same := checked.term.expression.ren_sound embedded
  simp only [execBlock, expression, same.1, evaluateExpression]
  rw [same.2.2 _ _ scope (appendLocals scope env) (get_keepLocal env scope)]

end Gabbro.Grammatik.Async.Representation
