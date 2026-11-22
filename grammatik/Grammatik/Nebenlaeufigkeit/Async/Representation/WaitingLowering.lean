module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Construction

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}
  {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Enter Waiting by evaluating the child constructor once and retaining
    just the live continuation frame. This block never polls the child. -/
@[expose] public def lowerAwaitConstruction (types : TypeResolution) (f : AsyncFn) (tag : Nat)
    {destination : String} {future : FutureExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (construct : Expr D Γ Λ (taskStorageType types [tag] future)) : Block D V l Γ Λ Λ :=
  evaluateBlock construct state (waitingExpr types f tag command
    (trimFrameExpr types f (liveAt f (.waiting tag future)) (.there saved)) (.var .here))

/-- With the exact lazy child storage, the generated Waiting block
    preserves the modeled frame, resource inventory and construction reads. -/
public theorem lowerAwaitConstruction_rep (inventory : Inventory D) (tag : Nat)
    {destination : String} {future : FutureExpr} {boundary : Boundary} {rest : List Command}
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (construct : Expr D Γ Λ (taskStorageType types [tag] future))
    (oracle : Orakel D) (passes : Nat) (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (represented : FrameRep D types f (.running tag) frame (env.get saved))
    (current : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag))
    (child : TaskRep D types [tag] future task (evaluateExpression construct world env).1) :
    let answer := evaluateExpression construct world env
    ∃ value, execBlock oracle passes calls (lowerAwaitConstruction (V := V) (l := l) types f tag command
        saved state construct) world env = .ok answer.2.1 (env.set state value) ∧
      Inv f types inventory (.waiting tag frame task) value ∧
      encode D types f (.waiting tag frame task) = some value := by
  intro answer
  have retained : liveAt f (.waiting tag future) ⊆ liveAt f (.running tag) := by
    simp only [liveAt, command, liveBefore]
    intro name member
    exact List.mem_append_right _ member
  let extended : Env D (taskStorageType types [tag] future :: Γ) := .cons answer.1 env
  let storage : Expr D (taskStorageType types [tag] future :: Γ) Λ (frameType types f) :=
    trimFrameExpr types f (liveAt f (.waiting tag future)) (.there saved)
  let successor := waitingExpr types f tag command storage (.var .here)
  obtain ⟨noFrameReads, trimmed⟩ := trimFrameExpr_rep (Λ := Λ) (.there saved) retained
    answer.2.1 answer.2.1 extended represented.slots
  change storage.orte = [] at noFrameReads
  have silent : successor.orte = [] := by
    change (waitingExpr types f tag command storage (Expr.var .here)).orte = []
    simp only [waitingExpr_reads, noFrameReads, Expr.orte, List.nil_append]
  let frameValue := eval answer.2.1 storage answer.2.1 extended
  let value := waitingValue D types f tag command frameValue answer.1
  have savedFrame : FrameRep D types f (.waiting tag future) frame frameValue :=
    ⟨trimmed, fun name member => represented.declared name (retained member), represented.unique⟩
  have owned : MarksRep inventory (.waiting tag future) (.waiting tag frame task) :=
    by simpa only [MarksRep, State.marks, sameInventory] using current
  have invariant := waitingValue_inv types f inventory tag command frame task frameValue answer.1 savedFrame child owned
  have execution := evaluateBlock_exec (V := V) (l := l) oracle passes calls construct state successor world env
  have noRead (current : World D) : current.lese Λ [] = current := rfl
  simp only [silent, noRead] at execution
  change execBlock oracle passes calls (lowerAwaitConstruction (V := V) (l := l) types f tag command
      saved state construct) world env =
    .ok answer.2.1 (env.set state (eval answer.2.1 successor answer.2.1 extended)) at execution
  have exactValue : eval answer.2.1 successor answer.2.1 extended = value :=
    waitingExpr_eval types f tag command storage (.var .here) answer.2.1 answer.2.1 extended
  rw [exactValue] at execution
  exact ⟨value, execution, invariant, inv_encoded f types inventory _ value invariant⟩

end Gabbro.Grammatik.Async.Representation
