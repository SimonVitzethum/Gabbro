module

public import Grammatik.Nebenlaeufigkeit.Async.Kosten
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async
open Parser

/-! These are outer-layer checks. Physical HeldB/resource/cost guarantees
    additionally require the ordinary segment and reification certificates.
    In particular, an annotation saying heldLocks=[] is not a G proof. -/

mutual
/-- Conservative free-name collection; extension names are included, so an
    unknown binding form can over-refuse, never hide a needed saved local. -/
@[expose] public def expressionNames : SExpr → List String
  | .variable name => [name]
  | .field e _ | .arrow e _ | .un _ e | .old e => expressionNames e
  | .index a b | .bin _ a b => expressionNames a ++ expressionNames b
  | .call _ args | .built _ args => argumentNames args
  | .ext _ names args => names ++ argumentNames args
  | _ => []
@[expose] public def argumentNames : List SExpr → List String
  | [] => []
  | e :: es => expressionNames e ++ argumentNames es
end

@[expose] public def futureNames : FutureExpr → List String
  | .call _ args => argumentNames args
  | .join a b => futureNames a ++ futureNames b

@[expose] public def without (name : String) (names : List String) : List String :=
  names.filter (fun candidate => !(candidate == name))

/-- Backwards liveness, computed from the continuation rather than trusted
    from its annotation. An await's result binder is not yet a saved local. -/
@[expose] public def liveBefore (result : SExpr) : List Command → List String
  | [] => expressionNames result
  | .bind name expr _ :: rest => expressionNames expr ++ without name (liveBefore result rest)
  | .await name expr _ :: rest => futureNames expr ++ without name (liveBefore result rest)

/-- Explicit save, no held lock, and a bijective move of unique marks. Exact
    list equality makes the move deterministic and forbids omission/copying. -/
@[expose] public def BoundarySafe (fields required : List String) (b : Boundary) : Prop :=
  required.all b.live.contains = true ∧
  b.live.all b.saved.contains = true ∧
  b.saved.all fields.contains = true ∧
  b.heldLocks = [] ∧ b.moved = b.owned ∧ b.owned.Nodup ∧ b.saved.Nodup

@[expose] public instance (fields required : List String) (b : Boundary) :
    Decidable (BoundarySafe fields required b) := by
  unfold BoundarySafe
  infer_instance

@[expose] public def bodyCheck (fields : List String) (result : SExpr) : List Command → Bool
  | [] => true
  | .bind name _ _ :: rest => fields.contains name && bodyCheck fields result rest
  | .await name _ b :: rest => fields.contains name &&
    decide (BoundarySafe fields (without name (liveBefore result rest)) b) &&
    bodyCheck fields result rest

/-- The generated record retains parameters as well as all declared locals.
    Saving a superset is intentional: it avoids a second storage mechanism. -/
@[expose] public def fieldNames (f : AsyncFn) : List String := (f.params ++ f.fields).map Prod.fst

@[expose] public def asyncCheck (f : AsyncFn) : Bool :=
  decide (fieldNames f).Nodup && bodyCheck (fieldNames f) f.result f.body

@[expose] public def AsyncOk (f : AsyncFn) : Prop := asyncCheck f = true

/-- Declarative reading of the recursive checker. -/
@[expose] public def BodySafe (fields : List String) (result : SExpr) : List Command → Prop
  | [] => True
  | .bind name _ _ :: rest => name ∈ fields ∧ BodySafe fields result rest
  | .await name _ b :: rest => name ∈ fields ∧
    BoundarySafe fields (without name (liveBefore result rest)) b ∧
    BodySafe fields result rest

public theorem bodyCheck_sound (fields : List String) (result : SExpr) (body : List Command) :
    bodyCheck fields result body = true → BodySafe fields result body := by
  induction body with
  | nil => intro _; trivial
  | cons command rest ih =>
    cases command <;>
      simp only [bodyCheck, BodySafe, Bool.and_eq_true, decide_eq_true_eq,
        List.contains_iff_mem] <;> intro h
    · exact ⟨h.1, ih h.2⟩
    · exact ⟨h.1.1, h.1.2, ih h.2⟩

public theorem asyncCheck_sound (f : AsyncFn) (h : AsyncOk f) :
    (fieldNames f).Nodup ∧ BodySafe (fieldNames f) f.result f.body := by
  simp only [AsyncOk, asyncCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, bodyCheck_sound _ _ _ h.2⟩

public theorem boundary_no_locks {fields required : List String} {b : Boundary}
    (h : BoundarySafe fields required b) : b.heldLocks = [] := h.2.2.2.1

public theorem boundary_moves_once {fields required : List String} {b : Boundary}
    (h : BoundarySafe fields required b) : b.moved = b.owned ∧ b.moved.Nodup := by
  have moved := h.2.2.2.2.1
  exact ⟨moved, moved.symm ▸ h.2.2.2.2.2.1⟩

/-- The checker adds storage/resource conditions to the unconditional semantic
    transformation theorem. It does not fabricate a canonical G certificate. -/
public theorem asyncOk_refines (model : Model Value Child) (f : AsyncFn) (_ok : AsyncOk f)
    {source target : State Value Child} {event : Event Value} {cost : Nat}
    (run : MachinePoll model (asyncExpand model f) source event target cost) :
    DirectPoll model f (decode f source) event (decode f target) cost :=
  poll_refines model f run

/-- Well-formed tags and storage. This prevents invalid wait tags and forged
    completed records from laundering marks; it is not a G memory proof. -/
@[expose] public def StorageValid (f : AsyncFn) : State Value Child → Prop
  | .running tag _ => tag ≤ f.body.length
  | .waiting tag _ _ => ∃ name expr boundary rest,
      f.body.drop tag = .await name expr boundary :: rest
  | .completed _ frame => frame.marks = []
  | .cancelled => True

public theorem cancellation_refines (f : AsyncFn) (state : State Value Child)
    (valid : StorageValid f state) :
    directCancel (decode f state) =
      ((machineCancel state).1, decode f (machineCancel state).2) := by
  cases state with
  | running tag frame => rfl
  | waiting tag frame child =>
    obtain ⟨name, expr, boundary, rest, h⟩ := valid
    simp only [decode, h, directCancel, machineCancel, State.marks, List.nil_append, List.append_nil]
  | completed value frame =>
    simp only [StorageValid] at valid
    simp only [decode, directCancel, machineCancel, State.marks, valid, List.nil_append, List.append_nil]
  | cancelled => rfl

/-- The destructor sees the COMPLETE saved state, including partial join
    children. Invoke it before clearing storage: marks alone cannot encode
    child cancellation hooks or the values needed by a resource destructor. -/
@[expose] public def cancelWith (drop : State Value Child → Heap → List Nat × Heap)
    (source : State Value Child) (heap : Heap) : List Nat × State Value Child × Heap :=
  let result := drop source heap
  (result.1, .cancelled, result.2)

/-- An ordinary user duty, not an assumption: the actual destructor receives
    the saved values and children, releases each owned mark exactly once and
    leaves no permissions. Owns and drop must be instantiated by G contracts. -/
@[expose] public def DropDuty (Owns : List Nat → Heap → Prop)
    (drop : State Value Child → Heap → List Nat × Heap) : Prop :=
  ∀ state heap, state.marks.Nodup → Owns state.marks heap →
    (drop state heap).1 = state.marks ∧ (drop state heap).1.Nodup ∧
      Owns [] (drop state heap).2

public theorem cancellation_no_leak (Owns : List Nat → Heap → Prop)
    (drop : State Value Child → Heap → List Nat × Heap)
    (duty : DropDuty Owns drop) (state : State Value Child) (heap : Heap)
    (unique : state.marks.Nodup) (owned : Owns state.marks heap) :
    (let (released, target, heap') := cancelWith drop state heap
     released = state.marks ∧ released.Nodup ∧ target.marks = [] ∧ Owns [] heap') := by
  have good := duty state heap unique owned
  exact ⟨good.1, good.2.1, rfl, good.2.2⟩

public theorem cancelWith_refines (Owns : List Nat → Heap → Prop)
    (drop : State Value Child → Heap → List Nat × Heap)
    (duty : DropDuty Owns drop) (f : AsyncFn) (state : State Value Child) (heap : Heap)
    (valid : StorageValid f state) (unique : state.marks.Nodup)
    (owned : Owns state.marks heap) :
    directCancel (decode f state) =
      ((cancelWith drop state heap).1, decode f (cancelWith drop state heap).2.1) := by
  have good := duty state heap unique owned
  rw [cancellation_refines f state valid]
  simp only [cancelWith, machineCancel, good.1]

/-- Exact missing boundary: provide actual ordinary target operations, their
    state encoding, and a proof for EVERY dispatch and destructor execution.
    No instance is supplied here. In particular this is not source admission,
    Akzeptiert, a G/GX theorem or a Stage-0 lowering certificate. -/
public structure ReificationDuty (model : Model Value Child) (f : AsyncFn)
    (Target : Type) (step : Target → Event Value × Target × Nat)
    (cancel : Target → List Nat × Target) where
  encode : State Value Child → Target
  stepCorrect : ∀ source event target cost,
    StorageValid f source →
    machineStep model (asyncExpand model f) source = (event, target, cost) →
    step (encode source) = (event, encode target, cost)
  cancelCorrect : ∀ source, StorageValid f source →
    cancel (encode source) = ((machineCancel source).1, encode (machineCancel source).2)

/-- Computed liveness reaches actual generated record fields, transitively
    through the written save list. -/
public theorem boundary_saves_required {fields required : List String} {b : Boundary}
    (h : BoundarySafe fields required b) (name : String) (needed : name ∈ required) :
    name ∈ b.saved ∧ name ∈ fields := by
  have live : name ∈ b.live :=
    List.contains_iff_mem.mp (List.all_eq_true.mp h.1 name needed)
  have saved : name ∈ b.saved :=
    List.contains_iff_mem.mp (List.all_eq_true.mp h.2.1 name live)
  exact ⟨saved, List.contains_iff_mem.mp (List.all_eq_true.mp h.2.2.1 name saved)⟩

/-- No finite tag can escape its code table when starting with create. This
    also keeps completed records empty after the Ready ownership transfer. -/
public theorem storageValid_step (model : Model Value Child) (f : AsyncFn)
    {source target : State Value Child} {event : Event Value} {cost : Nat}
    (valid : StorageValid f source)
    (h : machineStep model (asyncExpand model f) source = (event, target, cost)) :
    StorageValid f target := by
  cases source with
  | running tag frame =>
    cases hd : f.body.drop tag with
    | nil =>
      cases he : model.evaluate f.result frame with
      | mk value work =>
        simp only [machineStep, table_drop, drop_compiled, hd, asyncExpand, he, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
    | cons command rest =>
      have nextTag : tag + 1 ≤ f.body.length := by
        have size := congrArg List.length hd
        simp only [List.length_drop, List.length_cons] at size
        omega
      cases command with
      | bind name expr bound =>
        cases he : model.evaluate expr frame with
        | mk value work =>
          simp only [machineStep, table_drop, drop_compiled, hd, compileCommand, he, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact nextTag
      | await name expr boundary =>
        cases he : makeTask model frame expr with
        | mk child work =>
          simp only [machineStep, table_drop, drop_compiled, hd, compileCommand, he, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨name, expr, boundary, rest, hd⟩
  | waiting tag frame child =>
    obtain ⟨name, expr, boundary, rest, hd⟩ := valid
    have nextTag : tag + 1 ≤ f.body.length := by
      have size := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at size
      omega
    cases hp : pollTask model child with
    | mk result payload =>
      cases payload with
      | mk child' work =>
        cases result with
        | pending =>
          simp only [machineStep, table_drop, drop_compiled, hd, compileCommand, hp, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨name, expr, boundary, rest, hd⟩
        | ready value =>
          simp only [machineStep, table_drop, drop_compiled, hd, compileCommand, hp, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact nextTag
  | completed value frame =>
    simp only [machineStep, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact valid
  | cancelled =>
    simp only [machineStep, List.map_nil, List.map_cons, Prod.mk.injEq, reduceCtorEq, true_and, false_and] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    trivial

public theorem storageValid_poll (model : Model Value Child) (f : AsyncFn)
    {source target : State Value Child} {event : Event Value} {cost : Nat}
    (valid : StorageValid f source)
    (run : MachinePoll model (asyncExpand model f) source event target cost) :
    StorageValid f target := by
  revert valid
  induction run with
  | stop step terminal =>
    intro valid
    exact storageValid_step model f valid step
  | next step rest ih =>
    intro valid
    exact ih (storageValid_step model f valid step)

public theorem storageValid_create (f : AsyncFn) (frame : Frame Value) :
    StorageValid f (create (Child := Child) f frame).state := Nat.zero_le _

/-- Authority accounting is separate from inert local values. -/
@[expose] public def directMarks : Direct Value Child → List Nat
  | .running _ frame | .waiting _ _ frame _ => frame.marks
  | .completed _ | .cancelled => []

@[expose] public def eventMarks : Event Value → List Nat
  | .ready _ marks => marks
  | _ => []

public theorem step_preserves_authority (model : Model Value Child) (f : AsyncFn)
    (source : Direct Value Child) :
    (let (event, target, _) := directStep model f source
     directMarks target ++ eventMarks event) = directMarks source := by
  cases source with
  | running rest frame =>
    cases rest with
    | nil =>
      cases he : model.evaluate f.result frame <;>
        simp only [directStep, he, directMarks, eventMarks, List.nil_append, List.append_nil]
    | cons command rest =>
      cases command with
      | bind name expr bound =>
        cases he : model.evaluate expr frame <;>
          simp only [directStep, he, directMarks, eventMarks, save, List.nil_append, List.append_nil]
      | await name expr boundary =>
        cases he : makeTask model frame expr <;>
          simp only [directStep, he, directMarks, eventMarks, List.nil_append, List.append_nil]
  | waiting name rest frame child =>
    cases hp : pollTask model child with
    | mk result payload =>
      cases payload with
      | mk child' work =>
        cases result <;> simp only [directStep, hp, directMarks, eventMarks, save, List.nil_append, List.append_nil]
  | completed value => rfl
  | cancelled => rfl

public theorem poll_preserves_authority (model : Model Value Child) (f : AsyncFn)
    {source target : Direct Value Child} {event : Event Value} {cost : Nat}
    (run : DirectPoll model f source event target cost) :
    directMarks target ++ eventMarks event = directMarks source := by
  have exactStep {source target : Direct Value Child} {event : Event Value} {work : Nat}
      (step : directStep model f source = (event, target, work)) :
      directMarks target ++ eventMarks event = directMarks source := by
    have conserved := step_preserves_authority model f source
    simpa only [step] using conserved
  induction run with
  | stop step terminal => exact exactStep step
  | next step rest ih =>
    have conserved := exactStep step
    simp only [eventMarks, List.append_nil] at conserved
    exact ih.trans conserved

end Gabbro.Grammatik.Async
