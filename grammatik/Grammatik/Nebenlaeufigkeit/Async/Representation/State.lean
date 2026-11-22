module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Tasks

namespace Gabbro.Grammatik.Async.Representation
open Segment

variable {D : Deklaration}

/-- A phase is selected only when both its semantic tag and payload agree.
    Completion has no frame; malformed children and mistyped cached answers
    fail encoding rather than being coerced to a different state. -/
@[expose] public def encodePhase (D : Deklaration) (types : TypeResolution) (f : AsyncFn) :
    (phase : Phase) → State (Value D) (Child D types) → Option (Wert D (phaseType types f phase))
  | Phase.cancelled, State.cancelled => some ()
  | Phase.completed, State.completed value ⟨[], []⟩ => do
      let result ← valueAt D (types.ordinary f.resultType) value
      pure (result, ())
  | Phase.running tag, State.running actual frame =>
      if actual = tag then encodeFrame D types f (Phase.running tag) frame else none
  | Phase.waiting tag future, State.waiting actual frame task =>
      if actual = tag then do
        let frame ← encodeFrame D types f (Phase.waiting tag future) frame
        let child ← encodeTask D types [tag] future task
        pure (frame, child, ())
      else none
  | _, _ => none

public inductive PhaseRep (D : Deklaration) (types : TypeResolution) (f : AsyncFn) :
    (phase : Phase) → State (Value D) (Child D types) → Wert D (phaseType types f phase) → Prop where
  | cancelled : PhaseRep D types f Phase.cancelled State.cancelled ()
  | completed (value : Value D) (result : Wert D (types.ordinary f.resultType))
      (typed : valueAt D (types.ordinary f.resultType) value = some result) :
      PhaseRep D types f Phase.completed (State.completed value ⟨[], []⟩) (result, ())
  | running (tag : Nat) (frame : Frame (Value D)) (value : Wert D (frameType types f))
      (slots : FrameRep D types f (Phase.running tag) frame value) :
      PhaseRep D types f (Phase.running tag) (State.running tag frame) value
  | waiting (tag : Nat) (future : FutureExpr) (frame : Frame (Value D))
      (task : Task (Value D) (Child D types)) (frameValue : Wert D (frameType types f))
      (taskValue : Wert D (taskStorageType types [tag] future))
      (slots : FrameRep D types f (Phase.waiting tag future) frame frameValue)
      (child : TaskRep D types [tag] future task taskValue) :
      PhaseRep D types f (Phase.waiting tag future) (State.waiting tag frame task)
        (frameValue, taskValue, ())

public theorem phaseRep_encoded (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (source : State (Value D) (Child D types))
    (payload : Wert D (phaseType types f phase))
    (represented : PhaseRep D types f phase source payload) :
    encodePhase D types f phase source = some payload := by
  cases represented with
  | cancelled => rfl
  | completed value result typed =>
    simp only [encodePhase, typed, Option.bind_eq_bind, Option.bind_some, Option.pure_def] <;> rfl
  | running tag frame value slots =>
    change (if tag = tag then encodeFrame D types f (Phase.running tag) frame else none) = some value
    rw [if_pos rfl]
    exact frameRep_encoded types f (Phase.running tag) frame value slots
  | waiting tag future frame task frameValue taskValue slots child =>
    simp only [encodePhase, if_pos rfl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      frameRep_encoded types f (Phase.waiting tag future) frame frameValue slots,
      taskRep_encoded types [tag] future task taskValue child] <;> rfl

/-- Inject a later case, keeping its payload and increasing only its finite
    index. The proof is over the exact remaining schema, not a raw tag bound. -/
@[expose] public def laterPhaseValue (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (rest : List Phase)
    (value : Wert D (Ty.sum (rest.map fun p => some (phaseType types f p)))) :
    Wert D (Ty.sum ((phase :: rest).map fun p => some (phaseType types f p))) :=
  ⟨⟨value.1.val + 1, Nat.succ_lt_succ value.1.isLt⟩, value.2⟩

@[expose] public def firstPhaseValue (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (phase : Phase) (rest : List Phase) (value : Wert D (phaseType types f phase)) :
    Wert D (Ty.sum ((phase :: rest).map fun p => some (phaseType types f p))) :=
  ⟨⟨0, Nat.zero_lt_succ (rest.map fun p => some (phaseType types f p)).length⟩, value⟩

@[expose] public def encodePhases (D : Deklaration) (types : TypeResolution) (f : AsyncFn) :
    (cases : List Phase) → State (Value D) (Child D types) →
      Option (Wert D (Ty.sum (cases.map fun phase => some (phaseType types f phase))))
  | [], _ => none
  | phase :: rest, source =>
      match encodePhase D types f phase source with
      | some value => some (firstPhaseValue D types f phase rest value)
      | none => do
          let value ← encodePhases D types f rest source
          pure (laterPhaseValue D types f phase rest value)

/-- The selected finite case, its actual payload shape, and its owned
    resources. Earlier cases must not match the source state. -/
public inductive PhaseListRep (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) : (cases : List Phase) → State (Value D) (Child D types) →
      Wert D (Ty.sum (cases.map fun phase => some (phaseType types f phase))) → Prop where
  | first (phase : Phase) (rest : List Phase) (source : State (Value D) (Child D types))
      (value : Wert D (phaseType types f phase))
      (payload : PhaseRep D types f phase source value) (marks : MarksRep inventory phase source) :
      PhaseListRep D types f inventory (phase :: rest) source
        (firstPhaseValue D types f phase rest value)
  | later (phase : Phase) (rest : List Phase) (source : State (Value D) (Child D types))
      (value : Wert D (Ty.sum (rest.map fun p => some (phaseType types f p))))
      (absent : encodePhase D types f phase source = none)
      (tail : PhaseListRep D types f inventory rest source value) :
      PhaseListRep D types f inventory (phase :: rest) source
        (laterPhaseValue D types f phase rest value)

public theorem phaseListRep_encoded (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) (cases : List Phase) (source : State (Value D) (Child D types))
    (value : Wert D (Ty.sum (cases.map fun phase => some (phaseType types f phase))))
    (represented : PhaseListRep D types f inventory cases source value) :
    encodePhases D types f cases source = some value := by
  induction represented with
  | first phase rest source value payload _ =>
    simp only [encodePhases, phaseRep_encoded types f phase source value payload]
  | later phase rest source value absent _ ih =>
    simp only [encodePhases, absent, ih, Option.bind_eq_bind, Option.bind_some, Option.pure_def] <;> rfl

/-- Inject the payload at its position in the generated schema. The
    matched position, rather than payload-type equality, identifies a case. -/
@[expose] public def phaseValueAt (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (cases : List Phase) (index : Fin cases.length)
    (value : Wert D (phaseType types f (cases.get index))) :
    Wert D (.sum (cases.map fun p => some (phaseType types f p))) :=
  let schema := cases.map fun p => some (phaseType types f p)
  let mapped : Fin schema.length := ⟨index.val, by simpa only [schema, List.length_map] using index.isLt⟩
  have typeAt : schema.get mapped = some (phaseType types f (cases.get index)) :=
    List.getElem_map (fun p => some (phaseType types f p)) (h := mapped.isLt)
  let payload : Nutzlast D.Fn D.passt (some (phaseType types f (cases.get index))) := value
  ⟨mapped, Fall.ofNutzlast D.Fn D.passt schema mapped (typeAt.symm ▸ payload)⟩

public theorem phaseListRep_at (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) (source : State (Value D) (Child D types)) :
    ∀ (cases : List Phase) (index : Fin cases.length)
      (value : Wert D (phaseType types f (cases.get index))),
      PhaseRep D types f (cases.get index) source value →
      MarksRep inventory (cases.get index) source →
      (∀ before : Fin cases.length, before.val < index.val →
        encodePhase D types f (cases.get before) source = none) →
      PhaseListRep D types f inventory cases source (phaseValueAt D types f cases index value)
  | [], index, _, _, _, _ => index.elim0
  | phase :: rest, ⟨0, _⟩, value, payload, marks, _ => .first phase rest source value payload marks
  | phase :: rest, ⟨offset + 1, valid⟩, value, payload, marks, absent =>
    have head := absent ⟨0, Nat.zero_lt_succ _⟩ (Nat.zero_lt_succ offset)
    let next : Fin rest.length := ⟨offset, Nat.lt_of_succ_lt_succ valid⟩
    have tail := phaseListRep_at types f inventory source rest next value payload marks
      (fun before earlier => absent before.succ (Nat.succ_lt_succ earlier))
    .later phase rest source _ head tail

@[expose] public def prefixValue (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (suffix : List Phase)
    (value : Wert D (Ty.sum (suffix.map fun phase => some (phaseType types f phase)))) :
    («prefix» : List Phase) →
      Wert D (Ty.sum ((«prefix» ++ suffix).map fun phase => some (phaseType types f phase)))
  | [] => value
  | phase :: rest => laterPhaseValue D types f phase (rest ++ suffix)
      (prefixValue D types f suffix value rest)

public theorem phaseListRep_prefix (types : TypeResolution) (f : AsyncFn)
    (inventory : Inventory D) (source : State (Value D) (Child D types))
    (suffix : List Phase)
    (value : Wert D (Ty.sum (suffix.map fun phase => some (phaseType types f phase))))
    (represented : PhaseListRep D types f inventory suffix source value)
    («prefix» : List Phase)
    (absent : ∀ phase ∈ «prefix», encodePhase D types f phase source = none) :
    PhaseListRep D types f inventory («prefix» ++ suffix) source
      (prefixValue D types f suffix value «prefix») := by
  revert absent
  induction «prefix» with
  | nil => intro _; exact represented
  | cons phase rest ih =>
    intro absent
    exact PhaseListRep.later phase (rest ++ suffix) source
      (prefixValue D types f suffix value rest) (absent phase List.mem_cons_self)
      (ih (fun other member => absent other (List.mem_cons_of_mem phase member)))

/-- Representation invariant for the canonical stateType: exact phase sum,
    live saved slots, declaration-shaped child/join storage and owned marks.
    Resource authority is inventory.resources, never a copied G value. -/
@[expose] public def Inv (f : AsyncFn) (types : TypeResolution) (inventory : Inventory D)
    (source : State (Value D) (Child D types)) (value : Wert D (stateType types f)) : Prop :=
  PhaseListRep D types f inventory (phases f) source value.1

/-- A partial encoder is intentional: an arbitrary semantic State can have
    an out-of-range tag, a mismatched child, or an uninitialised live local.
    Totality on semantic reachability requires preservation, not a default. -/
@[expose] public def encode (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (source : State (Value D) (Child D types)) : Option (Wert D (stateType types f)) := do
  let value ← encodePhases D types f (phases f) source
  pure (value, ())

public theorem inv_encoded (f : AsyncFn) (types : TypeResolution) (inventory : Inventory D)
    (source : State (Value D) (Child D types)) (value : Wert D (stateType types f))
    (represented : Inv f types inventory source value) :
    encode D types f source = some value := by
  obtain ⟨sum, tail⟩ := value
  cases tail
  have encoded := phaseListRep_encoded types f inventory (phases f) source sum represented
  unfold encode
  rw [encoded]
  rfl

@[expose] public def runningValue (D : Deklaration) (types : TypeResolution) (f : AsyncFn)
    (tag : Nat) (within : tag ≤ f.body.length) (frame : Wert D (frameType types f)) :
    Wert D (stateType types f) :=
  let selected := runningCase types f tag within
  let payload : Nutzlast D.Fn D.passt (some (frameType types f)) := frame
  (⟨selected.val, Fall.ofNutzlast D.Fn D.passt _ selected.val (selected.property.symm ▸ payload)⟩, ())

private theorem phaseValueAt_transport (types : TypeResolution) (f : AsyncFn)
    (cases : List Phase) (index : Fin cases.length) {τ : Ty}
    (same : phaseType types f (cases.get index) = τ) (value : Wert D τ) :
    let schema := cases.map fun p => some (phaseType types f p)
    let mapped : Fin schema.length := ⟨index.val, by simpa only [schema, List.length_map] using index.isLt⟩
    let mappedType : schema.get mapped = some (phaseType types f (cases.get index)) :=
      List.getElem_map (fun p => some (phaseType types f p)) (h := mapped.isLt)
    let payload : Nutzlast D.Fn D.passt (some τ) := value
    phaseValueAt D types f cases index (same.symm ▸ value) =
      ⟨mapped, Fall.ofNutzlast D.Fn D.passt schema mapped
        ((mappedType.trans (congrArg some same)).symm ▸ payload)⟩ := by
  cases same
  rfl

/-- The computed dispatch tag and the live frame written by ordinary G
    form the same state as the semantic running command. -/
public theorem runningValue_inv (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (tag : Nat) (within : tag ≤ f.body.length) (frame : Frame (Value D))
    (saved : Wert D (frameType types f)) (slots : FrameRep D types f (.running tag) frame saved)
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame)) :
    Inv f types inventory (.running tag frame) (runningValue D types f tag within saved) := by
  let selected := commandRunningIndex 0 f.body tag within
  let index : Fin (phases f).length := selected.val.succ.succ
  have active : (phases f).get index = .running tag := selected.property
  have sameType : phaseType types f ((phases f).get index) = frameType types f :=
    congrArg (phaseType types f) active
  have payload : PhaseRep D types f ((phases f).get index) (.running tag frame) (sameType.symm ▸ saved) := by
    have transport (phase : Phase) (same : phase = .running tag) :
        PhaseRep D types f phase (.running tag frame) ((congrArg (phaseType types f) same).symm ▸ saved) := by
      cases same
      exact .running tag frame saved slots
    exact transport _ active
  have presentMarks : MarksRep inventory ((phases f).get index) (.running tag frame) := active.symm ▸ marks
  have absent (before : Fin (phases f).length) (earlier : before.val < index.val) :
      encodePhase D types f ((phases f).get before) (.running tag frame) = none := by
    obtain ⟨position, inList⟩ := before
    cases position with
    | zero => rfl
    | succ position =>
      cases position with
      | zero => rfl
      | succ position =>
        let previous : Fin (commandPhases 0 f.body).length :=
          ⟨position, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ inList)⟩
        have closer : previous.val < selected.val.val := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ earlier)
        have different := commandRunningIndex_first 0 f.body tag within previous closer
        change encodePhase D types f ((commandPhases 0 f.body).get previous) (.running tag frame) = none
        cases atPhase : (commandPhases 0 f.body).get previous with
        | cancelled => rfl
        | completed => rfl
        | waiting => rfl
        | running current =>
          have other : tag ≠ current := by
            intro equal
            exact (different (atPhase.trans (congrArg Phase.running equal.symm)))
          exact if_neg other
  have matched := phaseListRep_at types f inventory (.running tag frame) (phases f) index _ payload presentMarks absent
  have exactValue : phaseValueAt D types f (phases f) index (sameType.symm ▸ saved) =
      (runningValue D types f tag within saved).1 :=
    phaseValueAt_transport types f (phases f) index sameType saved
  rw [exactValue] at matched
  exact matched

public theorem runningExpr_reads (types : TypeResolution) (f : AsyncFn)
    {Γ : Ctx} {Λ : List (Res D)} (tag : Nat) (within : tag ≤ f.body.length)
    (frame : Expr D Γ Λ (frameType types f)) :
    (runningExpr types f tag within frame).orte = frame.orte := by
  have transport {before after : Option Ty} (same : before = after)
      (payload : NutzlastExpr D Γ Λ before) :
      (same ▸ payload : NutzlastExpr D Γ Λ after).orte = payload.orte := by
    cases same
    rfl
  simp only [runningExpr, stateExpr, Expr.orte, Args.orte, transport, NutzlastExpr.orte, List.append_nil]

/-- The generated constructor carries the actual evaluated frame. Transport
    across the selector's type equality changes no field in that frame. -/
public theorem runningExpr_eval {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (tag : Nat) (within : tag ≤ f.body.length)
    (expression : Expr D Γ Λ (frameType types f)) (entry world : World D) (env : Env D Γ) :
    eval entry (runningExpr types f tag within expression) world env =
      runningValue D types f tag within (eval entry expression world env) := by
  simp only [runningExpr, stateExpr, runningValue, eval, evalProd, evalNutz_cast, evalNutz] <;> rfl

/-- Change the dispatch tag after the next frame has been constructed.
    Both the frame input and the state destination are ordinary locals. -/
@[expose] public def resumeBlock {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (tag : Nat) (within : tag ≤ f.body.length)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f)) : Block D V l Γ Λ Λ :=
  constructBlock state (runningExpr types f tag within (.var saved))

public theorem resumeBlock_exec {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (types : TypeResolution) (f : AsyncFn) (tag : Nat) (within : tag ≤ f.body.length)
    (saved : Var Γ (frameType types f)) (state : Var Γ (stateType types f))
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (world : World D) (env : Env D Γ) :
    execBlock oracle passes calls (resumeBlock (V := V) (l := l) (Λ := Λ) types f tag within saved state) world env =
      .ok world (env.set state (runningValue D types f tag within (env.get saved))) := by
  let successor : Expr D Γ Λ (stateType types f) := runningExpr types f tag within (.var saved)
  have reads : successor.orte = [] := runningExpr_reads types f tag within (.var saved)
  have execution := constructBlock_exec (V := V) (l := l) oracle passes calls state successor world env
  have noRead : world.lese Λ [] = world := rfl
  simp only [reads, noRead] at execution
  have exactFrame := runningExpr_eval types f tag within (Expr.var (Λ := Λ) saved) world world env
  change eval world successor world env = runningValue D types f tag within (env.get saved) at exactFrame
  rw [exactFrame] at execution
  exact execution

public theorem cancelled_encoded (types : TypeResolution) (f : AsyncFn) :
    encode D types f State.cancelled = some (cancelledValue types f D) := rfl

public theorem cancelled_inv (types : TypeResolution) (f : AsyncFn) (inventory : Inventory D)
    (empty : inventory.owned Phase.cancelled = []) :
    Inv f types inventory State.cancelled (cancelledValue types f D) := by
  apply PhaseListRep.first Phase.cancelled (Phase.completed :: commandPhases 0 f.body)
    State.cancelled () PhaseRep.cancelled
  simp only [MarksRep, State.marks, empty, List.map_nil]

end Gabbro.Grammatik.Async.Representation
