module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.State
public import Grammatik.Nebenlaeufigkeit.Async.Representation.Poll
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Model
public import Grammatik.Nebenlaeufigkeit.Async.Verfeinerung
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}
  {types : TypeResolution} {f : AsyncFn}

/-- Each context entry used by an await argument comes from a live slot
    with the same ordinary type in the source declaration. -/
@[expose] public def AwaitLocalOrigins (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (future : FutureExpr) : Prop :=
  ∀ callee args, FutureExpr.call callee args ∈ callsIn future →
    ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
      ∀ localName type, (localName, type) ∈ expression.locals →
        ∃ sourceType, (localName, sourceType) ∈ f.params ++ f.fields ∧
          localName ∈ liveAt f (.running tag) ∧ types.ordinary sourceType = type

/-- Check the actual typed argument contexts against the declared live slots. -/
@[expose] public def checkAwaitLocalOrigins (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (future : FutureExpr) : Bool :=
  (callsIn future).all fun leaf => match leaf with
  | .join .. => false
  | .call _ args => args.all fun source => match elaboration.expression source with
    | none => false
    | some expression => expression.locals.all fun localEntry =>
      decide (localEntry.1 ∈ liveAt f (.running tag)) &&
      (f.params ++ f.fields).any fun declared =>
        declared.1 == localEntry.1 && decide (types.ordinary declared.2 = localEntry.2)

public theorem checkAwaitLocalOrigins_sound (elaboration : Elaboration D V Λ types f)
    (tag : Nat) (future : FutureExpr) (checked : checkAwaitLocalOrigins elaboration tag future = true) :
    AwaitLocalOrigins elaboration tag future := by
  intro callee args leaf source argument expression resolved name type localEntry
  have arguments := List.all_eq_true.mp checked _ leaf
  have locals := List.all_eq_true.mp arguments source argument
  simp only [resolved] at locals
  have valid := List.all_eq_true.mp locals (name, type) localEntry
  obtain ⟨live, typed⟩ := Bool.and_eq_true_iff.mp valid
  obtain ⟨⟨declaredName, sourceType⟩, declared, exactType⟩ := List.any_eq_true.mp typed
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at exactType
  obtain ⟨rfl, exactType⟩ := exactType
  exact ⟨sourceType, declared, of_decide_eq_true live, exactType⟩

/-- Match the exact sequence of ordinary owned marks and their counts
    before and after entering the waiting phase. -/
@[expose] public def checkAwaitInventory (inventory : Inventory D) (tag : Nat) (future : FutureExpr) : Bool :=
  let encoded := fun phase => (inventory.owned phase).map fun entry => (inventory.number entry.1, entry.2)
  decide (encoded (.waiting tag future) = encoded (.running tag))

public theorem checkAwaitInventory_sound (inventory : Inventory D) (tag : Nat) (future : FutureExpr)
    (checked : checkAwaitInventory inventory tag future = true) :
    inventory.owned (.waiting tag future) = inventory.owned (.running tag) := by
  have exactEntry (left right : D.Marke × Nat)
      (same : (inventory.number left.1, left.2) = (inventory.number right.1, right.2)) : left = right :=
    Prod.ext (inventory.injective _ _ (congrArg Prod.fst same))
      (congrArg (fun key : Nat × Nat => key.2) same)
  exact (List.map_inj_right exactEntry).mp (of_decide_eq_true checked)

/-- Evaluating the resolved arguments in source order gives an ordinary
    argument environment. The successor world of each expression is the
    initial world of the next expression. -/
private theorem evalArguments_typed (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (frame : Frame (Value D)) {args : List Parser.SExpr} {resolved : List (BoundExpression D Λ)}
    (expressions : ExpressionsResolved elaboration.expression args resolved)
    (restored : ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
      ∃ environment, localsEnv D expression.locals frame = some environment) (world : World D) :
    ∃ environment, argumentsEnv D (resolved.map BoundExpression.result)
      (evalArguments (inducedModel elaboration calls prices normal) frame args world).1 =
        some environment := by
  induction expressions generalizing world with
  | nil => exact ⟨.nil, rfl⟩
  | @cons source expression sources expressions found _ ih =>
    obtain ⟨localEnvironment, localRestored⟩ := restored source List.mem_cons_self expression found
    simp only [evalArguments]
    change ∃ environment, argumentsEnv D (expression.result :: expressions.map BoundExpression.result)
      (let (value, middle, _) := evaluateBound elaboration source frame world
       value :: (evalArguments (inducedModel elaboration calls prices normal) frame sources middle).1) =
      some environment
    rw [evaluateBound_resolved elaboration source expression found frame localEnvironment
      localRestored world]
    generalize evaluateExpression expression.expression world localEnvironment = step
    obtain ⟨value, middle, cost⟩ := step
    obtain ⟨tail, typed⟩ := ih (fun source member => restored source (List.mem_cons_of_mem _ member)) middle
    exact ⟨.cons value tail, by simp only [argumentsEnv, valueAt_typed, typed,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩

/-- Construction of a call/join tree produces its typed active storage.
    Only the arguments and constructor expressions execute in this step. -/
private theorem makeTask_rep (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (frame : Frame (Value D)) (future : FutureExpr)
    (resolved : ∀ name args, FutureExpr.call name args ∈ callsIn future →
      ∃ callee expressions, elaboration.callee name = some callee ∧
        ExpressionsResolved elaboration.expression args expressions ∧
        expressions.map BoundExpression.result = callee.parameters)
    (restored : ∀ name args, FutureExpr.call name args ∈ callsIn future →
      ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
      ∃ environment, localsEnv D expression.locals frame = some environment)
    (path : List Nat) (world : World D) :
    ∃ record, TaskRep D types path future
      (makeTask (inducedModel elaboration calls prices normal) frame future world).1 record := by
  induction future generalizing path world with
  | call name args =>
    obtain ⟨callee, expressions, known, arguments, parameterTypes⟩ :=
      resolved name args List.mem_cons_self
    have typed := evalArguments_typed elaboration calls prices normal frame arguments
      (restored name args List.mem_cons_self) world
    rw [parameterTypes] at typed
    obtain ⟨environment, typed⟩ := typed
    simp only [makeTask]
    generalize evalArguments (inducedModel elaboration calls prices normal) frame args world =
      evaluated at typed ⊢
    obtain ⟨values, middle, cost⟩ := evaluated
    change argumentsEnv D callee.parameters values = some environment at typed
    change ∃ record, TaskRep D types path (.call name args)
      (let (child, _, _) := constructChild elaboration name values middle; Task.leaf child)
      record
    rw [constructChild_resolved elaboration name callee known values environment typed middle]
    exact ⟨_, .callActive path name args _⟩
  | join left right leftIH rightIH =>
    obtain ⟨leftRecord, leftRep⟩ := leftIH
      (fun name args member => resolved name args (List.mem_append_left _ member))
      (fun name args member => restored name args (List.mem_append_left _ member))
      (0 :: path) world
    simp only [makeTask]
    generalize makeTask (inducedModel elaboration calls prices normal) frame left world =
      leftStep at leftRep ⊢
    obtain ⟨leftTask, middle, leftCost⟩ := leftStep
    obtain ⟨rightRecord, rightRep⟩ := rightIH
      (fun name args member => resolved name args (List.mem_append_right _ member))
      (fun name args member => restored name args (List.mem_append_right _ member))
      (1 :: path) middle
    generalize makeTask (inducedModel elaboration calls prices normal) frame right middle =
      rightStep at rightRep ⊢
    obtain ⟨rightTask, after, rightCost⟩ := rightStep
    exact ⟨_, .joinActive leftRep rightRep⟩

private theorem restrictSlots {live kept : List String} {frame : Frame (Value D)}
    {fields : List (String × Parser.STyp)} {value}
    (slots : SlotsRep D types live frame fields value) (subset : kept ⊆ live) :
    ∃ value, SlotsRep D types kept frame fields value := by
  induction slots with
  | nil => exact ⟨(), .nil⟩
  | dead unused _ ih =>
    obtain ⟨_, rest⟩ := ih
    exact ⟨_, .dead (fun used => unused (subset used)) rest⟩
  | @live name _ _ _ _ _ _ found typed _ ih =>
    obtain ⟨_, rest⟩ := ih
    by_cases used : name ∈ kept
    · exact ⟨_, .live used found typed rest⟩
    · exact ⟨_, .dead used rest⟩

public theorem liveSlot {live : List String} {frame : Frame (Value D)}
    {fields : List (String × Parser.STyp)} {slots}
    (represented : SlotsRep D types live frame fields slots)
    (field : (name, sourceType) ∈ fields) (used : name ∈ live) :
    ∃ value ordinary, frame.values.lookup name = some value ∧
      valueAt D (types.ordinary sourceType) value = some ordinary := by
  induction represented with
  | nil => cases field
  | dead unused _ ih =>
    rcases List.mem_cons.mp field with same | member
    · cases same
      exact (unused used).elim
    · exact ih member
  | live _ found typed _ ih =>
    rcases List.mem_cons.mp field with same | member
    · cases same
      exact ⟨_, _, found, typed⟩
    · exact ih member

private theorem restoreLiveLocals {live : List String} {frame : Frame (Value D)}
    {fields : List (String × Parser.STyp)} {slots}
    (represented : SlotsRep D types live frame fields slots) (locals : List (String × Ty))
    (declared : ∀ name type, (name, type) ∈ locals →
      ∃ sourceType, (name, sourceType) ∈ fields ∧ name ∈ live ∧ types.ordinary sourceType = type) :
    ∃ environment, localsEnv D locals frame = some environment := by
  induction locals with
  | nil => exact ⟨.nil, rfl⟩
  | cons localEntry rest ih =>
    obtain ⟨name, type⟩ := localEntry
    obtain ⟨sourceType, field, liveName, same⟩ := declared name type List.mem_cons_self
    obtain ⟨value, ordinary, lookup, typed⟩ := liveSlot represented field liveName
    obtain ⟨tail, restored⟩ := ih (fun name type member =>
      declared name type (List.mem_cons_of_mem _ member))
    subst type
    exact ⟨.cons ordinary tail, by simp only [localsEnv, lookup, typed, restored,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]⟩

/-- An actual await instruction enters the waiting phase with the same
    semantic frame and a fully represented child. Frame storage retains
    the slots live in the continuation. -/
public theorem await_construction_rep (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (tag : Nat) (name : String) (future : FutureExpr) (boundary : Boundary)
    (rest : List Command)
    (command : f.body.drop tag = Command.await name future boundary :: rest)
    (frame : Frame (Value D)) (frameValue : Wert D (frameType types f))
    (slots : FrameRep D types f (Phase.running tag) frame frameValue)
    (localTypes : AwaitLocalOrigins elaboration tag future)
    (world : World D) :
    let model := inducedModel elaboration calls prices normal
    let built := makeTask model frame future world
    machineStep model (asyncExpand model f) (.running tag frame) world =
        (.next, .waiting tag frame built.1, built.2.1, built.2.2 + 1) ∧
      ∃ payload, PhaseRep D types f (Phase.waiting tag future) (.waiting tag frame built.1) payload := by
  have subset : liveAt f (Phase.waiting tag future) ⊆ liveAt f (Phase.running tag) := by
    simp only [liveAt, command, liveBefore]
    intro localName member
    exact List.mem_append_right _ member
  obtain ⟨waitingValue, waitingSlots⟩ := restrictSlots slots.slots subset
  have waitingFrame : FrameRep D types f (Phase.waiting tag future) frame waitingValue :=
    ⟨waitingSlots, fun name member => slots.declared name (subset member), slots.unique⟩
  have member : Command.await name future boundary ∈ f.body :=
    List.mem_of_mem_drop (by rw [command]; exact List.mem_cons_self)
  obtain ⟨record, represented⟩ :=
    makeTask_rep elaboration calls prices normal frame future
      (fun callee args leaf => elaboration.arguments callee args
        (List.mem_flatMap.mpr ⟨_, member, leaf⟩))
      (fun callee args leaf source argument expression known =>
        restoreLiveLocals slots.slots expression.locals
          (localTypes callee args leaf source argument expression known)) [tag] world
  simp only [machineStep, table_drop, command, List.map_cons, compileCommand]
  generalize makeTask (inducedModel elaboration calls prices normal) frame future world =
    constructed at represented ⊢
  obtain ⟨task, after, cost⟩ := constructed
  exact ⟨True.intro, _, .waiting tag future frame task waitingValue record waitingFrame represented⟩

private theorem waitingPhaseList {frame : Frame (Value D)} {task : Task (Value D) (Child D types)}
    (inventory : Inventory D) (base offset tag : Nat) (commands : List Command)
    {name : String} {future : FutureExpr} {boundary : Boundary} {remaining : List Command}
    (found : commands.drop offset = Command.await name future boundary :: remaining)
    (tagIndex : tag = base + offset)
    (payload : ∃ value, PhaseRep D types f (.waiting tag future) (.waiting tag frame task) value)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task)) :
    ∃ record, PhaseListRep D types f inventory (commandPhases base commands)
      (.waiting tag frame task) record := by
  induction offset generalizing base commands with
  | zero =>
    simp only [List.drop_zero] at found
    subst commands
    have same : tag = base := by simpa only [Nat.add_zero] using tagIndex
    subst tag
    obtain ⟨value, represented⟩ := payload
    exact ⟨_, .later _ _ _ _ rfl (.first _ _ _ value represented marks)⟩
  | succ offset ih =>
    cases commands with
    | nil => simp at found
    | cons first rest =>
      simp only [List.drop_succ_cons] at found
      have nextTag : tag = base + 1 + offset := by omega
      obtain ⟨_, represented⟩ := ih (base + 1) rest found nextTag
      cases first with
      | bind =>
        exact ⟨_, .later _ _ _ _ rfl represented⟩
      | await _ earlier _ =>
        have different : tag ≠ base := by omega
        have skipped : encodePhase D types f (.waiting base earlier) (.waiting tag frame task) =
            none := by simp only [encodePhase, ite_eq_right different]
        exact ⟨_, .later _ _ _ _ rfl (.later _ _ _ _ skipped represented)⟩

private theorem waiting_phase_inv (inventory : Inventory D) (tag : Nat)
    {name : String} {future : FutureExpr} {boundary : Boundary} {remaining : List Command}
    (found : f.body.drop tag = Command.await name future boundary :: remaining)
    {frame : Frame (Value D)} {task : Task (Value D) (Child D types)}
    (payload : ∃ value, PhaseRep D types f (.waiting tag future) (.waiting tag frame task) value)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task)) :
    ∃ record, Inv f types inventory (.waiting tag frame task) record ∧
      encode D types f (.waiting tag frame task) = some record := by
  obtain ⟨sum, represented⟩ := waitingPhaseList (types := types) (f := f) inventory 0 tag tag f.body found
    (Nat.zero_add tag).symm payload marks
  let cases := commandPhases 0 f.body
  let wrapped := laterPhaseValue D types f Phase.cancelled (Phase.completed :: cases)
    (laterPhaseValue D types f Phase.completed cases sum)
  have exactRecord : Inv f types inventory (.waiting tag frame task) (wrapped, ()) :=
    .later _ _ _ _ rfl (.later _ _ _ _ rfl represented)
  exact ⟨(wrapped, ()), exactRecord, inv_encoded f types inventory _ _ exactRecord⟩

/-- A represented await belongs to the full generated state record at its
    declared tag. The saved inventory is the one carried into construction. -/
public theorem waiting_construction_inv (inventory : Inventory D) (tag : Nat)
    {name : String} {future : FutureExpr} {boundary : Boundary} {remaining : List Command}
    (found : f.body.drop tag = Command.await name future boundary :: remaining)
    {frame : Frame (Value D)} {task : Task (Value D) (Child D types)}
    (payload : ∃ value, PhaseRep D types f (.waiting tag future) (.waiting tag frame task) value)
    (current : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag)) :
    ∃ record, Inv f types inventory (.waiting tag frame task) record ∧
      encode D types f (.waiting tag frame task) = some record :=
  waiting_phase_inv inventory tag found payload
    (by simpa only [MarksRep, State.marks, sameInventory] using current)

private theorem runningPhaseFrame {inventory : Inventory D} {cases : List Phase}
    {source : State (Value D) (Child D types)} {sum}
    (record : PhaseListRep D types f inventory cases source sum) :
    ∀ tag frame, source = .running tag frame →
      ∃ frameValue, FrameRep D types f (.running tag) frame frameValue ∧
        MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame) := by
  induction record with
  | first _ _ _ _ phase marks =>
    intro tag frame running
    cases phase <;> cases running
    exact ⟨_, ‹FrameRep D types f _ _ _›, marks⟩
  | later _ _ _ _ _ _ ih => exact ih

/-- The actual construction step preserves the complete encoded-state
    invariant and leaves the ordinary resource index untouched. The input
    record supplies its own running frame and ownership evidence. -/
public theorem await_construction_preserves
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (inventory : Inventory D) (tag : Nat) (name : String) (future : FutureExpr)
    (boundary : Boundary) (remaining : List Command)
    (command : f.body.drop tag = Command.await name future boundary :: remaining)
    (frame : Frame (Value D)) (record : Wert D (stateType types f))
    (represented : Inv f types inventory (.running tag frame) record)
    (owned : checkAwaitInventory inventory tag future = true)
    (localTypes : checkAwaitLocalOrigins elaboration tag future = true)
    (world : World D) :
    let model := inducedModel elaboration calls prices normal
    let built := makeTask model frame future world
    let waiting := State.waiting tag frame built.1
    machineStep model (asyncExpand model f) (.running tag frame) world =
      (.next, waiting, built.2.1, built.2.2 + 1) ∧
    inventory.resources (.waiting tag future) = inventory.resources (.running tag) ∧
    ∃ next, Inv f types inventory waiting next ∧ encode D types f waiting = some next := by
  obtain ⟨_, slots, marks⟩ := runningPhaseFrame (show PhaseListRep D types f inventory (phases f)
    (.running tag frame) record.1 from represented) tag frame rfl
  obtain ⟨stepped, payload⟩ :=
    await_construction_rep elaboration calls prices normal tag name future boundary remaining command
      frame _ slots (checkAwaitLocalOrigins_sound elaboration tag future localTypes) world
  have sameInventory := checkAwaitInventory_sound inventory tag future owned
  refine ⟨stepped, ?_, waiting_construction_inv inventory tag command payload marks sameInventory⟩
  rw [inventory.exact, inventory.exact, sameInventory]

/-- A Pending poll retains the phase tag, frame and owned marks, and
    re-encodes the actual successor child, including partial joins. -/
public theorem await_pending_preserves
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (inventory : Inventory D) (tag : Nat) (name : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await name future boundary :: rest)
    (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (saved : Wert D (frameType types f)) (child : Wert D (taskStorageType types [tag] future))
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    (represented : TaskRep D types [tag] future task child)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (world : World D) :
    let model := inducedModel elaboration calls prices normal
    let answer := pollTask model task world
    answer.1 = .pending →
    machineStep model (asyncExpand model f) (.waiting tag frame task) world =
      (.pending, .waiting tag frame answer.2.1, answer.2.2.1, answer.2.2.2 + 1) ∧
    ∃ next, Inv f types inventory (.waiting tag frame answer.2.1) next ∧
      encode D types f (.waiting tag frame answer.2.1) = some next := by
  intro model answer pending
  have member : Command.await name future boundary ∈ f.body :=
    List.mem_of_mem_drop (by rw [command]; exact List.mem_cons_self)
  have polled : PollRep D types [tag] future answer.1 answer.2.1 :=
    await_poll_rep elaboration calls prices normal tag name future boundary member represented world
  obtain ⟨storage, childStored⟩ := polled.storage
  have newMarks : MarksRep inventory (.waiting tag future) (.waiting tag frame answer.2.1) := marks
  refine ⟨?_, waiting_phase_inv inventory tag command ⟨(saved, storage, ()), ?_⟩ newMarks⟩
  · simp only [machineStep, table_drop, command, List.map_cons, compileCommand]
    change (match answer.1 with
      | .pending => (Event.pending, State.waiting tag frame answer.2.1, answer.2.2.1, answer.2.2.2 + 1)
      | .ready value => (Event.next, State.running (tag + 1) (save frame name value), answer.2.2.1, answer.2.2.2 + 1)) = _
    rw [pending]
  · exact .waiting tag future frame answer.2.1 saved storage slots childStored

end Gabbro.Grammatik.Async.Representation
