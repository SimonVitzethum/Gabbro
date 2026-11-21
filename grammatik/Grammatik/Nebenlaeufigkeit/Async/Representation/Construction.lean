module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.State
public import Grammatik.Nebenlaeufigkeit.Async.Segment.Model
public import Grammatik.Nebenlaeufigkeit.Async.Verfeinerung
import Lean.Elab.Tactic.Omega

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {V : Vertrag D} {Λ : List (Res D)}
  {types : TypeResolution} {f : AsyncFn}

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

private theorem liveSlot {live : List String} {frame : Frame (Value D)}
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
    (localTypes : ∀ callee args, FutureExpr.call callee args ∈ callsIn future →
      ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
        ∀ localName type, (localName, type) ∈ expression.locals →
          ∃ sourceType, (localName, sourceType) ∈ f.params ++ f.fields ∧
            localName ∈ liveAt f (Phase.running tag) ∧ types.ordinary sourceType = type)
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
    (inventory : Inventory D) (base offset : Nat) (commands : List Command)
    {name : String} {future : FutureExpr} {boundary : Boundary} {remaining : List Command}
    (found : commands.drop offset = Command.await name future boundary :: remaining)
    (payload : ∃ value, PhaseRep D types f (.waiting (base + offset) future)
      (.waiting (base + offset) frame task) value)
    (marks : MarksRep inventory (.waiting (base + offset) future) (.waiting (base + offset) frame task)) :
    ∃ record, PhaseListRep D types f inventory (commandPhases base commands)
      (.waiting (base + offset) frame task) record := by
  induction offset generalizing base commands with
  | zero =>
    simp only [List.drop_zero, Nat.add_zero] at found payload marks ⊢
    subst commands
    obtain ⟨value, represented⟩ := payload
    exact ⟨_, .later _ _ _ _ rfl (.first _ _ _ value represented marks)⟩
  | succ offset ih =>
    cases commands with
    | nil => simp at found
    | cons first rest =>
      simp only [List.drop_succ_cons] at found
      have moved : base + (offset + 1) = base + 1 + offset := by omega
      simp only [moved] at payload marks ⊢
      obtain ⟨_, represented⟩ := ih (base + 1) rest found payload marks
      cases first with
      | bind =>
        exact ⟨_, .later _ _ _ _ rfl represented⟩
      | await _ earlier _ =>
        have different : base + 1 + offset ≠ base := by omega
        have skipped : encodePhase D types f (.waiting base earlier) (.waiting (base + 1 + offset) frame task) =
            none := by simp only [encodePhase, ite_eq_right different]
        exact ⟨_, .later _ _ _ _ rfl (.later _ _ _ _ skipped represented)⟩

/-- A represented await belongs to the full generated state record at its
    declared tag. Every earlier case fails to encode this state. The
    saved resource inventory is the same one carried into construction. -/
public theorem waiting_construction_inv (inventory : Inventory D) (tag : Nat)
    {name : String} {future : FutureExpr} {boundary : Boundary} {remaining : List Command}
    (found : f.body.drop tag = Command.await name future boundary :: remaining)
    {frame : Frame (Value D)} {task : Task (Value D) (Child D types)}
    (payload : ∃ value, PhaseRep D types f (.waiting tag future) (.waiting tag frame task) value)
    (current : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag)) :
    ∃ record, Inv f types inventory (.waiting tag frame task) record ∧
      encode D types f (.waiting tag frame task) = some record := by
  have marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task) := by
    simpa only [MarksRep, State.marks, sameInventory] using current
  obtain ⟨sum, represented⟩ := waitingPhaseList (types := types) (f := f) inventory 0 tag f.body found
    (by simpa only [Nat.zero_add] using payload) (by simpa only [Nat.zero_add] using marks)
  let cases := commandPhases 0 f.body
  have selected : PhaseListRep D types f inventory cases (.waiting tag frame task) sum := by
    simpa only [Nat.zero_add] using represented
  let wrapped := laterPhaseValue D types f Phase.cancelled (Phase.completed :: cases)
    (laterPhaseValue D types f Phase.completed cases sum)
  have exactRecord : Inv f types inventory (.waiting tag frame task) (wrapped, ()) :=
    .later _ _ _ _ rfl (.later _ _ _ _ rfl selected)
  exact ⟨(wrapped, ()), exactRecord, inv_encoded f types inventory _ _ exactRecord⟩

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
    (sameInventory : inventory.owned (.waiting tag future) = inventory.owned (.running tag))
    (localTypes : ∀ callee args, FutureExpr.call callee args ∈ callsIn future →
      ∀ source ∈ args, ∀ expression, elaboration.expression source = some expression →
        ∀ localName type, (localName, type) ∈ expression.locals →
          ∃ sourceType, (localName, sourceType) ∈ f.params ++ f.fields ∧
            localName ∈ liveAt f (.running tag) ∧ types.ordinary sourceType = type)
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
      frame _ slots localTypes world
  refine ⟨stepped, ?_, waiting_construction_inv inventory tag command payload marks sameInventory⟩
  rw [inventory.exact, inventory.exact, sameInventory]

end Gabbro.Grammatik.Async.Representation
