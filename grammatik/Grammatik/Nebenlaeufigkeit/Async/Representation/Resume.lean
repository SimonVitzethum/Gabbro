module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Construction

namespace Gabbro.Grammatik.Async.Representation

open Segment

variable {D : Deklaration} {types : TypeResolution} {f : AsyncFn}

private theorem sourceTypeUnique {fields : List (String × Parser.STyp)} {name : String}
    {first second : Parser.STyp} (unique : (fields.map Prod.fst).Nodup)
    (left : (name, first) ∈ fields) (right : (name, second) ∈ fields) : first = second := by
  induction fields with
  | nil => cases left
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp left with atHead | deeper
    · subst head
      rcases List.mem_cons.mp right with equal | tail
      · exact (congrArg Prod.snd equal).symm
      · exact (unique.1 (List.mem_map.mpr ⟨(name, second), tail, rfl⟩)).elim
    · rcases List.mem_cons.mp right with atHead | tail
      · subst head
        exact (unique.1 (List.mem_map.mpr ⟨(name, first), deeper, rfl⟩)).elim
      · exact ih unique.2 deeper tail

private theorem encodeLiveSlots (frame : Frame (Value D)) (live : List String)
    (fields : List (String × Parser.STyp))
    (contents : ∀ name sourceType, (name, sourceType) ∈ fields → name ∈ live →
      ∃ value ordinary, frame.values.lookup name = some value ∧
        valueAt D (types.ordinary sourceType) value = some ordinary) :
    ∃ slots, SlotsRep D types live frame fields slots := by
  induction fields with
  | nil => exact ⟨(), .nil⟩
  | cons field fields ih =>
    obtain ⟨name, sourceType⟩ := field
    obtain ⟨_, rest⟩ := ih (fun other τ member => contents other τ (List.mem_cons_of_mem _ member))
    by_cases used : name ∈ live
    · obtain ⟨_, _, found, typed⟩ := contents name sourceType List.mem_cons_self used
      exact ⟨_, .live used found typed rest⟩
    · exact ⟨_, .dead used rest⟩

private theorem store_frame {phase nextPhase : Phase} (destination : String)
    {frame : Frame (Value D)} {record : Wert D (frameType types f)}
    (current : FrameRep D types f phase frame record)
    (retain : ∀ name, name ∈ liveAt f nextPhase → name ≠ destination → name ∈ liveAt f phase)
    {value : Value D} {sourceType : Parser.STyp} {ordinary : Wert D (types.ordinary sourceType)}
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (typed : valueAt D (types.ordinary sourceType) value = some ordinary) :
    ∃ next, FrameRep D types f nextPhase (save frame destination value) next ∧
      (save frame destination value).marks = frame.marks := by
  have declared : (destination, sourceType) ∈ f.params ++ f.fields := by
    obtain ⟨before, after, placed, _⟩ := List.lookup_eq_some_iff.mp binding
    rw [placed]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨slots, represented⟩ := encodeLiveSlots (types := types) (save frame destination value)
    (liveAt f nextPhase) (f.params ++ f.fields) (by
      intro name τ entry needed
      by_cases same : name = destination
      · subst name
        have sameType := sourceTypeUnique current.unique entry declared
        subst τ
        exact ⟨value, ordinary, List.lookup_cons_self, typed⟩
      · obtain ⟨old, oldValue, found, exactType⟩ := liveSlot current.slots entry (retain name needed same)
        refine ⟨old, oldValue, ?_, exactType⟩
        simpa only [save, List.lookup_cons, beq_eq_false_iff_ne.mpr same] using found)
  refine ⟨slots, ⟨represented, ?_, current.unique⟩, rfl⟩
  intro name needed
  by_cases same : name = destination
  · subst name
    exact List.mem_map_of_mem declared
  · exact current.declared name (retain name needed same)

/-- A Ready answer initializes the declared destination and retains
    the values and authority marks needed at the next command. -/
public theorem await_resume_frame (tag : Nat) (destination : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    {frame : Frame (Value D)} {record : Wert D (frameType types f)}
    (waiting : FrameRep D types f (.waiting tag future) frame record)
    {value : Value D} {sourceType : Parser.STyp} {ordinary : Wert D (types.ordinary sourceType)}
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (typed : valueAt D (types.ordinary sourceType) value = some ordinary) :
    ∃ next, FrameRep D types f (.running (tag + 1)) (save frame destination value) next ∧
      (save frame destination value).marks = frame.marks := by
  have tail : f.body.drop (tag + 1) = rest := by
    rw [← List.drop_drop, command]
    rfl
  apply store_frame destination waiting _ binding typed
  intro name needed different
  simp only [liveAt, tail] at needed
  simp only [liveAt, command, without, List.mem_filter, needed, beq_eq_false_iff_ne.mpr different,
    Bool.not_false, and_self]

/-- An ordinary bind in an async function saves its typed result and
    retains every other live value in the continuation. -/
public theorem bind_resume_frame (tag : Nat) (destination : String) (expression : Parser.SExpr)
    (bound : Nat) (rest : List Command)
    (command : f.body.drop tag = Command.bind destination expression bound :: rest)
    {frame : Frame (Value D)} {record : Wert D (frameType types f)}
    (current : FrameRep D types f (.running tag) frame record)
    {value : Value D} {sourceType : Parser.STyp} {ordinary : Wert D (types.ordinary sourceType)}
    (binding : (f.params ++ f.fields).lookup destination = some sourceType)
    (typed : valueAt D (types.ordinary sourceType) value = some ordinary) :
    ∃ next, FrameRep D types f (.running (tag + 1)) (save frame destination value) next ∧
      (save frame destination value).marks = frame.marks := by
  have tail : f.body.drop (tag + 1) = rest := by
    rw [← List.drop_drop, command]
    rfl
  apply store_frame destination current _ binding typed
  intro name needed different
  simp only [liveAt, tail] at needed
  simp only [liveAt, command, liveBefore, List.mem_append, without, List.mem_filter, needed,
    beq_eq_false_iff_ne.mpr different, Bool.not_false, and_self, or_true]

/-- A successful poll of the resolved child restores the typed continuation
    frame. The call semantics may also produce a logic or hardware outcome. -/
public theorem await_runTaskPoll_ready_frame {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (tag : Nat) (destination : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    {frame : Frame (Value D)} {saved : Wert D (frameType types f)}
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    {task successor : Task (Value D) (Child D types)}
    {child : Wert D (taskStorageType types [tag] future)}
    (represented : TaskRep D types [tag] future task child)
    {world after : World D} {value : Value D} {cost : Nat}
    (successful : runTaskPoll elaboration calls prices task world =
      .ok (.ready value, successor, after, cost)) :
    successor = .ready value ∧
    ∃ next, FrameRep D types f (.running (tag + 1)) (save frame destination value) next ∧
      (save frame destination value).marks = frame.marks := by
  have member : Command.await destination future boundary ∈ f.body :=
    List.mem_of_mem_drop (by rw [command]; exact List.mem_cons_self)
  have polled := await_runTaskPoll_rep elaboration calls prices tag destination future boundary
    member represented successful
  cases polled with
  | ready typed _ =>
    obtain ⟨sourceType, binding, exactType⟩ := elaboration.awaited tag destination future boundary rest command
    have resolved : ∃ ordinary, valueAt D (types.ordinary sourceType) value = some ordinary :=
      exactType ▸ (show ∃ ordinary, valueAt D (taskResultType types [tag] future) value = some ordinary
        from ⟨_, typed⟩)
    obtain ⟨_, typedAnswer⟩ := resolved
    exact ⟨rfl, await_resume_frame tag destination future boundary rest command slots binding typedAnswer⟩

/-- The actual Ready poll resumes at the next command with its typed
    answer bound once. Both the branch and its world come from the
    resolved child poll, including a completed join. -/
public theorem await_ready_resumes {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (tag : Nat) (destination : String) (future : FutureExpr) (boundary : Boundary)
    (rest : List Command) (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (saved : Wert D (frameType types f)) (child : Wert D (taskStorageType types [tag] future))
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    (represented : TaskRep D types [tag] future task child)
    (world : World D) (value : Value D) :
    let model := inducedModel elaboration calls prices normal
    let answer := pollTask model task world
    answer.1 = .ready value →
    machineStep model (asyncExpand model f) (.waiting tag frame task) world =
      (.next, .running (tag + 1) (save frame destination value), answer.2.2.1, answer.2.2.2 + 1) ∧
    ∃ next, FrameRep D types f (.running (tag + 1)) (save frame destination value) next ∧
      (save frame destination value).marks = frame.marks := by
  intro model answer ready
  have successful : runTaskPoll elaboration calls prices task world =
      .ok (.ready value, answer.2.1, answer.2.2.1, answer.2.2.2) := by
    rw [runTaskPoll_agrees_with_inducedModel elaboration calls prices normal task world, ← ready]
  refine ⟨?_, (await_runTaskPoll_ready_frame elaboration calls prices tag destination future boundary
    rest command slots represented successful).2⟩
  simp only [machineStep, table_drop, command, List.map_cons, compileCommand, waitingReply]
  rw [show (pollTask model task world).1 = Poll.ready value from ready]

private theorem runningPhaseList (inventory : Inventory D) (tag : Nat)
    {frame : Frame (Value D)} {saved : Wert D (frameType types f)}
    (slots : FrameRep D types f (.running tag) frame saved)
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (commands : List Command) (base offset : Nat) (bound : offset ≤ commands.length)
    (atTag : tag = base + offset) :
    ∃ sum, PhaseListRep D types f inventory (commandPhases base commands) (.running tag frame) sum := by
  induction commands generalizing base offset with
  | nil =>
    have same : tag = base := by
      simp only [List.length_nil, Nat.le_zero] at bound
      omega
    subst base
    exact ⟨_, .first _ _ _ _ (.running tag frame saved slots) marks⟩
  | cons command rest ih =>
    cases offset with
    | zero =>
      have same : tag = base := by simpa only [Nat.add_zero] using atTag
      subst base
      cases command with
      | bind => exact ⟨_, .first _ _ _ _ (.running tag frame saved slots) marks⟩
      | await => exact ⟨_, .first _ _ _ _ (.running tag frame saved slots) marks⟩
    | succ offset =>
      have shorter : offset ≤ rest.length := Nat.le_of_succ_le_succ bound
      have nextTag : tag = base + 1 + offset := by omega
      have different : tag ≠ base := by omega
      have skipRun : encodePhase D types f (.running base) (.running tag frame) = none := by
        change (if tag = base then encodeFrame D types f (.running base) frame else none) = none
        rw [if_neg different]
      obtain ⟨_, continuation⟩ := ih (base + 1) offset shorter nextTag
      cases command with
      | bind =>
        exact ⟨_, .later _ _ _ _ skipRun continuation⟩
      | await =>
        exact ⟨_, .later _ _ _ _ skipRun (.later _ _ _ _ rfl continuation)⟩

/-- The resolved ordinary expression of a bind produces a representable
    next state with its exact result and retained authority marks. -/
public theorem evaluateBind_preserves {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f) (inventory : Inventory D) (tag : Nat)
    (destination : String) (expression : Parser.SExpr) (bound : Nat) (rest : List Command)
    (command : f.body.drop tag = Command.bind destination expression bound :: rest)
    (resolved : BoundExpression D Λ) (known : elaboration.expression expression = some resolved)
    (frame : Frame (Value D)) (slots : Wert D (frameType types f))
    (current : FrameRep D types f (.running tag) frame slots)
    (marks : MarksRep inventory (.running tag) (.running (Child := Child D types) tag frame))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.running tag))
    (locals : Env D (resolved.locals.map Prod.snd))
    (restored : localsEnv D resolved.locals frame = some locals) (world : World D) :
    let answer := evaluateBound elaboration expression frame world
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination answer.1)
    ∃ record, Inv f types inventory resumed record ∧ encode D types f resumed = some record := by
  have member : Command.bind destination expression bound ∈ f.body :=
    List.mem_of_mem_drop (by rw [command]; exact List.mem_cons_self)
  obtain ⟨selected, sourceType, selectedAt, binding, exactType⟩ := elaboration.bound destination expression bound member
  have same := Option.some.inj (selectedAt.symm.trans known)
  subst selected
  simp only [evaluateBound_resolved elaboration expression resolved known frame locals restored world]
  let evaluated := evaluateExpression resolved.expression world locals
  let value := Value.typed resolved.result evaluated.1
  let resumed : State (Value D) (Child D types) := .running (tag + 1) (save frame destination value)
  change ∃ record, Inv f types inventory resumed record ∧ encode D types f resumed = some record
  have typed : valueAt D (types.ordinary sourceType) value = some (exactType ▸ evaluated.1) := by
    simp only [value, valueAt, dif_pos exactType]
  obtain ⟨_, saved, sameMarks⟩ := bind_resume_frame tag destination expression bound rest command current binding typed
  have within : tag + 1 ≤ f.body.length := by
    have length := congrArg List.length command
    simp only [List.length_drop, List.length_cons] at length
    omega
  have owned : MarksRep inventory (.running (tag + 1)) resumed := by
    simpa only [MarksRep, resumed, State.marks, sameMarks, sameInventory] using marks
  obtain ⟨_, running⟩ := runningPhaseList inventory (tag + 1) saved owned f.body 0 (tag + 1) within
    (Nat.zero_add (tag + 1)).symm
  have full : PhaseListRep D types f inventory (phases f) resumed _ :=
    .later _ _ _ _ rfl (.later _ _ _ _ rfl running)
  have invariant : Inv f types inventory resumed (_, ()) := full
  exact ⟨_, invariant, inv_encoded f types inventory resumed _ invariant⟩

/-- A Ready answer from the actual call semantics restores the complete
    encoded state when the enclosing frame retains its own inventory. -/
public theorem await_runTaskPoll_ready_preserves {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat)
    (inventory : Inventory D) (tag : Nat) (destination : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (saved : Wert D (frameType types f)) (child : Wert D (taskStorageType types [tag] future))
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    (represented : TaskRep D types [tag] future task child)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag future))
    {world after : World D} {value : Value D} {successor : Task (Value D) (Child D types)}
    {cost : Nat} (successful : runTaskPoll elaboration calls prices task world =
      .ok (.ready value, successor, after, cost)) :
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination value)
    successor = .ready value ∧
    inventory.resources (.running (tag + 1)) = inventory.resources (.waiting tag future) ∧
    ∃ record, Inv f types inventory resumed record ∧ encode D types f resumed = some record := by
  intro resumed
  obtain ⟨cached, _, restored, sameMarks⟩ :=
    await_runTaskPoll_ready_frame elaboration calls prices tag destination future boundary rest command
      slots represented successful
  have within : tag + 1 ≤ f.body.length := by
    have length := congrArg List.length command
    simp only [List.length_drop, List.length_cons] at length
    omega
  have owned : MarksRep inventory (.running (tag + 1)) resumed := by
    simpa only [MarksRep, resumed, State.marks, sameMarks, sameInventory] using marks
  obtain ⟨_, running⟩ := runningPhaseList inventory (tag + 1) restored owned f.body 0 (tag + 1) within
    (Nat.zero_add (tag + 1)).symm
  have full : PhaseListRep D types f inventory (phases f) resumed _ :=
    .later _ _ _ _ rfl (.later _ _ _ _ rfl running)
  have invariant : Inv f types inventory resumed (_, ()) := full
  refine ⟨cached, ?_, _, invariant, inv_encoded f types inventory resumed _ invariant⟩
  rw [inventory.exact, inventory.exact, sameInventory]

/-- The complete state and the ordinary table step agree in the total
    model when the supplied call environment always returns normally. -/
public theorem await_ready_preserves {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat) (normal : PollRuns elaboration calls)
    (inventory : Inventory D) (tag : Nat) (destination : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (saved : Wert D (frameType types f)) (child : Wert D (taskStorageType types [tag] future))
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    (represented : TaskRep D types [tag] future task child)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag future))
    (world : World D) (value : Value D) :
    let model := inducedModel elaboration calls prices normal
    let answer := pollTask model task world
    let resumed := State.running (Child := Child D types) (tag + 1) (save frame destination value)
    answer.1 = .ready value →
    machineStep model (asyncExpand model f) (.waiting tag frame task) world =
      (.next, resumed, answer.2.2.1, answer.2.2.2 + 1) ∧
    inventory.resources (.running (tag + 1)) = inventory.resources (.waiting tag future) ∧
    ∃ record, Inv f types inventory resumed record ∧ encode D types f resumed = some record := by
  intro model answer resumed ready
  have successful : runTaskPoll elaboration calls prices task world =
      .ok (.ready value, answer.2.1, answer.2.2.1, answer.2.2.2) := by
    rw [runTaskPoll_agrees_with_inducedModel elaboration calls prices normal task world, ← ready]
  refine ⟨?_, (await_runTaskPoll_ready_preserves elaboration calls prices inventory tag destination future
    boundary rest command frame task saved child slots represented marks sameInventory successful).2⟩
  simp only [machineStep, table_drop, command, List.map_cons, compileCommand, waitingReply]
  rw [show (pollTask model task world).1 = Poll.ready value from ready]

/-- A continuing wait driven by the actual G outcome preserves the
    complete encoded state. The retained inventory obligation applies
    on Ready, when the phase changes. -/
public theorem runWaitingPoll_preserves {V : Vertrag D} {Λ : List (Res D)}
    (elaboration : Elaboration D V Λ types f)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (prices : D.Fn → Nat)
    (inventory : Inventory D) (tag : Nat) (destination : String) (future : FutureExpr)
    (boundary : Boundary) (rest : List Command)
    (command : f.body.drop tag = Command.await destination future boundary :: rest)
    (frame : Frame (Value D)) (task : Task (Value D) (Child D types))
    (saved : Wert D (frameType types f)) (child : Wert D (taskStorageType types [tag] future))
    (slots : FrameRep D types f (.waiting tag future) frame saved)
    (represented : TaskRep D types [tag] future task child)
    (marks : MarksRep inventory (.waiting tag future) (.waiting tag frame task))
    (sameInventory : inventory.owned (.running (tag + 1)) = inventory.owned (.waiting tag future))
    {world after : World D} {event : Event (Value D)} {next : State (Value D) (Child D types)}
    {cost : Nat} (stepped : runWaitingPoll elaboration calls prices tag destination frame task world =
      .ok (event, next, after, cost)) :
    ∃ record, Inv f types inventory next record ∧ encode D types f next = some record := by
  cases polled : runTaskPoll elaboration calls prices task world with
  | error failure => simp only [runWaitingPoll, polled, reduceCtorEq] at stepped
  | ok answer =>
    obtain ⟨reply, successor, nextWorld, pollCost⟩ := answer
    cases reply with
    | pending =>
      simp only [runWaitingPoll, polled, waitingReply, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨_, rfl, _, _⟩ := stepped
      exact await_runTaskPoll_pending_preserves elaboration calls prices inventory tag destination future
        boundary rest command frame task saved child slots represented marks polled
    | ready value =>
      simp only [runWaitingPoll, polled, waitingReply, Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨_, rfl, _, _⟩ := stepped
      exact (await_runTaskPoll_ready_preserves elaboration calls prices inventory tag destination future
        boundary rest command frame task saved child slots represented marks sameInventory polled).2.2

end Gabbro.Grammatik.Async.Representation
