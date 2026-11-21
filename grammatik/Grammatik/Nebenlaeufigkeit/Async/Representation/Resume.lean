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
      · exact (unique.1 (List.mem_map_of_mem tail)).elim
    · rcases List.mem_cons.mp right with atHead | tail
      · subst head
        exact (unique.1 (List.mem_map_of_mem deeper)).elim
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

/-- A Ready answer initializes the destination of the await at its
    declared type. Every other live continuation slot keeps its earlier
    value, and the frame's authority marks are unchanged. -/
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
  have wasLive (name : String) (needed : name ∈ liveAt f (.running (tag + 1)))
      (different : name ≠ destination) : name ∈ liveAt f (.waiting tag future) := by
    simp only [liveAt, tail] at needed
    simp only [liveAt, command, without, List.mem_filter, needed, beq_eq_false_iff_ne.mpr different,
      Bool.not_false, and_self]
  have declared : (destination, sourceType) ∈ f.params ++ f.fields := by
    obtain ⟨before, after, placed, _⟩ := List.lookup_eq_some_iff.mp binding
    rw [placed]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨slots, represented⟩ := encodeLiveSlots (types := types) (save frame destination value)
    (liveAt f (.running (tag + 1))) (f.params ++ f.fields) (by
      intro name τ entry needed
      by_cases same : name = destination
      · subst name
        have sameType := sourceTypeUnique waiting.unique entry declared
        subst τ
        exact ⟨value, ordinary, List.lookup_cons_self, typed⟩
      · obtain ⟨old, oldValue, found, exactType⟩ := liveSlot waiting.slots entry (wasLive name needed same)
        refine ⟨old, oldValue, ?_, exactType⟩
        simpa only [save, List.lookup_cons, beq_eq_false_iff_ne.mpr same] using found)
  refine ⟨slots, ⟨represented, ?_, waiting.unique⟩, rfl⟩
  intro name needed
  by_cases same : name = destination
  · subst name
    exact List.mem_map_of_mem declared
  · exact waiting.declared name (wasLive name needed same)

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
  have member : Command.await destination future boundary ∈ f.body :=
    List.mem_of_mem_drop (by rw [command]; exact List.mem_cons_self)
  have polled : PollRep D types [tag] future answer.1 answer.2.1 :=
    await_poll_rep elaboration calls prices normal tag destination future boundary member represented world
  have typedOnReady {event : Poll (Value D)} {next : Task (Value D) (Child D types)}
      (progress : PollRep D types [tag] future event next) (isReady : event = .ready value) :
      ∃ ordinary, valueAt D (taskResultType types [tag] future) value = some ordinary := by
    cases progress with
    | pending _ => cases isReady
    | ready typed _ =>
      cases isReady
      exact ⟨_, typed⟩
  have typedResult := typedOnReady polled ready
  obtain ⟨sourceType, binding, exactType⟩ := elaboration.awaited tag destination future boundary rest command
  have resolved : ∃ ordinary, valueAt D (types.ordinary sourceType) value = some ordinary :=
    (show taskResultType types [tag] future = types.ordinary sourceType from exactType) ▸ typedResult
  obtain ⟨_, typed⟩ := resolved
  refine ⟨?_, await_resume_frame tag destination future boundary rest command slots binding typed⟩
  simp only [machineStep, table_drop, command, List.map_cons, compileCommand]
  rw [show (pollTask model task world).1 = Poll.ready value from ready]

end Gabbro.Grammatik.Async.Representation
