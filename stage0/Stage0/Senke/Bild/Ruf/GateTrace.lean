module

public import Stage0.Senke.Images.Correctness
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- A guarded oracle call contributes exactly one source foreign event.
    Reading the arguments and recording the declared writes retain their
    order in the full run without adding another foreign event. -/
theorem imageSourceForeignEvents_call {D : Deklaration} {O : Orakel D} (oracle : GutO O)
    (thread : Faden) (routine : D.Ax) (before : World D) (held : List (Res D))
    (reads : List (D.Tab ⊕ D.Glob)) (arguments : Env D (D.aparams routine))
    (writeTabs : ∀ t, D.aschreibt routine t = true → ∀ l, Sum.inl l ∈ D.braucht t → l ∈ before.haelt)
    (writeGlobs : ∀ g, D.agschreibt routine g = true → ∀ l, Sum.inl l ∈ D.gbraucht g → l ∈ before.haelt)
    {added : List (Ereignis D)}
    (events : (O.wirkt routine ((before.lese held reads).fragt (.inl routine)) arguments).1.spur =
      added ++ before.spur) :
    imageSourceForeignEvents (rufEigenG thread added) = [(thread, routine)] := by
  let readEvent : D.Tab ⊕ D.Glob → Ereignis D := fun carrier => match carrier with
    | .inl table => .zugriff table false held before.haelt
    | .inr global => .gzugriff global false held before.haelt
  let question := (before.lese held reads).fragt (.inl routine)
  have sameHeld : question.haelt = before.haelt := by
    change (before.lese held reads).haelt = before.haelt
    exact lese_haelt before held reads
  obtain ⟨tabs, globs, visible, _, _, _, _, _, _, written⟩ :=
    (oracle routine question arguments).2.2 (sameHeld.symm ▸ writeTabs) (sameHeld.symm ▸ writeGlobs)
  let writes := axiomSpur tabs globs routine visible question.haelt
  have logEq : added = writes ++ [.fremd (.inl routine)] ++ reads.map readEvent := by
    apply List.append_cancel_right (bs := before.spur)
    change (O.wirkt routine question arguments).1.spur = added ++ before.spur at events
    rw [← events, written]
    simp only [question, writes, World.fragt, World.lese, World.merke, readEvent, List.append_assoc] <;> rfl
  let observation : Ereignis D → Option (Faden × D.Ax) := fun event => match event with
    | .fremd (.inl called) => some (thread, called)
    | _ => none
  have readsSilent : (reads.map readEvent).filterMap observation = [] := by
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro carrier _
    cases carrier <;> rfl
  have writesSilent : writes.filterMap observation = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro event member
    rcases axiomSpur_mem member with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have projected : ((writes ++ [Ereignis.fremd (.inl routine)] ++ reads.map readEvent).reverse).filterMap
      observation = [(thread, routine)] := by
    simp only [List.reverse_append, List.filterMap_append, List.filterMap_reverse,
      readsSilent, writesSilent, List.reverse_nil, List.nil_append, List.append_nil]
    rfl
  rw [logEq, imageSourceForeignEvents, rufEigenG, List.filterMap_map]
  exact projected

/-- Internal runner requests leave the foreign history intact when the
    corresponding GX segment adds no foreign event. -/
theorem ImageForeignTrace.appendInternal {output : Emitted src reserve options}
    {history events : List Ev} {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (matched : ImageForeignTrace output history before)
    (internal : ∀ event ∈ events, imageExternalEvent event = false)
    (silent : imageSourceForeignEvents after.m.lauf = imageSourceForeignEvents before.m.lauf) :
    ImageForeignTrace output (history ++ events) after := by
  have noExternal : events.filter imageExternalEvent = [] :=
    List.filter_eq_nil_iff.mpr (fun event member => by rw [internal event member]; decide)
  simpa only [ImageForeignTrace, List.filter_append, noExternal, List.append_nil, silent] using matched

/-- A matched host response extends the global trace by the call taken
    by the actual issuing GX thread. -/
theorem ImageForeignTrace.appendGate [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {event : Ev} {returned : Cfg imageTSO (Res T)}
    {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (matched : ImageForeignTrace output history before) (external : imageExternalEvent event = true)
    (call : ImageGateEvent output E O before after returned event) :
    ImageForeignTrace output (history ++ [event]) after := by
  obtain ⟨_, _, routine, _, _, _, _, _, _, log, _, gate, _, _, present, number, _⟩ := call
  unfold ImageForeignTrace at matched ⊢
  rw [log, List.filter_append]
  simp only [List.filter_cons, external, ite_true, List.filter_nil]
  exact List.rel_append matched (.cons ⟨rfl, gate, present, number⟩ .nil)

/-- Reading a syscall's register arguments is unaffected by adding the
    purely logical idle function. The transport uses only word parameters. -/
theorem Senke.ArgsW.withIdle_words {D : Deklaration} {L : Senke.Lay D} :
    {types : List Ty} → (args : Env D types) → ∀ {registers : Nat → W},
      types.all wortTy = true → ArgsW L registers args →
        ArgsW L.withIdle registers (envR args)
  | [], .nil, _, _, _ => trivial
  | τ :: _, .cons value rest, registers, types, encoded => by
    obtain ⟨wordType, restTypes⟩ := Bool.and_eq_true_iff.mp types
    change ((if isPtr (tyR τ) then True else Enc L.withIdle (tyR τ) (valR τ value) (registers 0)) ∧ _)
    refine ⟨?_, ArgsW.withIdle_words rest restTypes encoded.2⟩
    cases τ <;> first | exact encoded.1 | cases wordType

/-- A real response to a returning scalar gate supplies the observed
    word and the model answer on the exact issuing thread and call. -/
theorem image_plain_gate_answer [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    (answers : ImageGateAnswers output.image.Y O)
    {before : Cfg imageTSO (Res T)} {memory : imageTSO.St} {thread : Nat}
    {req : Req} {resume : Ans → Res T} {answer : Ans}
    (waiting : before.ths[thread]? = some (some (.ask (.sys req) resume)))
    (ordinary : (Op.sys req).special = false)
    (answered : imageTSO.ans before.ms thread (.sys req) answer memory)
    (routine : (declOf output.compiled.unit).Ax) (gate : TorB)
    (selected : output.image.Y.tor routine = some gate)
    (transport : torGut gate ((declOf output.compiled.unit).aparams routine).length = true)
    (scalar : ptrParam ((declOf output.compiled.unit).aparams routine) = none)
    (types : ((declOf output.compiled.unit).aparams routine).all wortTy = true)
    (world : World (declOf output.compiled.unit))
    (args : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).aparams routine))
    (number : req.nr = BitVec.ofNat 64 gate.nr) (registers : ArgsW output.image.Y (reqArg req) args)
    (unused : ∀ i, ((declOf output.compiled.unit).aparams routine).length ≤ i → i < 6 → reqArg req i = 0)
    (represented : WeltAt (before.ms.1.view thread) output.image.Y world)
    {first site last : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (atCall : ImageReach output E O first site) (afterCall : ImageReach output E O site last)
    (alive : site.lebt thread = true) (sourceMemory : Speicher (declOf output.compiled.unit).mitRuhe)
    (key : (mitSpeicher site.m sourceMemory).foreignCallKey thread = some ⟨routine, worldR world, envR args⟩)
    (carriers : ∀ carrier, ¬ GeteiltV (D := declOf output.compiled.unit) E.P E.ws carrier →
      TraegerGleich sourceMemory site.m.speicher carrier)
    (observed : imageSourceForeignEvents last.m.lauf = imageSourceForeignEvents first.m.lauf ++ [(thread, routine)]) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set thread (some (resume answer))⟩
    ProcessStep imageTSO actI before [(thread, req, answer)] after ∧
      ImageGateEvent output E O first last after (thread, req, answer) ∧
      KernW output.image.Y (before.ms.1.view thread) (after.ms.1.view thread) ∧
      WeltAt (after.ms.1.view thread) output.image.Y (O.wirkt routine world args).1 := by
  intro after
  have otherRequest : req ≠ cloneReq := by
    rintro rfl
    exact (by decide : ¬ (Op.sys cloneReq).special = false) ordinary
  have external := answered.2
  change (if req = cloneReq then _ else
    Kern.ans req (before.ms.1.view thread) answer (memory.1.view thread) ∧
      memory.1.buf = before.ms.1.buf) at external
  rw [if_neg otherRequest] at external
  obtain ⟨word, extra, response, frame, nextWorld, outcome⟩ :=
    answers.plain routine gate selected transport scalar world args req (before.ms.1.view thread)
      number registers unused represented answer (memory.1.view thread) external.1
  have noArea : gate.resultArea = none := by
    have checked := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp transport).2).2
    exact Option.isNone_iff_eq_none.mp checked
  refine ⟨.ask waiting rfl ordinary answered rfl, ?_, frame, nextWorld⟩
  refine ⟨site, sourceMemory, routine, worldR world, envR args, atCall, afterCall, alive, key, observed,
    carriers, gate, word, extra, selected, number, ArgsW.withIdle_words args types registers, response, .inl ⟨noArea, ?_⟩⟩
  rw [wirkt_mitRuhe O]
  exact outcome

end Gabbro.Stage0
