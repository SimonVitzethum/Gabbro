module

public import Stage0.Senke.Images.Correctness
import Stage0.Senke.Bild.Mehr.ImageTransition
import Stage0.Senke.Welt.Spans.IdleValue
import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik.T2
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach
open Gabbro.Stage0.Senke.BildMehr

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
    (internal : ∀ event ∈ events, imageCanBeInternal event = true)
    (silent : imageSourceForeignEvents after.m.lauf = imageSourceForeignEvents before.m.lauf) :
    ImageForeignTrace output (history ++ events) after := by
  have noCalls : ImageForeignTraceAlignment output events [] := by
    induction events with
    | nil => exact .nil
    | cons event rest ih =>
      exact .internal (internal event List.mem_cons_self)
        (ih (fun later member => internal later (List.mem_cons_of_mem _ member)))
  unfold ImageForeignTrace at matched ⊢
  rw [silent, ← List.append_nil (imageSourceForeignEvents before.m.lauf)]
  exact matched.append noCalls

/-- A matched host response extends the global trace by the call taken
    by the actual issuing GX thread. -/
theorem ImageForeignTrace.appendGate [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {event : Ev} {returned : Cfg imageTSO (Res T)}
    {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (matched : ImageForeignTrace output history before)
    (call : ImageGateEvent output E O before after returned event) :
    ImageForeignTrace output (history ++ [event]) after := by
  obtain ⟨_, _, routine, _, _, _, _, _, _, log, _, gate, _, _, present, number, _⟩ := call
  unfold ImageForeignTrace at matched ⊢
  rw [log]
  exact matched.append (.gate rfl present number .nil)

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

private theorem image_host_answer [Kern] {before : Cfg imageTSO (Res T)} {after : imageTSO.St}
    {thread : Nat} {req : Req} {answer : Ans} (ordinary : (Op.sys req).special = false)
    (answered : imageTSO.ans before.ms thread (.sys req) answer after) :
    Kern.ans req (before.ms.1.view thread) answer (after.1.view thread) ∧ after.1.buf = before.ms.1.buf := by
  have notClone : req ≠ cloneReq := by
    rintro rfl
    exact (by decide : ¬ (Op.sys cloneReq).special = false) ordinary
  have external := answered.2
  change (if req = cloneReq then _ else
    Kern.ans req (before.ms.1.view thread) answer (after.1.view thread) ∧
      after.1.buf = before.ms.1.buf) at external
  rw [if_neg notClone] at external
  exact external

/-- A host answer's effect on the issuer's view determines the committed
    bytes at any reservation outside that issuer's stack. -/
private theorem image_gate_dormant_frame [Kern] {output : Emitted src reserve options}
    {before : Cfg imageTSO (Res T)} {after : imageTSO.St} {thread future : Nat} {control : Res T}
    (running : before.ths[thread]? = some (some control)) (unused : before.ths.length ≤ future)
    (buffers : PrivateBuffers (imageStackFootprint output) before.ms.1)
    (sameBuffers : after.1.buf = before.ms.1.buf)
    (outside : GleichAuf (imageStackFootprint output future) (before.ms.1.view thread) (after.1.view thread)) :
    GleichAuf (imageStackFootprint output future) before.ms.1.m after.1.m := by
  have distinct : thread ≠ future := by
    intro equal
    exact (Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp running).1) (equal.symm ▸ unused)
  intro byte reserved
  have untouched (store : W × W) (queued : store ∈ before.ms.1.buf thread) : ¬ fenster store.1 byte :=
    fun touched => distinct (imageStackFootprint_disjoint (buffers thread store queued byte touched).1 reserved)
  have current : GleichAt (after.1.view thread) after.1.m byte := by
    apply view_agrees_at
    intro store queued
    rw [sameBuffers] at queued
    exact untouched store queued
  exact (view_agrees_at untouched).symm.trans ((outside byte reserved).trans current)

private theorem stack_byte_below_world [Kern] {output : Emitted src reserve options}
    {thread : Nat} {byte : W} (reserved : imageStackFootprint output thread byte) :
    byte.toNat < output.image.Y.lo := by
  have slots : output.image.Ks * (thread + 1) ≤ output.image.Ks * (output.starts.length + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right reserved.1 1)
  have limit := (Nat.add_le_add_left (Nat.mul_le_mul_left 8 slots) output.image.fp0).trans
    output.stackReservation_bounds.1
  exact reserved.2.2.trans_le limit

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
      WeltAt (after.ms.1.view thread) output.image.Y (O.wirkt routine world args).1 ∧
      ∀ future, before.ths.length ≤ future → PrivateBuffers (imageStackFootprint output) before.ms.1 →
        GleichAuf (imageStackFootprint output future) before.ms.1.m after.ms.1.m := by
  intro after
  obtain ⟨answeredByHost, sameBuffers⟩ := image_host_answer ordinary answered
  obtain ⟨word, extra, response, frame, nextWorld, outcome⟩ :=
    answers.plain routine gate selected transport scalar world args req (before.ms.1.view thread)
      number registers unused represented answer (memory.1.view thread) answeredByHost
  have noArea : gate.resultArea = none := by
    have checked := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp transport).2).2
    exact Option.isNone_iff_eq_none.mp checked
  refine ⟨.ask waiting rfl ordinary answered rfl, ?_, frame, nextWorld, ?_⟩
  · refine ⟨site, sourceMemory, routine, worldR world, envR args, atCall, afterCall, alive, key, observed,
      carriers, gate, word, extra, selected, number, ArgsW.withIdle_words args types registers, response, .inl ⟨noArea, ?_⟩⟩
    rw [wirkt_mitRuhe O]
    exact outcome
  · intro future dormant buffers
    apply image_gate_dormant_frame waiting dormant buffers sameBuffers
    intro byte reserved
    have below := stack_byte_below_world reserved
    exact ⟨(frame.2.2 _ (fun hit => (Nat.not_le_of_lt below) hit.1)).symm,
      congrFun frame.1.symm byte, congrFun frame.2.1.symm byte⟩

private theorem foreignDecode_withIdle {D : Deklaration} (O : Orakel D) (routine : D.Ax) (raw : Int) :
    foreignDecode O.mitRuhe routine raw =
      (foreignDecode O routine raw).map (Sum.map (ergR (D.aerg routine)) id) := by
  unfold foreignDecode
  by_cases zero : D.agruende routine = 0
  · rw [if_pos (show D.mitRuhe.agruende routine = 0 from zero), if_pos zero]
    rw [einpassenErg_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)]
    cases einpassenErg O.zeiger (D.aerg routine) raw <;> rfl
  · rw [if_neg (show D.mitRuhe.agruende routine ≠ 0 from zero), if_neg zero]
    exact sonstPasst_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O) (D.aerg routine) (D.agruende routine) raw

private theorem ergWert_withIdle {D : Deklaration} {τ : Ty} {e : Option Ty}
    (typed : e = some τ) (value : ErgVal D e) :
    ergWert (congrArg (Option.map tyR) typed) (ergR e value) = valR τ (ergWert typed value) := by
  cases typed
  rfl

/-- The idle extension retains the exact result bytes or failure tag of
    a caller-owned result area, including aggregate and function values. -/
theorem Senke.AreaReply.withIdle {D : Deklaration} {L : Senke.Lay D} {O : Orakel D}
    {routine : D.Ax} {gate : TorB} {τ : Ty} {typed : D.aerg routine = some τ}
    {world : World D} {args : Env D (D.aparams routine)} {memory : Mem} {fp tag : W} {base : Nat}
    (reply : AreaReply L O routine gate τ typed world args memory fp base tag) :
    AreaReply L.withIdle O.mitRuhe routine gate (tyR τ) (congrArg (Option.map tyR) typed)
      (worldR world) (envR args) memory fp base tag := by
  unfold AreaReply at reply ⊢
  rw [wirkt_mitRuhe O, foreignDecode_withIdle]
  rcases reply with ⟨value, decoded, classified, bytes⟩ | ⟨reason, errno, decoded, classified⟩ |
    ⟨invalid, nonzero, unknown, fallible⟩
  · refine .inl ⟨ergR (D.aerg routine) value, ?_, classified, ?_⟩
    · rw [decoded]
      rfl
    · rw [ergWert_withIdle]
      exact bytes.withIdle
  · refine .inr (.inl ⟨reason, errno, ?_, classified⟩)
    rw [decoded]
    rfl
  · refine .inr (.inr ⟨?_, nonzero, unknown, fallible⟩)
    rw [invalid]
    rfl

/-- A running gate with a hidden result register delivers the exact
    source value or error tag in the actual caller-owned memory. -/
theorem image_area_gate_answer [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    (answers : ImageGateAnswers output.image.Y O)
    {before : Cfg imageTSO (Res T)} {memory : imageTSO.St} {thread : Nat}
    {req : Req} {resume : Ans → Res T} {answer : Ans}
    (waiting : before.ths[thread]? = some (some (.ask (.sys req) resume)))
    (ordinary : (Op.sys req).special = false)
    (answered : imageTSO.ans before.ms thread (.sys req) answer memory)
    (routine : (declOf output.compiled.unit).Ax) (gate : TorB)
    (τ : Ty) (typed : (declOf output.compiled.unit).aerg routine = some τ) (slotIndex : Nat)
    (selected : output.image.Y.tor routine = some gate)
    (transport : areaGut gate ((declOf output.compiled.unit).aparams routine).length slotIndex = true)
    (types : ((declOf output.compiled.unit).aparams routine).all wortTy = true)
    (world : World (declOf output.compiled.unit))
    (args : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).aparams routine))
    (fp : W) (base capacity : Nat)
    (frame : FrameOK (before.ms.1.view thread) fp capacity) (fits : base + valueWords τ ≤ capacity)
    (layout : LayIn output.image.Y) (belowWorld : fp.toNat + 8 * capacity ≤ output.image.Y.lo)
    (number : req.nr = BitVec.ofNat 64 gate.nr) (registers : ArgsW output.image.Y (reqArg req) args)
    (destination : reqArg req slotIndex = slot fp (BitVec.ofNat 64 base))
    (unused : ∀ i, ((declOf output.compiled.unit).aparams routine).length ≤ i → i < 6 →
      i ≠ slotIndex → reqArg req i = 0)
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
      AgreeW output.image.Y fp base (base + valueWords τ) (before.ms.1.view thread) (after.ms.1.view thread) ∧
      WeltAt (after.ms.1.view thread) output.image.Y (O.wirkt routine world args).1 ∧
      ∀ future, before.ths.length ≤ future → PrivateBuffers (imageStackFootprint output) before.ms.1 →
        (∀ byte, inSlots fp base (base + valueWords τ) byte → imageStackFootprint output thread byte) →
        GleichAuf (imageStackFootprint output future) before.ms.1.m after.ms.1.m := by
  intro after
  obtain ⟨answeredByHost, sameBuffers⟩ := image_host_answer ordinary answered
  obtain ⟨tag, extra, response, retained, nextWorld, reply⟩ :=
    answers.area routine gate τ typed slotIndex selected transport world args req (before.ms.1.view thread)
      fp base capacity frame fits layout belowWorld number registers destination unused represented
      answer (memory.1.view thread) answeredByHost
  have hasArea : gate.resultArea = some slotIndex :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp transport).2
  exact ⟨.ask waiting rfl ordinary answered rfl,
    ⟨site, sourceMemory, routine, worldR world, envR args, atCall, afterCall, alive, key, observed, carriers,
      gate, tag, extra, selected, number, ArgsW.withIdle_words args types registers, response,
      .inr ⟨slotIndex, tyR τ, congrArg (Option.map tyR) typed, fp, base, hasArea, destination, reply.withIdle⟩⟩,
    retained, nextWorld, ?_⟩
  intro future dormant buffers owned
  apply image_gate_dormant_frame waiting dormant buffers sameBuffers
  intro byte reserved
  have distinct : thread ≠ future := fun equal =>
    (Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp waiting).1) (equal.symm ▸ dormant)
  have outside : ¬ inSlots fp base (base + valueWords τ) byte :=
    fun hit => distinct (imageStackFootprint_disjoint (owned byte hit) reserved)
  have below := stack_byte_below_world reserved
  refine ⟨(retained.b _ outside (fun hit => (Nat.not_le_of_lt below) hit.1)
    (fun hit => (Nat.not_le_of_lt below) hit.1)).symm, congrFun retained.rd.symm byte, congrFun retained.wr.symm byte⟩

/-- A pointer-buffer gate reports its actual scalar result and leaves the
    table update encoded in just the caller's reserved scratch bytes.
    The subsequent unpacking uses the proven per-cell encodings. -/
theorem image_buffer_gate_answer [Kern] {output : Emitted src reserve options}
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
    (types : ((declOf output.compiled.unit).aparams routine).all wortTy = true)
    (pointer tableNumber : Nat) (writable : Bool) (table : (declOf output.compiled.unit).Tab)
    (field : (declOf output.compiled.unit).Feld table)
    (parameter : ptrParam ((declOf output.compiled.unit).aparams routine) = some (pointer, tableNumber, writable))
    (identified : (declOf output.compiled.unit).tabNr tableNumber = some table)
    (bytes : output.image.Y.byte table = some field) (byteType : (declOf output.compiled.unit).typ table field = .int 0 255)
    (world : World (declOf output.compiled.unit))
    (args : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).aparams routine))
    (number : req.nr = BitVec.ofNat 64 gate.nr) (registers : ArgsW output.image.Y (reqArg req) args)
    (unused : ∀ i, ((declOf output.compiled.unit).aparams routine).length ≤ i → i < 6 → reqArg req i = 0)
    (represented : WeltAt (before.ms.1.view thread) output.image.Y world)
    (packed : ∀ i, i < pufW ((declOf output.compiled.unit).count table).toNat →
      (before.ms.1.view thread).rd64 (reqArg req pointer + BitVec.ofNat 64 (8 * i)) =
        some (packV (fun k => wAt (before.ms.1.view thread) (output.image.Y.elem table field k))
          ((declOf output.compiled.unit).count table).toNat i 8))
    {first site last : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (atCall : ImageReach output E O first site) (afterCall : ImageReach output E O site last)
    (alive : site.lebt thread = true) (sourceMemory : Speicher (declOf output.compiled.unit).mitRuhe)
    (key : (mitSpeicher site.m sourceMemory).foreignCallKey thread = some ⟨routine, worldR world, envR args⟩)
    (carriers : ∀ carrier, ¬ GeteiltV (D := declOf output.compiled.unit) E.P E.ws carrier →
      TraegerGleich sourceMemory site.m.speicher carrier)
    (observed : imageSourceForeignEvents last.m.lauf = imageSourceForeignEvents first.m.lauf ++ [(thread, routine)]) :
    let prior := before.ms.1.view thread
    let current := memory.1.view thread
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set thread (some (resume answer))⟩
    ProcessStep imageTSO actI before [(thread, req, answer)] after ∧
      ImageGateEvent output E O first last after (thread, req, answer) ∧
      current.rd = prior.rd ∧ current.wr = prior.wr ∧
      (∀ y, ¬ ((reqArg req pointer).toNat ≤ y.toNat ∧
        y.toNat < (reqArg req pointer).toNat + 8 * pufW ((declOf output.compiled.unit).count table).toNat) →
        current.b y = prior.b y) ∧
      WeltOhne prior output.image.Y (O.wirkt routine world args).1 table field ∧
      (∀ k, k < ((declOf output.compiled.unit).count table).toNat →
        Enc output.image.Y ((declOf output.compiled.unit).typ table field) ((O.wirkt routine world args).1.slots table k field)
          (if writable then byteOf current (reqArg req pointer) k else wAt prior (output.image.Y.elem table field k))) ∧
      ∀ future, before.ths.length ≤ future → PrivateBuffers (imageStackFootprint output) before.ms.1 →
        (∀ byte, (reqArg req pointer).toNat ≤ byte.toNat →
          byte.toNat < (reqArg req pointer).toNat + 8 * pufW ((declOf output.compiled.unit).count table).toNat →
          imageStackFootprint output thread byte) →
        GleichAuf (imageStackFootprint output future) before.ms.1.m after.ms.1.m := by
  intro prior current after
  obtain ⟨answeredByHost, sameBuffers⟩ := image_host_answer ordinary answered
  obtain ⟨word, extra, response, readable, writableMap, outside, remaining, cells, outcome⟩ :=
    answers.buffer routine gate selected transport pointer tableNumber writable table field
      parameter identified bytes byteType world args req prior number registers unused represented packed
      answer current answeredByHost
  have noArea : gate.resultArea = none :=
    Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp transport).2).2
  refine ⟨.ask waiting rfl ordinary answered rfl, ?_, readable, writableMap, outside, remaining, cells, ?_⟩
  · refine ⟨site, sourceMemory, routine, worldR world, envR args, atCall, afterCall, alive, key, observed,
      carriers, gate, word, extra, selected, number, ArgsW.withIdle_words args types registers, response, .inl ⟨noArea, ?_⟩⟩
    rw [wirkt_mitRuhe O]
    exact outcome
  · intro future dormant buffers owned
    apply image_gate_dormant_frame waiting dormant buffers sameBuffers
    intro byte reserved
    have distinct : thread ≠ future := fun equal =>
      (Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp waiting).1) (equal.symm ▸ dormant)
    exact ⟨(outside _ (fun hit => distinct (imageStackFootprint_disjoint (owned byte hit.1 hit.2) reserved))).symm,
      congrFun readable.symm byte, congrFun writableMap.symm byte⟩

end Gabbro.Stage0
