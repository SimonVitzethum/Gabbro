module

public import Stage0.Senke.Bild.Mehr.Ort.IRCorrectness
public import Stage0.Senke.Bild.Ruf.ExpressionMemory
public import Stage0.Senke.Bild.Ruf.RootMemory

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.BildLauf
  Runner Runner.IR Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The production function's fixed entry code and the lowered body
    that follows it at a strictly later instruction address. -/
structure FunctionIRPrologue (output : Emitted src reserve options) (memory : Mem)
    (f : (declOf output.compiled.unit).Fn) where
  requirement : List II × Nat
  postcondition : List II × Nat
  capture : List II
  body : List II × Nat
  prefixCode : List II
  requirementLowered : lowE output.image.Y (output.compiled.program.requires f)
    (functionFrame output.compiled.program f).canonicalResult = some requirement
  postconditionLowered : lowPost output.image.Y (functionFrame output.compiled.program f)
    output.compiled.program f (functionFrame output.compiled.program f).internalStatus = some postcondition
  captureLowered : EntrySnapshots.capture output.image.Y (oldCells (output.compiled.program.ensures f))
    (functionFrame output.compiled.program f).snapshotBase = some capture
  bodyLowered : lowEnd (reserved := (functionFrame output.compiled.program f).bodyReserved)
    output.image.passes output.image.A output.image.Y (functionFrame output.compiled.program f)
    postcondition [] (0, 0) (output.compiled.program.rumpf f) = some body
  assembled :
    let frame := functionFrame output.compiled.program f
    prefixCode = guardC 2 105 frame.canonicalResult ++ requirement.1 ++
      guardC frame.canonicalResult 101 frame.canonicalResult ++
      relocateC FB frame.ensReserved frame.parameterWords ++ capture ++
      relocateC frame.ensParams (frame.bodyReserved - frame.ensReserved) frame.parameterWords
  instructions : CodeAt memory (BitVec.ofNat 64 (output.image.A f)) (prefixCode ++ body.1)
  beforeStacks : output.image.A f + 16 * (prefixCode ++ body.1).length ≤ output.image.fp0

def FunctionIRPrologue.entry {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} (_ : FunctionIRPrologue output memory f) (fp : W) : T :=
  ⟨BitVec.ofNat 64 (output.image.A f), fp⟩

def FunctionIRPrologue.bodyEntry {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} (entry : FunctionIRPrologue output memory f) (fp : W) : T :=
  ⟨(entry.entry fp).pc + BitVec.ofNat 64 (16 * entry.prefixCode.length), fp⟩

/-- Derive the two contiguous code regions from the image's real function
    lowering. No separate compilation, validator, or execution is needed. -/
theorem Emitted.function_prologue [Kern] {output : Emitted src reserve options} {memory : Mem}
    (loaded : output.IRFunctionSemantics memory) (f : (declOf output.compiled.unit).Fn) :
    Nonempty (FunctionIRPrologue output memory f) := by
  obtain ⟨code, _, _, functions, _⟩ := loaded
  obtain ⟨_, lowered, _, exactCode, fits⟩ := functions f
  simp only [lowFun, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lowered
  obtain ⟨requirement, requirementLowered, post, postLowered, body, bodyLowered,
    capture, captureLowered, built, _⟩ := lowered
  let frame := functionFrame output.compiled.program f
  let prefixCode := guardC 2 105 frame.canonicalResult ++ requirement.1 ++
    guardC frame.canonicalResult 101 frame.canonicalResult ++
    relocateC FB frame.ensReserved frame.parameterWords ++ capture ++
    relocateC frame.ensParams (frame.bodyReserved - frame.ensReserved) frame.parameterWords
  have equal : prefixCode ++ body.1 = code f := built
  exact ⟨⟨requirement, post, capture, body, prefixCode, requirementLowered,
    postLowered, captureLowered, bodyLowered, rfl, equal.symm ▸ exactCode, equal.symm ▸ fits⟩⟩

/-- The prologue ends at the first instruction of the actual lowered
    body, with the same frame pointer. -/
theorem FunctionIRPrologue.partitions [Kern] {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} (compiled : FunctionIRPrologue output memory f) (fp : W) :
    CodeAt memory (compiled.entry fp).pc compiled.prefixCode ∧
      CodeAt memory (compiled.bodyEntry fp).pc compiled.body.1 :=
  ⟨codeAt_left compiled.instructions, codeAt_right compiled.instructions⟩

private theorem snapshots_agree {D : Deklaration} {L : Lay D} {world : World D}
    {before after : Mem} {fp : W} {K base : Nat} {cells : List (Zelle D)}
    (frame : FrameOK before fp K) (fits : base + EntrySnapshots.words cells ≤ K)
    (same : ∀ byte, inSlots fp 0 K byte → after.b byte = before.b byte ∧ after.rd byte = before.rd byte)
    (saved : EntrySnapshots.At L world before fp cells base) :
    EntrySnapshots.At L world after fp cells base := by
  induction cells generalizing base with
  | nil => trivial
  | cons head tail ih =>
    have bound : base + valueWords head.ty + EntrySnapshots.words tail ≤ K := by
      simpa only [EntrySnapshots.words, Nat.add_assoc] using fits
    exact ⟨frame_value_agrees frame (by omega) same saved.1, ih bound saved.2⟩

/-- Snapshot capture is confined to the generated instructions, the
    declared source cells, and the destination frame. This single
    reference accounts for every prefix of the complete capture. -/
theorem _root_.Gabbro.Stage0.Senke.EntrySnapshots.capture_frameMemory [kernel : Kern]
    {D : Deklaration} {L : Lay D} {world : World D} {memory : Mem} {pc fp : W}
    {K base : Nat} {cells : List (Zelle D)} {code : List II}
    (reads : W → Prop) (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (cellReads : ∀ cell ∈ cells, ∀ byte : W, cell.adr L ≤ byte.toNat →
      byte.toNat < cell.adr L + 8 * valueWords cell.ty → reads byte)
    (emitted : EntrySnapshots.capture L cells base = some code)
    (frame : FrameOK memory fp K) (small : K < 2 ^ 31) (fits : base + EntrySnapshots.words cells ≤ K)
    (separated : ∀ cell ∈ cells, fp.toNat + 8 * K ≤ cell.adr L)
    (installed : CodeAt memory pc code) (far : CodeFar pc code.length fp K)
    (inputs : EntrySnapshots.Inputs L world memory cells) :
    let start : T := ⟨pc, fp⟩
    let target : T := ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩
    let restricted := maskMemory reads (inSlots fp 0 K) memory
    ∃ count finish, @IRReference kernel.withoutSyscalls count start restricted target finish ∧
      ∀ {taken : Nat} {pointer : T} {actual : Mem},
        StarM taken start memory pointer actual → taken ≤ count →
        (taken = count → pointer = target ∧ Agree fp base (base + EntrySnapshots.words cells) memory actual ∧
          EntrySnapshots.At L world actual fp cells base) ∧
        (taken < count → ∀ {control : Res T} {atControl : Mem},
          RunP (step pointer) actual control atControl → HostFreeControl reads (inSlots fp 0 K) control) := by
  intro start target restricted
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨proofFrame, proofCode⟩ := maskMemory_code_frame installed frame far.1 frameReads codeReads
  have inputCells : EntrySnapshots.Inputs L world restricted cells := by
    intro cell member
    have span := (EntrySnapshots.capture_bounds cells base emitted cell member).2
    exact expression_mask_value frameReads (span.trans (by decide)) (cellReads cell member) (inputs cell member)
  obtain ⟨finish, executed, written, stored⟩ :=
    EntrySnapshots.capture_ok cells base emitted restricted pc proofFrame small fits separated proofCode far inputCells
  obtain ⟨count, reference⟩ := IRReference.of_star executed
  obtain ⟨agreement, readable, writable⟩ := maskMemory_agreement reads (inSlots fp 0 K) memory frameReads
  refine ⟨count, finish, reference, ?_⟩
  intro taken pointer actual run within
  obtain ⟨complete, pending⟩ := IRReference.scoped_prefix (kernel := kernel) reference agreement readable writable run within
  refine ⟨?_, pending⟩
  intro atEnd
  obtain ⟨rfl, relevant, untouched⟩ := complete atEnd
  obtain ⟨readMap, writeMap⟩ := StarM.permissions run
  have same (byte : W) (inside : inSlots fp 0 K byte) :
      actual.b byte = finish.b byte ∧ actual.rd byte = finish.rd byte :=
    ⟨(relevant.1 byte (frameReads byte inside)).1.symm, (relevant.1 byte (frameReads byte inside)).2.symm⟩
  refine ⟨rfl, ⟨readMap, writeMap, ?_⟩,
    snapshots_agree (proofFrame.agree (Senke.Agree.widen written fits)) fits same stored⟩
  intro byte outside
  by_cases inside : inSlots fp 0 K byte
  · exact (same byte inside).1.trans ((written.b byte outside).trans (agreement.1 byte (frameReads byte inside)).1)
  · exact (untouched byte inside).1

/-- A private request advances the same IR continuation in the reference
    and the scheduled image. For a native scalar answer the proof needs
    uniqueness of that operation's word, as holds for comparisons. -/
private theorem image_private_continuation [kernel : Kern] {before after : imageTSO.St} {thread : Nat}
    {reads writes : W → Prop} {localMemory finish : Mem} {target : T}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    (reference : @Run kernel.withoutSyscalls (.ask request resume) localMemory target finish)
    (blind : Blind (.ask request resume))
    (scope : HostFreeControl reads writes (.ask request resume))
    (agreement : GleichAuf reads (before.1.view thread) localMemory)
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (replied : imageTSO.ans before thread request answer after) :
    ∃ updated, @Run kernel.withoutSyscalls (resume answer) updated target finish ∧
      GleichAuf reads (after.1.view thread) updated := by
  cases reference with
  | ask expected rest =>
    have memory : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases expected
    obtain ⟨updated, _, exactAnswer, continued, same⟩ :=
      tso_memory_response_matches blind agreement scope.2.1 memory replied.1
    rw [expected] at exactAnswer
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj exactAnswer)
    exact ⟨_, continued.symm ▸ rest, same⟩
  | sys impossible _ => exact False.elim impossible
  | fp expected rest =>
    obtain ⟨rfl, word, rfl, observed⟩ := replied.1
    have same := nativeUnique _ _ _ _ _ rfl expected observed
    cases same
    exact ⟨localMemory, rest, agreement⟩

/-- The remaining instructions of an established IR region. Its current
    instruction may be between requests, and the last full instruction
    ends at the same fixed boundary in every case. -/
def IRContinuation [kernel : Kern] (target : T) (finish : Mem) (control : Res T) (memory : Mem) : Prop :=
  match control with
  | .next pointer => ∃ count, @IRReference kernel.withoutSyscalls count pointer memory target finish
  | .ask .. => ∃ next middle count,
      @Run kernel.withoutSyscalls control memory next middle ∧
      @IRReference kernel.withoutSyscalls count next middle target finish
  | .fault | .unk => False

private theorem IRContinuation.ofRun [kernel : Kern] {target next : T} {memory middle finish : Mem}
    {control : Res T} {count : Nat} (step : @Run kernel.withoutSyscalls control memory next middle)
    (remaining : @IRReference kernel.withoutSyscalls count next middle target finish) :
    IRContinuation target finish control memory := by
  cases control with
  | next pointer =>
    cases step
    exact ⟨count, remaining⟩
  | ask request resume => exact ⟨next, middle, count, step, remaining⟩
  | fault | unk => cases step

theorem IRContinuation.noHost [Kern] {target : T} {memory finish : Mem} {request : Req} {resume : Ans → Res T}
    (pending : IRContinuation target finish (.ask (.sys request) resume) memory) : False := by
  obtain ⟨_, _, _, instruction, _⟩ := pending
  cases instruction with
  | ask impossible _ => cases impossible
  | sys impossible _ => exact impossible

/-- A restricted continuation certifies its next request from the Lean IR
    semantics and the permissions of its reference memory. -/
theorem IRContinuation.request_scope [Kern] {target : T} {memory finish : Mem}
    {request : Op} {resume : Ans → Res T} {reads writes : W → Prop}
    (continuation : IRContinuation target finish (.ask request resume) memory)
    (blind : Blind (.ask request resume))
    (readable : ∀ byte, memory.rd byte = true → reads byte)
    (writable : ∀ byte, memory.wr byte = true → reads byte ∧ writes byte) :
    HostFreeControl reads writes (.ask request resume) := by
  have noHost (call : Req) (same : request = .sys call) : False := by
    subst request
    exact IRContinuation.noHost continuation
  obtain ⟨_, _, _, instruction, _⟩ := continuation
  cases instruction with
  | ask answered rest =>
    rename_i answer
    cases answer with
    | none =>
      rw [blind.missing] at rest
      cases rest
    | some words =>
      obtain ⟨readScope, writeScope⟩ := memAns_confined readable writable answered
      exact ⟨noHost, readScope, writeScope⟩
  | sys impossible _ => exact False.elim impossible
  | fp =>
    exact ⟨fun _ impossible => by cases impossible,
      fun _ touched => by cases touched, fun writesMemory => by cases writesMemory⟩

/-- Decoding the next instruction either opens the remaining reference
    or identifies the exact boundary where the region has finished. -/
theorem IRContinuation.decode [Kern] {target pointer : T} {memory finish : Mem}
    (continuation : IRContinuation target finish (.next pointer) memory) :
    (pointer = target ∧ memory = finish) ∨ IRContinuation target finish (IR.step pointer) memory := by
  obtain ⟨_, code⟩ := continuation
  cases code with
  | start => exact .inl ⟨rfl, rfl⟩
  | extend current remaining => exact .inr (.ofRun current remaining)

/-- A scheduled private response retains the original boundary and advances
    exactly the instruction fragment that the Lean IR was waiting on. -/
theorem IRContinuation.answer [Kern] {before after : imageTSO.St} {thread : Nat}
    {reads writes : W → Prop} {reference finish : Mem} {target : T}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    (continuation : IRContinuation target finish (.ask request resume) reference)
    (blind : Blind (.ask request resume)) (scope : HostFreeControl reads writes (.ask request resume))
    (agreement : GleichAuf reads (before.1.view thread) reference)
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (replied : imageTSO.ans before thread request answer after) :
    ∃ updated, IRContinuation target finish (resume answer) updated ∧
      GleichAuf reads (after.1.view thread) updated := by
  obtain ⟨_, _, _, current, rest⟩ := continuation
  obtain ⟨updated, continued, kept⟩ :=
    image_private_continuation current blind scope agreement nativeUnique replied
  exact ⟨updated, .ofRun continued rest, kept⟩

/-- Adjacent regions preserve the unfinished part of the current
    instruction while extending its eventual destination. -/
theorem IRContinuation.append [kernel : Kern] {control : Res T} {memory middle finish : Mem}
    {target next : T} {count : Nat}
    (first : IRContinuation target middle control memory)
    (suffix : @IRReference kernel.withoutSyscalls count target middle next finish) :
    IRContinuation next finish control memory := by
  letI : Kern := kernel.withoutSyscalls
  cases control with
  | next pointer =>
    obtain ⟨_, initial⟩ := first
    exact ⟨_, initial.append suffix⟩
  | ask request resume =>
    obtain ⟨pointer, after, _, instruction, initial⟩ := first
    exact ⟨pointer, after, _, instruction, initial.append suffix⟩
  | fault | unk => exact False.elim first

def imagePrologueFrame (output : Emitted src reserve options) (thread : Nat) : W :=
  slot (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread))) (BitVec.ofNat 64 FB)

/-- A root is already in its lowered function and its first body
    instruction is still the destination of the active IR reference.
    The same phase covers pending memory and native comparison requests. -/
structure ImageProloguePhase [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (thread : Nat) (control : Res T) (memory : Mem)
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) where
  root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)
  declared : E.starts[thread]? = some root
  alive : state.lebt thread = true
  unentered : state.m.faeden thread = (imageSourceStart E).m.faeden thread
  reads : W → Prop
  reference : Mem
  finish : Mem
  lowered : FunctionIRPrologue output finish root.1
  running : IRContinuation (lowered.bodyEntry (imagePrologueFrame output thread)) finish control reference
  blind : Blind control
  agrees : GleichAuf reads memory reference

/-- A scheduler change outside the retained reference's read scope
    preserves the active function prologue and its exact destination. -/
def ImageProloguePhase.transport [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {control : Res T}
    {memory nextMemory : Mem} {state nextState : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread control memory state)
    (sameBytes : GleichAuf phase.reads nextMemory memory)
    (alive : nextState.lebt thread = true) (sameHead : nextState.m.faeden thread = state.m.faeden thread) :
    ImageProloguePhase output E thread control nextMemory nextState :=
  ⟨phase.root, phase.declared, alive, sameHead.trans phase.unentered, phase.reads,
    phase.reference, phase.finish, phase.lowered, phase.running, phase.blind,
    fun byte inside => (sameBytes byte inside).trans (phase.agrees byte inside)⟩

/-- Decoding either advances a prologue or identifies the precise memory
    and pointer at which the source body can be admitted. -/
theorem ImageProloguePhase.decode [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {pointer : T}
    {memory : Mem} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread (.next pointer) memory state) :
    let frame := imagePrologueFrame output thread
    (pointer = phase.lowered.bodyEntry frame ∧ GleichAuf phase.reads memory phase.finish) ∨
      Nonempty (ImageProloguePhase output E thread (IR.step pointer) memory state) := by
  intro frame
  rcases IRContinuation.decode phase.running with ⟨boundary, reference⟩ | progress
  · exact .inl ⟨boundary, reference ▸ phase.agrees⟩
  · exact .inr ⟨⟨phase.root, phase.declared, phase.alive, phase.unentered,
      phase.reads, phase.reference, phase.finish, phase.lowered, progress, blind_step pointer, phase.agrees⟩⟩

/-- An actual memory or native response leaves the root headed to the
    same lowered entry and retains agreement on the active read scope. -/
theorem ImageProloguePhase.answer [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {before after : imageTSO.St}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread (.ask request resume) (before.1.view thread) state)
    (scope : HostFreeControl phase.reads (imageStackFootprint output thread) (.ask request resume))
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (response : imageTSO.ans before thread request answer after) :
    Nonempty (ImageProloguePhase output E thread (resume answer) (after.1.view thread) state) := by
  obtain ⟨updated, progress, kept⟩ :=
    IRContinuation.answer phase.running phase.blind scope phase.agrees nativeUnique response
  exact ⟨⟨phase.root, phase.declared, phase.alive, phase.unentered, phase.reads,
    updated, phase.finish, phase.lowered, progress, phase.blind.weiter answer, kept⟩⟩

/-- Before body admission a root can still be in its startup stub or
    already running the actual lowered function prologue. -/
def ImagePendingRoot [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (history : List Ev)
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) (memory : Mem) (thread : Nat)
    (control : Res T) : Prop :=
  ImageRootPhase output E history memory thread control state ∨
    Nonempty (ImageProloguePhase output E thread control memory state)

/-- A thread can decode its next prologue instruction while other body
    and root slots retain their existing relations to the source machine. -/
theorem ImageRuntimePartition.prologue_decode [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {before : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {thread : Nat} {pointer : T}
    (partition : ImageRuntimePartition footprint output E O history before state body
      (ImagePendingRoot output E history state))
    (pending : body[thread]? = some none) (running : before.ths[thread]? = some (some (.next pointer)))
    (phase : ImageProloguePhase output E thread (.next pointer) (before.ms.1.view thread) state) :
    let boundary := phase.lowered.bodyEntry (imagePrologueFrame output thread)
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set thread (some (IR.step pointer))⟩
    (pointer = boundary ∧ GleichAuf phase.reads (before.ms.1.view thread) phase.finish) ∨
      (ProcessStep imageTSO Runner.Beweis.actI before [] after ∧
        ImageRuntimePartition footprint output E O history after state body
          (ImagePendingRoot output E history state)) := by
  intro boundary after
  rcases phase.decode with atBody | progress
  · exact .inl atBody
  · refine .inr ⟨.priv running rfl, ?_⟩
    exact partition.advance_pending pending rfl (.inr progress) (fun _ _ => rfl)
      partition.1 id (fun related _ => ⟨_, related⟩)

/-- A read or native comparison advances the real prologue without
    moving any other thread or changing its memory view. -/
theorem ImageRuntimePartition.prologue_read_answer [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {before : Cfg imageTSO (Res T)} {memory : imageTSO.St}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {thread : Nat}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    (partition : ImageRuntimePartition footprint output E O history before state body
      (ImagePendingRoot output E history state))
    (pending : body[thread]? = some none)
    (running : before.ths[thread]? = some (some (.ask request resume)))
    (phase : ImageProloguePhase output E thread (.ask request resume) (before.ms.1.view thread) state)
    (scope : HostFreeControl phase.reads (imageStackFootprint output thread) (.ask request resume))
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (readOnly : schreibtOp request = false) (response : imageTSO.ans before.ms thread request answer memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set thread (some (resume answer))⟩
    ProcessStep imageTSO Runner.Beweis.actI before [] after ∧
      ImageRuntimePartition footprint output E O history after state body (ImagePendingRoot output E history state) := by
  have unchanged : memory = before.ms ∧ request.special = false ∧ lbl thread request answer = [] := by
    cases request with
    | rd | fp => exact ⟨response.1.1, rfl, rfl⟩
    | wr | cas => cases readOnly
    | sys => exact (IRContinuation.noHost phase.running).elim
  obtain ⟨rfl, ordinary, silent⟩ := unchanged
  intro after
  have progress := phase.answer scope nativeUnique response
  refine ⟨?_, partition.advance_pending pending rfl (.inr progress) (fun _ _ => rfl)
    partition.1 id (fun related _ => ⟨_, related⟩)⟩
  exact silent ▸ ProcessStep.ask running rfl ordinary response rfl

end Gabbro.Stage0
