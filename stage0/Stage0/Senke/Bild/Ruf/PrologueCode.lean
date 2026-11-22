module

public import Stage0.Senke.Bild.Ruf.PrologueContinuation
public import Stage0.Senke.Rueckkehr.Entry
public import Stage0.Senke.Bild.Ruf.ExpressionMemory
public import Stage0.Senke.Bild.Ruf.RootMemory
public import Stage0.Senke.Bild.Ruf.PrologueAccess

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

/-- The actual lowered function has one contiguous prologue followed by
    its body. This decomposition preserves the original instruction table. -/
theorem FunctionIRPrologue.of_lowered [Kern] {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} {code : List II} {top : Nat}
    (lowered : lowFun output.image.passes output.compiled.program output.image.A output.image.Y f = some (code, top))
    (exactCode : CodeAt memory (BitVec.ofNat 64 (output.image.A f)) code)
    (fits : output.image.A f + 16 * code.length ≤ output.image.fp0) :
    ∃ prologue : FunctionIRPrologue output memory f,
      code = prologue.prefixCode ++ prologue.body.1 ∧
        frei ((declOf output.compiled.unit).params f) (functionFrame output.compiled.program f).bodyReserved ≤ top := by
  simp only [lowFun, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lowered
  obtain ⟨requirement, requirementLowered, post, postLowered, body, bodyLowered,
    capture, captureLowered, built, frameTop⟩ := lowered
  let frame := functionFrame output.compiled.program f
  let prefixCode := guardC 2 105 frame.canonicalResult ++ requirement.1 ++
    guardC frame.canonicalResult 101 frame.canonicalResult ++
    relocateC FB frame.ensReserved frame.parameterWords ++ capture ++
    relocateC frame.ensParams (frame.bodyReserved - frame.ensReserved) frame.parameterWords
  have equal : prefixCode ++ body.1 = code := built
  have room : frei ((declOf output.compiled.unit).params f) frame.bodyReserved ≤ top := by
    have storage : frei ((declOf output.compiled.unit).params f) frame.bodyReserved =
        frame.bodyParams + frame.parameterWords := rfl
    change max (retTop frame) (max requirement.2 (max (frame.bodyParams + frame.parameterWords) body.2)) = top
      at frameTop
    rw [storage]
    omega
  exact ⟨⟨requirement, post, capture, body, prefixCode, requirementLowered,
    postLowered, captureLowered, bodyLowered, rfl, equal.symm ▸ exactCode, equal.symm ▸ fits⟩,
    equal.symm, room⟩

theorem Emitted.function_prologue [Kern] {output : Emitted src reserve options} {memory : Mem}
    (loaded : output.IRFunctionSemantics memory) (f : (declOf output.compiled.unit).Fn) :
    Nonempty (FunctionIRPrologue output memory f) := by
  obtain ⟨code, _, _, functions, _⟩ := loaded
  obtain ⟨_, lowered, _, exactCode, fits⟩ := functions f
  obtain ⟨prologue, _, _⟩ := FunctionIRPrologue.of_lowered lowered exactCode fits
  exact ⟨prologue⟩

/-- The prologue ends at the first instruction of the actual lowered
    body, with the same frame pointer. -/
theorem FunctionIRPrologue.partitions [Kern] {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} (compiled : FunctionIRPrologue output memory f) (fp : W) :
    CodeAt memory (compiled.entry fp).pc compiled.prefixCode ∧
      CodeAt memory (compiled.bodyEntry fp).pc compiled.body.1 :=
  ⟨codeAt_left compiled.instructions, codeAt_right compiled.instructions⟩

theorem _root_.Gabbro.Stage0.Senke.EntrySnapshots.At.congr_read_frame
    {D : Deklaration} {L : Lay D} {world : World D}
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

/-- Restored arguments and old values depend only on their complete frame spans. -/
theorem _root_.Gabbro.Stage0.Senke.EntryFrameValues.congr_read_frame
    {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
    {before after : Mem} {fp : W} {K : Nat} {entry : World D} {args : Env D (D.params f)}
    (stored : EntryFrameValues L P f before fp entry args) (frame : FrameOK before fp K)
    (fits : frei (D.params f) (functionFrame P f).bodyReserved ≤ K)
    (same : ∀ byte, inSlots fp 0 K byte → after.b byte = before.b byte ∧ after.rd byte = before.rd byte) :
    EntryFrameValues L P f after fp entry args := by
  let layout := functionFrame P f
  have reserves : layout.ensReserved ≤ layout.bodyReserved := by
    simp only [FrameLayout.ensReserved, FrameLayout.bodyReserved]
    omega
  have move (reserved : Nat) (bound : reserved ≤ layout.bodyReserved)
      (env : EnvAt L before fp args reserved) : EnvAt L after fp args reserved := by
    intro ty x
    refine frame_value_agrees frame ?_ same (env ty x)
    have extent := variableOffset_bound x
    change frei (D.params f) layout.bodyReserved ≤ K at fits
    unfold frei vslot at *
    omega
  have snapshotEnd : FB + EntrySnapshots.words (oldCells (P.ensures f)) = layout.ensParams := rfl
  have snapshotFits : FB + EntrySnapshots.words (oldCells (P.ensures f)) ≤ K := by
    rw [snapshotEnd]
    have start : layout.ensParams = FB + layout.ensReserved := rfl
    change frei (D.params f) layout.bodyReserved ≤ K at fits
    unfold frei at fits
    omega
  exact ⟨move layout.ensReserved reserves stored.original,
    move layout.bodyReserved (Nat.le_refl _) stored.lexical,
    stored.snapshots.congr_read_frame frame snapshotFits same⟩

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
    stored.congr_read_frame (proofFrame.agree (Senke.Agree.widen written fits)) fits same⟩
  intro byte outside
  by_cases inside : inSlots fp 0 K byte
  · exact (same byte inside).1.trans ((written.b byte outside).trans (agreement.1 byte (frameReads byte inside)).1)
  · exact (untouched byte inside).1

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
  writes : W → Prop
  privateWrites : ∀ byte, writes byte → imageStackFootprint output thread byte
  reference : Mem
  finish : Mem
  lowered : FunctionIRPrologue output finish root.1
  entryWorld : World (declOf output.compiled.unit)
  entryValues : EntryFrameValues output.image.Y output.compiled.program root.1 finish
    (imagePrologueFrame output thread) entryWorld root.2
  entryFrame : FrameOK finish (imagePrologueFrame output thread) (output.image.Ks - FB)
  entryFits : frei ((declOf output.compiled.unit).params root.1)
    (functionFrame output.compiled.program root.1).bodyReserved ≤ output.image.Ks - FB
  running : IRContinuation (lowered.bodyEntry (imagePrologueFrame output thread)) finish control reference
  blind : Blind control
  readable : ∀ byte, reference.rd byte = true → imagePrologueReads output thread root.1 byte
  writable : ∀ byte, reference.wr byte = true → imagePrologueReads output thread root.1 byte ∧ writes byte
  agrees : MaskedAgreement (imagePrologueReads output thread root.1) writes reference memory

abbrev ImageProloguePhase.reads [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {control : Res T} {memory : Mem}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread control memory state) : W → Prop :=
  imagePrologueReads output thread phase.root.1

/-- The actual issuing view has the restored arguments and snapshots
    at the decoded prologue boundary. -/
theorem ImageProloguePhase.entry_values [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {control : Res T}
    {memory : Mem} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread control memory state)
    (frameReads : ∀ byte, inSlots (imagePrologueFrame output thread) 0 (output.image.Ks - FB) byte →
      phase.reads byte)
    (reached : MaskedAgreement phase.reads phase.writes phase.finish memory) :
    EntryFrameValues output.image.Y output.compiled.program phase.root.1 memory
      (imagePrologueFrame output thread) phase.entryWorld phase.root.2 :=
  phase.entryValues.congr_read_frame phase.entryFrame phase.entryFits fun byte inside =>
    let same := reached.1 byte (frameReads byte inside)
    ⟨same.1.symm, same.2.symm⟩

/-- A scheduler change outside the retained reference's read scope
    preserves the active function prologue and its exact destination. -/
def ImageProloguePhase.transport [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {control : Res T}
    {memory nextMemory : Mem} {state nextState : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread control memory state)
    (sameReads : ∀ byte, phase.reads byte →
      nextMemory.b byte = memory.b byte ∧ nextMemory.rd byte = memory.rd byte)
    (sameWrites : ∀ byte, phase.writes byte → nextMemory.wr byte = memory.wr byte)
    (alive : nextState.lebt thread = true) (sameHead : nextState.m.faeden thread = state.m.faeden thread) :
    ImageProloguePhase output E thread control nextMemory nextState :=
  ⟨phase.root, phase.declared, alive, sameHead.trans phase.unentered,
    phase.writes, phase.privateWrites, phase.reference, phase.finish, phase.lowered,
    phase.entryWorld, phase.entryValues, phase.entryFrame, phase.entryFits, phase.running, phase.blind,
    phase.readable, phase.writable, ⟨fun byte inside =>
      ⟨(phase.agrees.1 byte inside).1.trans (sameReads byte inside).1.symm,
        (phase.agrees.1 byte inside).2.trans (sameReads byte inside).2.symm⟩,
      fun byte inside => (phase.agrees.2 byte inside).trans (sameWrites byte inside).symm⟩⟩

/-- Decoding either advances a prologue or identifies the precise memory
    and pointer at which the source body can be admitted. -/
theorem ImageProloguePhase.decode [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {pointer : T}
    {memory : Mem} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread (.next pointer) memory state) :
    let frame := imagePrologueFrame output thread
    (pointer = phase.lowered.bodyEntry frame ∧ MaskedAgreement phase.reads phase.writes phase.finish memory) ∨
      Nonempty (ImageProloguePhase output E thread (IR.step pointer) memory state) := by
  intro frame
  rcases IRContinuation.decode phase.running with ⟨boundary, reference⟩ | progress
  · exact .inl ⟨boundary, reference ▸ phase.agrees⟩
  · exact .inr ⟨⟨phase.root, phase.declared, phase.alive, phase.unentered,
      phase.writes, phase.privateWrites, phase.reference, phase.finish, phase.lowered,
      phase.entryWorld, phase.entryValues, phase.entryFrame, phase.entryFits, progress,
      blind_step pointer, phase.readable, phase.writable, phase.agrees⟩⟩

theorem ImageProloguePhase.request_scope [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {request : Op} {resume : Ans → Res T}
    {memory : Mem} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread (.ask request resume) memory state) :
    HostFreeControl phase.reads (imageStackFootprint output thread) (.ask request resume) := by
  obtain ⟨noHost, reads, writes⟩ := phase.running.request_scope phase.blind phase.readable phase.writable
  exact ⟨noHost, reads, fun stores byte touched => phase.privateWrites byte (writes stores byte touched)⟩

/-- An actual memory or native response leaves the root headed to the
    same lowered entry and retains agreement on the active read scope. -/
theorem ImageProloguePhase.answer [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread : Nat} {before after : imageTSO.St}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (phase : ImageProloguePhase output E thread (.ask request resume) (before.1.view thread) state)
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (response : imageTSO.ans before thread request answer after) :
    Nonempty (ImageProloguePhase output E thread (resume answer) (after.1.view thread) state) := by
  obtain ⟨updated, progress, kept, readMap, writeMap⟩ :=
    IRContinuation.answer phase.running phase.blind phase.readable phase.writable phase.agrees nativeUnique response
  exact ⟨⟨phase.root, phase.declared, phase.alive, phase.unentered,
    phase.writes, phase.privateWrites, updated, phase.finish, phase.lowered,
    phase.entryWorld, phase.entryValues, phase.entryFrame, phase.entryFits, progress, phase.blind.weiter answer,
    fun byte permit => phase.readable byte (by simpa only [readMap] using permit),
    fun byte permit => phase.writable byte (by simpa only [writeMap] using permit), kept⟩⟩

/-- Before body admission a root can still be in its startup stub or
    already running the actual lowered function prologue. -/
def ImagePendingRoot [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (history : List Ev)
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) (memory : Mem) (thread : Nat)
    (control : Res T) : Prop :=
  ImageRootPhase output E history memory thread control state ∨
    Nonempty (ImageProloguePhase output E thread control memory state)

/-- A partition whose pending threads are all in startup stubs is ready
    for the runtime relation that also admits installed prologues. -/
theorem ImageRuntimePartition.with_prologues [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {machine : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    (partition : ImageRuntimePartition footprint output E O history machine state body) :
    ImageRuntimePartition footprint output E O history machine state body (ImagePendingRoot output E history state) := by
  obtain ⟨buffers, length, bodies, roots⟩ := partition
  refine ⟨buffers, length, bodies, ?_⟩
  intro thread
  rcases roots thread with exactSlot | ⟨control, pending, live, root⟩
  · exact .inl exactSlot
  · exact .inr ⟨control, pending, live, .inl root⟩

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
    (pointer = boundary ∧ MaskedAgreement phase.reads phase.writes phase.finish (before.ms.1.view thread)) ∨
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
  have progress := phase.answer nativeUnique response
  refine ⟨?_, partition.advance_pending pending rfl (.inr progress) (fun _ _ => rfl)
    partition.1 id (fun related _ => ⟨_, related⟩)⟩
  exact silent ▸ ProcessStep.ask running rfl ordinary response rfl

/-- The actual prologue's frame store advances its reference without
    changing the source state or any other live stack. -/
theorem ImageRuntimePartition.prologue_store [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {before : Cfg imageTSO (Res T)} {memory : imageTSO.St}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))} {thread : Nat}
    {address word : W} {resume : Ans → Res T} {answer : Ans}
    (partition : ImageRuntimePartition footprint output E O history before state body
      (ImagePendingRoot output E history state))
    (placed : ∀ owner byte, footprint owner byte → imageStackFootprint output owner byte ∨
      output.image.Y.lo ≤ byte.toNat ∧ byte.toNat < output.image.Y.hi)
    (owns : ∀ byte, imageStackFootprint output thread byte → footprint thread byte)
    (pending : body[thread]? = some none)
    (running : before.ths[thread]? = some (some (.ask (.wr address word) resume)))
    (phase : ImageProloguePhase output E thread (.ask (.wr address word) resume) (before.ms.1.view thread) state)
    (answered : imageTSO.ans before.ms thread (.wr address word) answer memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set thread (some (resume answer))⟩
    ProcessStep imageTSO Runner.Beweis.actI before [] after ∧
      ImageRuntimePartition footprint output E O history after state body (ImagePendingRoot output E history state) := by
  obtain ⟨continued⟩ := phase.answer (fun _ _ _ _ _ incompatible => by cases incompatible) answered
  have success : answer = some (0, 0) := by
    rcases answered.1 with ⟨_, denied, _⟩ | ⟨_, accepted, _⟩
    · exact (continued.running.not_fault ((congrArg resume denied).trans phase.blind.missing)).elim
    · exact accepted
  subst answer
  exact partition.pending_store placed owns pending (phase.request_scope.2.2 rfl) running answered (.inr ⟨continued⟩)

end Gabbro.Stage0
