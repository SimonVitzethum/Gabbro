module

public import Stage0.Senke.Bild.Mehr.Ort.IRCorrectness
public import Stage0.Senke.Bild.Ruf.ExpressionMemory

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.BildLauf
  Runner Runner.IR

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
    snapshots_agree (proofFrame.agree (written.widen fits)) fits same stored⟩
  intro byte outside
  by_cases inside : inSlots fp 0 K byte
  · exact (same byte inside).1.trans ((written.b byte outside).trans (agreement.1 byte (frameReads byte inside)).1)
  · exact (untouched byte inside).1

end Gabbro.Stage0
