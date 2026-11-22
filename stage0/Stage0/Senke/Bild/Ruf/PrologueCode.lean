module

public import Stage0.Senke.Bild.Mehr.Ort.IRCorrectness

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Runner Runner.IR

variable {src : String} {reserve : Nat} {options : Profil.Options} [Kern]

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
theorem Emitted.function_prologue {output : Emitted src reserve options} {memory : Mem}
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
theorem FunctionIRPrologue.partitions {output : Emitted src reserve options} {memory : Mem}
    {f : (declOf output.compiled.unit).Fn} (compiled : FunctionIRPrologue output memory f) (fp : W) :
    CodeAt memory (compiled.entry fp).pc compiled.prefixCode ∧
      CodeAt memory (compiled.bodyEntry fp).pc compiled.body.1 :=
  ⟨codeAt_left compiled.instructions, codeAt_right compiled.instructions⟩

end Gabbro.Stage0
