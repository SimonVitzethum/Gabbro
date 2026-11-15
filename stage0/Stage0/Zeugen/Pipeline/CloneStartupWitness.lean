module
public import Stage0.IRBild
public import Stage0.SourceWitness
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section
/-! # Witness for plan A5: the startup's thread creation of an emitted image with two spawned roots

The actual accepted image below declares two roots (the same function with different arguments), so its startup
spawns two threads. The loaded payload is the one the builder emitted. Two different kernels meet the one named
environment assumption `Senke.CloneAnswers`, and each reading of the startup is inhabited:
* a kernel that answers every `clone` with a thread id: `main`'s thread runs through both spawn sites (`spawned_zeuge`);
* a kernel that refuses every `clone` with an error number: `main`'s thread stops with the declared `Senke.cloneCode`
  (`refused_zeuge`).
-/

namespace Gabbro.Stage0.Pipeline.CloneStartupWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def text : String :=
  "module startup { impl fn worker(i : u32 in 0 .. 9, b : bool) effects { pure } { } impl fn main() -> u32 in 0 .. 9 effects { pure } { return 3; } concurrent { worker(7, true), worker(2, false) }; }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output := Gabbro.Grammatik.except_ok_get candidate_present

/-- Two spawned roots: the spawn sites of the startup are not an empty list. -/
theorem two_roots : output.starts.length = 2 := by decide +kernel

attribute [irreducible] output

theorem roots_present : output.starts ≠ [] := by
  intro h
  have := two_roots
  rw [h] at this
  exact absurd this (by decide)

variable [RootNativeFloat.Hardware]

/-- The loaded payload of the emitted image: the single initial memory every statement below starts from. -/
theorem loaded : Senke.BytesAt (SourceWitness.loadedMemory output.bytes) Runner.Prog.IMG output.bytes :=
  SourceWitness.loadedBytes _ (ImagePhases.geometry output).2

section Creating

/-- A kernel that answers every thread creation with the thread id 1 and leaves the memory alone. -/
local instance creating : Runner.IR.Kern where
  toHardware := inferInstance
  ans q m a m' := q = Runner.cloneReq → a = some (1, 0) ∧ m' = m

local instance : Senke.CloneAnswers where
  ans _ := ⟨1, 0, by decide, fun _ => ⟨rfl, rfl⟩⟩

/-- Under the creating kernel `main`'s thread runs through both spawn sites of the startup of the actual image. -/
theorem spawned_zeuge :
    ∃ m1, Runner.IR.Star ⟨BitVec.ofNat 64 Senke.codeBase, BitVec.ofNat 64 output.image.fp0⟩
      (SourceWitness.loadedMemory output.bytes)
      ⟨BitVec.ofNat 64 (Senke.codeBase + 16 * (10 * output.starts.length)), BitVec.ofNat 64 output.image.fp0⟩ m1 ∧
      Runner.IR.Agree (BitVec.ofNat 64 output.image.fp0) (Senke.startScratch output.compiled.main)
        output.image.Ks (SourceWitness.loadedMemory output.bytes) m1 :=
  output.spawned loaded (fun m' r x _ h => by
    have e := (h rfl).1
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    rw [e.1]
    decide)

end Creating

section Refusing

/-- A kernel that refuses every thread creation with the error number -1 and leaves the memory alone. -/
local instance refusing : Runner.IR.Kern where
  toHardware := inferInstance
  ans q m a m' := q = Runner.cloneReq → a = some (-1, 0) ∧ m' = m

local instance : Senke.CloneAnswers where
  ans _ := ⟨-1, 0, by decide, fun _ => ⟨rfl, rfl⟩⟩

/-- Under the refusing kernel the startup of the actual image stops with the declared exit code of a refused
    thread creation; no root thread was created. -/
theorem refused_zeuge :
    Senke.Stops ⟨BitVec.ofNat 64 Senke.codeBase, BitVec.ofNat 64 output.image.fp0⟩
      (SourceWitness.loadedMemory output.bytes) Senke.cloneCode :=
  output.refused loaded roots_present (fun m' r x _ h => by
    have e := (h rfl).1
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    rw [e.1]
    decide)

end Refusing

end Gabbro.Stage0.Pipeline.CloneStartupWitness
