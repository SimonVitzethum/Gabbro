module
public import Stage0.IRBild
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


namespace Gabbro.Stage0.Pipeline.OptionalForeignBinderWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Real source bindings for nonfallible void, fallible value and fallible void.
    The void binder deliberately reuses a live name: it must not shadow saved.
    The value continuation uses first, and each handler returns a distinct value. -/
def text : String :=
  "module optional_binders { reason R { Denied = 9 \"denied\" exhaustive } assume boundary \"foreign fixture contracts\" falsifier boundary_probe; syscall ping() abi linux arch x86_64 number 39 regs in { } regs out { rax } clobbers { rcx, r11 } errors { } effects { pure } costs <= 8 ops assume boundary falsifier boundary_probe; syscall value(fd : u64) -> u8 in 0 .. 10 or R abi linux arch x86_64 number 3 regs in { rdi = fd } regs out { rax } clobbers { rcx, r11 } errors { EBADF => Denied } effects { pure } costs <= 8 ops assume boundary falsifier boundary_probe; syscall action(fd : u64) or R abi linux arch x86_64 number 3 regs in { rdi = fd } regs out { rax } clobbers { rcx, r11 } errors { EBADF => Denied } effects { pure } costs <= 8 ops assume boundary falsifier boundary_probe; impl fn main() -> u8 { let saved = 23; let saved? = ping(); let first? = value(1) else (e) { match e { Denied => { return 9; } } return 0; } if true { let saved? = action(99) else (e) { match e { Denied => { return 11; } } return 0; } return saved; } return first; } }"

/-- This is the production source-to-image entry, with all three explicit gates. -/
def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- The exporter retains both payload shapes and optional constructors in the
    exact canonical unit passed into image generation. -/
theorem image_shape :
    output.compiled.unit.axs.map (·.name) = ["ping", "value", "action"] ∧
    output.compiled.unit.axs.map (·.res) = [none, some (.int 0 10), none] ∧
    output.compiled.unit.axs.map (·.gruende) = [0, 1, 1] ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bindOptBeg .. => true | _ => false) = 1 ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bindOptElseBeg .. => true | _ => false) = 2 ∧
    0 < output.image.code.length ∧ 16 < output.image.bytes.length := by decide +kernel

/-- The void gates are real selected bindings, including the errno-to-reason map. -/
theorem binding_shape :
    ((List.finRange output.compiled.unit.axs.length).map
      (fun a => (output.tor a).map (·.nr))) = [some 39, some 3, some 3] ∧
    ((List.finRange output.compiled.unit.axs.length).map
      (fun a => (output.tor a).map (·.fehler))) = [some [], some [(-9, 0)], some [(-9, 0)]] := by
  decide +kernel

/-- Retain the generic certificate, rather than a program-specific lowering rule. -/
theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- Also exercise a fallible void binder at end-block level directly from source. -/
def endText : String :=
  "module optional_void_end { reason R { Denied = 9 \"denied\" exhaustive } assume boundary \"foreign fixture contract\" falsifier boundary_probe; syscall action(fd : u64) or R abi linux arch x86_64 number 3 regs in { rdi = fd } regs out { rax } clobbers { rcx, r11 } errors { EBADF => Denied } effects { pure } costs <= 8 ops assume boundary falsifier boundary_probe; impl fn main() -> u8 { let saved = 23; let saved? = action(99) else (e) { match e { Denied => { return 9; } } return 0; } return saved; } }"

def endCandidate : Except String (Emitted endText 256) := emit endText 256

theorem end_present : endCandidate.toOption.isSome = true := by decide +kernel

def endOutput : Emitted endText 256 := endCandidate.toOption.get end_present

theorem end_accepted_image : emit endText 256 = .ok endOutput :=
  Gabbro.Grammatik.except_ok_get end_present

theorem end_canonical_source : CanonicalSourceProgram endOutput.compiled :=
  compile_source_program endText endOutput.compiled

theorem end_image_correct [Runner.IR.Kern] [Senke.CloneOK] : endOutput.Correct := endOutput.correct

end Gabbro.Stage0.Pipeline.OptionalForeignBinderWitness
