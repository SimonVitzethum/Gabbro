module
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

namespace Gabbro.Stage0.EntrustWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- An explicit executable C08 binding with nontrivial region predicates.
    `kernel services::isolate` names software; it asserts no hardware isolation.
    Proving its implementation and GuestServicePflicht remains user logic. -/
def text : String :=
  "table Code count 1 { slot { value : u8, } } reason Failure { Denied = 9 \"denied\" exhaustive } syscall isolate(code : ptr<normal, r> Code) -> u8 in 0 .. 10 or Failure abi linux arch x86_64 number 3 regs in { rdi = code } regs out { rax } clobbers { rcx, r11 } errors { EBADF => Denied } requires forall i in slots of Code : Code.slots[i].value == 7 ensures forall i in slots of Code : Code.slots[i].value == 7 effects { pure } kernel services::isolate; entrust guest at Code arch x86_64 via isolate; impl fn main(code : ptr<normal, r> Code) -> u8 in 0 .. 10 { let answer = guest(code) else (e) { match e { Denied => { return 9; } } return 0; } return answer; }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- Production admission, after restoring original function postconditions. -/
theorem accepted_source : OldSource.accepts output.compiled.unit output.compiled.program = .ok true :=
  output.compiled.accepted

/-- Both checker variants receive the real descriptor, rather than an empty
    list. This fixture has one table and no locks, globals or started roots. -/
theorem checked_unit :
    (sourceGuests output.compiled.unit).map (fun guests =>
      Akzeptiert output.compiled.program (sperrFamilie output.compiled.unit)
        (List.finRange output.compiled.unit.fns.length) []
        ((List.finRange output.compiled.unit.tabs.length).map Sum.inl) [] [] [] [] guests) = .ok true := by
  decide +kernel

/-- The service, its two contracts and its software provenance all survive
    source elaboration, alongside exactly one descriptor and one wrapper. -/
theorem source_shape :
    output.compiled.unit.guests = [⟨"guest", "Code", "x86_64", "isolate"⟩] ∧
    output.compiled.unit.fns.map (·.name) = ["main", "guest"] ∧
    output.compiled.unit.axs.map (·.name) = ["isolate"] ∧
    output.compiled.unit.axs.map (fun a => (a.needs.length, a.gives.length)) = [(1, 1)] ∧
    output.compiled.unit.axs.map (·.software) = [true] ∧
    output.compiled.unit.axs.map (·.beleg) = [none] ∧
    0 < output.image.code.length := by decide +kernel

/-- The wrapper reaches precisely the already verified fallible optional
    foreign-call lowering arm, including its explicit failure continuation. -/
theorem ordinary_fallible_lowering :
    (match output.compiled.program.rumpf ⟨1, by decide +kernel⟩ with
    | .bindAxiomOptElse .. => true
    | _ => false) = true := by decide +kernel

theorem service_provenance :
    (declOf output.compiled.unit).axHerkunft ⟨0, by decide +kernel⟩ = some AxOrigin.software ∧
    (declOf output.compiled.unit).axBeleg ⟨0, by decide +kernel⟩ = none := by decide +kernel

/-- Generic exact-contract transport instantiated at the actual source image. -/
theorem exact_contract :
    lowerAxContract output.compiled.unit ⟨0, by decide +kernel⟩ =
      .ok (output.compiled.program.axVertrag ⟨0, by decide +kernel⟩) :=
  output.compiled.foreign_contracts _

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

def refusal (source : String) : Option String :=
  match emit source 256 with | .error error => some error | .ok _ => none

theorem missing_service :
    refusal (text.replace "via isolate;" "via absent;") =
      some "entrust: missing isolation service binding" := by decide +kernel

theorem absent_service_field :
    refusal (text.replace "via isolate;" ";") =
      some "entrust: missing isolation service binding" := by decide +kernel

theorem unowned_region :
    refusal (text.replace "code : ptr<normal, r> Code) -> u8 in 0 .. 10 or Failure"
      "code : ptr<normal, r> Code, data : ptr<normal, rw> Code) -> u8 in 0 .. 10 or Failure") =
      some "entrust: caller does not own a transferred region" := by decide +kernel

theorem register_state :
    refusal (text.replace "via isolate;"
      "via isolate { regs in { argument : rdi } stack Stack assume isolation; }") =
      some "entrust: register-state or privileged transfer is excluded" := by decide +kernel

theorem privileged_fields :
    refusal (text.replace "via isolate;"
      "via isolate { regs in {} stack privileged_stack assume isolation; }") =
      some "entrust: register-state or privileged transfer is excluded" := by decide +kernel

theorem unknown_abi :
    refusal (text.replace "entrust guest at Code arch x86_64" "entrust guest at Code arch z80") =
      some "entrust: unknown userspace ABI" := by decide +kernel

theorem infallible_service :
    refusal (text.replace "or Failure abi" "abi") =
      some "entrust: isolation service needs a failure channel" := by decide +kernel

theorem missing_region_contract :
    refusal (text.replace "requires forall i in slots of Code : Code.slots[i].value == 7" "requires true") =
      some "entrust: isolation service contract does not mention transferred regions" := by decide +kernel

end Gabbro.Stage0.EntrustWitness
