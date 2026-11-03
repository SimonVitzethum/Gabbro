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


namespace Gabbro.Stage0.Pipeline.OptionalForeignWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The optional foreign result is returned, and the source supplies an executable gate
    binding. This does not rely on an unbound axiom or a discarded optional result. -/
def text : String :=
  "module optional_foreign_probe { assume pid_contract \"getpid answers a pid\" falsifier pid_probe; syscall getpid() -> u64 in 1 .. 4194304 abi linux arch x86_64 number 39 regs in { } regs out { rax } clobbers { rcx, r11 } errors { } effects { pure } costs <= 8 ops assume pid_contract falsifier pid_probe; impl fn main() -> u64 in 1 .. 4194304 { let answer? = getpid(); return answer; } }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- One real foreign declaration and binding survive into a nonempty IR image. -/
theorem image_shape :
    output.compiled.unit.fns.length = 1 ∧
    output.compiled.unit.axs.map (·.name) = ["getpid"] ∧
    ((List.finRange output.compiled.unit.axs.length).map
      (fun a => (output.tor a).map (·.nr))) = [some 39] ∧
    0 < output.image.code.length ∧ 16 < output.bytes.length := by
  decide +kernel

/-- The accepted image retains the actual compiler's canonical source-program certificate. -/
theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- Keep optional binding and a value-discarding fallible foreign statement in one
    source program. The statement handler consumes its reason and has a distinct answer. -/
def statementText : String :=
  "module optional_foreign_statement_probe { reason R { Denied = 9 \"denied\" exhaustive } axiom value() -> u8 effects { pure } unfalsifiable \"probe\"; syscall action() -> u8 or R via sys_action effects { pure } costs <= 8 ops; syscall sys_action; impl fn main() -> u8 { let answer? = value(); action() else (e) { match e { Denied => { return 9; } } return 0; } return answer; } }"

/-- SYNTAX.md §7 defines handlers only on bindings: `parseRufSchwanz` requires `;` here.
    `let ignored = action() else (e) { ... }` instead emits bindAxiomElse; no source
    producer emits Stmt.axiomCallElse. The optional image above remains independent. -/
theorem statement_parser_refused :
    ((Gabbro.Grammatik.Parser.lex statementText).mapError (fun _ => "lex")).bind
      Gabbro.Grammatik.Parser.parseTopTief = .error "wanted ;" := by
  decide +kernel

theorem statement_image_refused : emit statementText 256 = .error "wanted ;" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.OptionalForeignWitness
