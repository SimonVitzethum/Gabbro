module
public import Stage0.Diagnose
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Stage0.FrontendDefects
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def clashText : String :=
  "tagged type T = { C, D }; impl fn C() -> u32 in 0 .. 9 { return 1; } impl fn main() -> u32 in 0 .. 255 { return 0; }"

/-- Evaluate the actual compiler in the kernel, including the constructor name table. -/
theorem function_case_clash_zeuge :
    (match compile clashText with
     | .error reason => reason
     | .ok _ => "") = "function and case share a name: C" := by kernel_rfl

def optionText : String :=
  "table T count 4 { slot { v : u32 in 0 .. 9, } } " ++
  "tagged type Message = { Empty, Item(option index into T) }; " ++
  "impl fn value(message : Message) -> u32 in 0 .. 20 effects { pure } { " ++
  "match message { Empty => { return 0; } Item(payload) => { " ++
  "match payload { Some(i) => { return i + 10; } None => { return 7; } } } } } " ++
  "impl fn main() -> u32 in 0 .. 255 effects { pure } { " ++
  "let selected : option index into T = Some(2); " ++
  "let message : Message = Item(selected); return value(message); }"

/-- The option kind survives both source elaboration and lowering into the checked program. -/
theorem option_payload_compiles_zeuge : (compile optionText).toOption.isSome = true := by kernel_rfl

def diagnosticText : String :=
  String.intercalate "\n"
    ["// Header", "impl fn main()", "    effects { pure }", "{",
     "    let s = \"}; // /*\";", "    let c = '}';",
     "    /* outer", "       /* nested */ still */",
     "    if true { let n = 1; } else { let n = 2; }",
     "    let bad = missing;", "    return;", "}"]

/-- Literal/comment braces, an effects block and both conditional arms preserve top-level indices. -/
theorem statement_lines_zeuge :
    Diagnose.statementLine diagnosticText "main" 2 4 "let c" = some 6 ∧
    Diagnose.statementLine diagnosticText "main" 4 4 "let bad" = some 10 :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- Expanded statement counts and kinds that disagree with source are left without a guessed line. -/
theorem statement_line_declines_zeuge :
    Diagnose.statementLine diagnosticText "main" 4 5 "let bad" = none ∧
    Diagnose.statementLine diagnosticText "main" 4 4 "assignment" = none :=
  ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Stage0.FrontendDefects
