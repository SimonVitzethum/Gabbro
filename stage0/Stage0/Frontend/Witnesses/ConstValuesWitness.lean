module
public import Stage0.Frontend.Witnesses.ConstWitness
public import Grammatik.Parser.Elab.Konst.Values.Witness
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
namespace Gabbro.Stage0.Frontend.ConstValuesWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The production source path lowers both computed Boolean values to ordinary G. -/
theorem bool_compiled_zeuge : (compile boolText).toOption.isSome = true := by
  kernel_rfl

/-- The option retains the exact declared finite domain and its present index. -/
theorem option_compiled_zeuge : (compile optionText).toOption.isSome = true := by
  kernel_rfl

theorem none_compiled_zeuge : (compile noneText).toOption.isSome = true := by
  kernel_rfl

/-- Tagged constructor identity and the evaluated numeric payload reach runtime G. -/
theorem tag_compiled_zeuge : (compile tagText).toOption.isSome = true := by
  kernel_rfl

/-- The byte spelling and declared maximum survive source-to-G compilation. -/
theorem string_compiled_zeuge : (compile stringText).toOption.isSome = true := by
  kernel_rfl

/-- Original global names are certified in the body and at the actual call site. -/
theorem globals_compiled_zeuge : (compile globalText).toOption.isSome = true := by
  kernel_rfl

theorem qualified_compiled_zeuge : (compile qualifiedText).toOption.isSome = true := by
  kernel_rfl

/-- The same source result retains the compiler's existing admission theorem. -/
theorem portable_source_pipeline_zeuge :
    ∃ result : Compiled boolText,
      compile boolText = .ok result ∧ CanonicalSourceProgram result ∧
      OldSource.accepts result.unit result.program result.main = .ok true := by
  exact ⟨_, except_ok_get bool_compiled_zeuge, compile_source_program boolText _,
    Compiled.accepted _⟩

/-- The portable path continues to use the one production image theorem. -/
theorem portable_image_pipeline_zeuge [Runner.IR.Kern] [Senke.CloneOK]
    (K : Nat) (bytes : List Runner.B) (emitted : irBild boolText K = .ok bytes) :
    ∃ output : Emitted boolText K,
      emit boolText K = .ok output ∧ output.bytes = bytes ∧ output.Correct := by
  obtain ⟨output, he, hb, hc, _⟩ := irBild_correct boolText K bytes emitted
  exact ⟨output, he, hb, hc⟩

/-- Excluded control-flow bodies remain refused in the actual source frontend. -/
theorem block_refused_zeuge : (compile blockText).toOption.isSome = false := by
  kernel_rfl

end Gabbro.Stage0.Frontend.ConstValuesWitness
