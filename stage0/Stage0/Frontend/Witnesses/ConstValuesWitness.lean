module
public import Stage0.Frontend.Witnesses.ConstWitness
public import Grammatik.Parser.Elab.Konst.Values.Witness

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstValuesWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The production source path lowers both computed Boolean values to ordinary G. -/

theorem bool_compiled_zeuge : (compile boolText).toOption.isSome = true := by decide +kernel

/-- The option retains the exact declared finite domain and its present index. -/

theorem option_compiled_zeuge : (compile optionText).toOption.isSome = true := by decide +kernel

theorem none_compiled_zeuge : (compile noneText).toOption.isSome = true := by decide +kernel

/-- Tagged constructor identity and the evaluated numeric payload reach runtime G. -/

theorem tag_compiled_zeuge : (compile tagText).toOption.isSome = true := by decide +kernel

/-- The byte spelling and declared maximum survive source-to-G compilation. -/

theorem string_compiled_zeuge : (compile stringText).toOption.isSome = true := by decide +kernel

/-- Original global names are certified in the body and at the actual call site. -/

theorem globals_compiled_zeuge : (compile globalText).toOption.isSome = true := by decide +kernel

theorem qualified_compiled_zeuge : (compile qualifiedText).toOption.isSome = true := by decide +kernel

/-- The same source result retains the compiler's existing admission theorem. -/
theorem portable_source_pipeline_zeuge :
    ∃ result : Compiled boolText,
      compile boolText = .ok result ∧ CanonicalSourceProgram result ∧
      OldSource.accepts result.unit result.program = .ok true := by
  let result := (compile boolText).toOption.get bool_compiled_zeuge
  exact ⟨result, except_ok_get bool_compiled_zeuge, compile_source_program boolText result, result.accepted⟩

/-- The portable path continues to use the one production image theorem. -/
theorem portable_image_pipeline_zeuge [Runner.IR.Kern] [Senke.CloneOK]
    (K : Nat) (bytes : List Runner.B) (emitted : irBild boolText K = .ok bytes) :
    ∃ output : Emitted boolText K,
      emit boolText K = .ok output ∧ output.bytes = bytes ∧ output.Correct := by
  obtain ⟨output, he, hb, hc, _⟩ := irBild_correct boolText K bytes emitted
  exact ⟨output, he, hb, hc⟩

/-- Excluded control-flow bodies remain refused in the actual source frontend. -/

theorem block_refused_zeuge : (compile blockText).toOption.isSome = false := by decide +kernel

end Gabbro.Stage0.Frontend.ConstValuesWitness
