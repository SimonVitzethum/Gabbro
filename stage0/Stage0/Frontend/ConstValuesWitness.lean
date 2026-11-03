module
public import Stage0.Frontend.ConstWitness
public import Grammatik.Parser.Elab.Konst.Values.Witness

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstValuesWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The production source path lowers both computed Boolean values to ordinary G. -/
def boolText : String := String.ofList
  ("const fn positive(x : u8 in 0 .. 10) -> bool ".toList ++
   "ensures result == (x > 0) { return x > 0; } ".toList ++
   "impl fn main() -> bool { return positive(3) && !positive(0); }".toList)

theorem bool_compiled_zeuge : (compile boolText).toOption.isSome = true := by decide +kernel

/-- The option retains the exact declared finite domain and its present index. -/
def optionText : String := String.ofList
  ("table Slots count 4 { slot { value : u8, } } ".toList ++
   "const fn selected(x : u8 in 0 .. 3) -> option index into Slots { return Some(x); } ".toList ++
   "impl fn main() -> option index into Slots { return selected(2); }".toList)

theorem option_compiled_zeuge : (compile optionText).toOption.isSome = true := by decide +kernel

def noneText : String := String.ofList
  ("table Slots count 4 { slot { value : u8, } } ".toList ++
   "const fn selected() -> option index into Slots { return None(); } ".toList ++
   "impl fn main() -> option index into Slots { return selected(); }".toList)

theorem none_compiled_zeuge : (compile noneText).toOption.isSome = true := by decide +kernel

/-- Tagged constructor identity and the evaluated numeric payload reach runtime G. -/
def tagText : String := String.ofList
  ("tagged type Choice = { Empty, Data(u8) }; ".toList ++
   "const fn selected(x : u8 in 0 .. 10) -> Choice { return Data(x + 1); } ".toList ++
   "impl fn main() -> Choice { return selected(4); }".toList)

theorem tag_compiled_zeuge : (compile tagText).toOption.isSome = true := by decide +kernel

/-- The byte spelling and declared maximum survive source-to-G compilation. -/
def stringText : String := String.ofList
  ("const fn selected() -> string max 1 { return \"A\"; } ".toList ++
   "impl fn main() -> string max 1 { return selected(); }".toList)

theorem string_compiled_zeuge : (compile stringText).toOption.isSome = true := by decide +kernel

/-- Original global names are certified in the body and at the actual call site. -/
def globalText : String := String.ofList
  ("const K : u8 = 5; ".toList ++
   "const fn addK(x : u8 in 0 .. 10) -> u8 in 0 .. 20 { return x + K; } ".toList ++
   "impl fn main() -> u8 { return addK(K + 1); }".toList)

theorem globals_compiled_zeuge : (compile globalText).toOption.isSome = true := by decide +kernel

def qualifiedText : String := String.ofList
  ("module Constants { pub const K : u8 = 5; } ".toList ++
   "const fn addK(x : u8 in 0 .. 10) -> u8 in 0 .. 20 { return x + Constants::K; } ".toList ++
   "impl fn main() -> u8 { return addK(Constants::K + 1); }".toList)

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
      emit boolText K = .ok output ∧ output.image.bytes = bytes ∧ output.Correct := by
  obtain ⟨output, he, hb, hc, _⟩ := irBild_correct boolText K bytes emitted
  exact ⟨output, he, hb, hc⟩

/-- Excluded control-flow bodies remain refused in the actual source frontend. -/
def blockText : String := String.ofList
  ("const fn selected() -> bool { let x = true; return x; } ".toList ++
   "impl fn main() -> bool { return selected(); }".toList)

theorem block_refused_zeuge : (compile blockText).toOption.isSome = false := by decide +kernel

end Gabbro.Stage0.Frontend.ConstValuesWitness
