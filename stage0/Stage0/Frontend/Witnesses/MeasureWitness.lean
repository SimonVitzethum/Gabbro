module
public import Stage0.Compiler
@[expose] public section

namespace Gabbro.Stage0.Frontend.MeasureWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

def characters : List Char :=
  ("type Small = u8 in 0 .. 1; ".toList ++
   "impl fn countdown(n : Small) decreases n ".toList ++
   "{ if n > 0 { countdown(0); } else { } return; } ".toList ++
   "impl fn main() { countdown(1); return; }".toList)

def text : String := String.ofList characters

theorem compiled : (compile text).toOption.isSome = true := by decide +kernel

def result : Compiled text := (compile text).toOption.get compiled

/-- The actual frontend and generic compiler carry the exact source measure through restoration. -/
theorem compile_source_program_zeuge :
    compile text = .ok result ∧ CanonicalSourceProgram result ∧
    Measures.lowerMeasures result.unit = .ok result.measures.val ∧
    Measures.cycleLengths result.unit result.program result.measures.val.mass = true :=
  ⟨except_ok_get compiled, compile_source_program text result,
    result.measures.property, result.measureLengths⟩

/-- The recursive function has the source singleton, while the entry without a clause stays empty. -/
theorem exact_measures_zeuge :
    result.unit.fns.length = 2 ∧
    (match result.unit.fns[0]? with
      | some function => function.decreases = some (.variable "n")
      | none => False) ∧
    (match result.unit.fns[1]? with
      | some function => function.decreases = none
      | none => False) := by decide +kernel

end Gabbro.Stage0.Frontend.MeasureWitness
