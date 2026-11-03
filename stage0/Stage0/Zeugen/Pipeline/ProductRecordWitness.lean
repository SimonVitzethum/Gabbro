module
public import Stage0.Frontend.ExportCorrectness
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


namespace Gabbro.Stage0.Pipeline.ProductRecordWitness
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Labelled construction has two different fields. The update copies the second field
    into the first, and the result reads that changed first field. -/
def text : String :=
  "module product_record_probe { type Pair = { first : u8, second : u8, }; impl fn main() -> u8 { let mut pair : Pair = Pair(first: 7, second: 11); pair.first = pair.second; return pair.first; } }"

/-- The canonical parser accepts the labelled constructor, field read and field assignment. -/
theorem source_present : (Frontend.source text).toOption.isSome = true := by
  decide +kernel

/-- The production path now collects C01 schemas before elaborating constructor and field paths. -/
def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- Construction, replacement using a projected field, and the final projection reach the
    same checked unit and nonempty image. The schema's two fields remain distinct. -/
theorem image_shape :
    output.compiled.unit.records.map (·.name) = ["Pair"] ∧
    output.compiled.unit.records.map (fun schema => schema.fields.map (·.1)) = [["first", "second"]] ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bindW _ _ (.product ..) => true | _ => false) = 1 ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .setVar "pair" (.replace (.param "pair") "first" (.field (.param "pair") "second")) => true
           | _ => false) = 1 ∧
    (fnAt output.compiled.unit output.compiled.main).ret = .val (.field (.param "pair") "first") ∧
    0 < output.image.code.length ∧ 16 < output.bytes.length := by
  decide +kernel

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- The actual nonempty image also instantiates the generic C01 export/simulation theorem. -/
theorem exported_records_ir_correct_zeuge [Runner.IR.Kern] [Senke.CloneOK] :
    ∃ result : Emitted text 256, emit text 256 = .ok result ∧ result.Correct ∧
      0 < result.bytes.length := by
  have image : irBild text 256 = .ok output.bytes := by
    change (emit text 256).map (fun result => result.bytes) = _
    rw [accepted_image]
    rfl
  obtain ⟨result, emitted, bytes, correct, _⟩ :=
    exported_records_ir_correct text 256 output.bytes image
  refine ⟨result, emitted, correct, ?_⟩
  rw [bytes]
  have size := image_shape
  omega

end Gabbro.Stage0.Pipeline.ProductRecordWitness
