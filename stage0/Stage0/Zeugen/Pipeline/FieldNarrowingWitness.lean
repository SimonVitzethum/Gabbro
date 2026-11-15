module
public import Stage0.IRBild
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Repr
import all Init.Data.ToString.Basic
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


namespace Gabbro.Stage0.Pipeline.FieldNarrowingWitness
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


/-- A numeric record field is read once, checked, and returned at its successful range. -/
def text : String :=
  "module field_narrow { type Entry = { pos : u64, other : u8, }; impl fn main() -> u8 { let e : Entry = Entry(pos: 23, other: 7); narrow e.pos to 0 .. 63 else { return e.other; } return e.pos; } }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  kernel_rfl

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneAnswers] : output.Correct := output.correct

/-- The existing G narrowing path receives the actual field snapshot, and the final
    return uses that checked local rather than rereading the original wide field. -/
theorem model_shape_zeuge :
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .bind "#fieldNarrow:0" _ (.field (.param "e") "pos") => true | _ => false) = 1 ∧
    (fnAt output.compiled.unit output.compiled.main).body.countP
      (fun | .narrowBeg "#fieldNarrow:0" 0 63 => true | _ => false) = 1 ∧
    (fnAt output.compiled.unit output.compiled.main).ret = .val (.param "#fieldNarrow:0") :=
  ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

/-- A later write invalidates the refined read, so the wide field cannot be returned as u8. -/
def changedField : String :=
  "module field_narrow { type Entry = { pos : u64, other : u8, }; impl fn main() -> u8 { let mut e : Entry = Entry(pos: 23, other: 7); narrow e.pos to 0 .. 63 else { return e.other; } e.pos = 100; return e.pos; } }"

theorem changed_field_refused_zeuge : (emit changedField 256).toOption.isSome = false := by
  kernel_rfl

/-- Validation also permits incrementing the field itself without an overflowing u64 range.
    The subsequent return uses the record at its declared type, after the fact was invalidated. -/
def firstWrite : String :=
  "module field_write { type Entry = { pos : u64, other : u8, }; impl fn main() -> u64 { let mut e : Entry = Entry(pos: 23, other: 7); narrow e.pos to 0 .. 63 else { return 7; } e.pos += 1; return e.pos; } }"

theorem first_write_emitted_zeuge : (emit firstWrite 256).toOption.isSome = true := by
  kernel_rfl

/-- The checked field can index an actual table write without being treated as a target. -/
def indexedStore : String :=
  "module field_store { table T count 2 { slot { value : u8, } } type Entry = { pos : u64, }; impl fn main() -> u8 effects { writes T.slots } { let e : Entry = Entry(pos: 1); narrow e.pos to 0 .. 1 else { return 7; } T.slots[e.pos].value = 23; return e.pos; } }"

theorem indexed_store_emitted_zeuge : (emit indexedStore 256).toOption.isSome = true := by
  kernel_rfl

def staleStore : String :=
  "module field_store { table T count 2 { slot { value : u8, } } type Entry = { pos : u64, }; impl fn main() -> u8 effects { writes T.slots } { let mut e : Entry = Entry(pos: 1); narrow e.pos to 0 .. 1 else { return 7; } e.pos = 100; T.slots[e.pos].value = 23; return 23; } }"

/-- A real record mutation still invalidates the index proof before the later store. -/
theorem stale_store_refused_zeuge : (emit staleStore 256).toOption.isSome = false := by
  kernel_rfl

/-- Shadowing introduces a different record, without inheriting the old field's range. -/
def shadowedRecord : String :=
  "module field_narrow { type Entry = { pos : u64, other : u8, }; impl fn main() -> u8 { let e : Entry = Entry(pos: 23, other: 7); narrow e.pos to 0 .. 63 else { return e.other; } let e : Entry = Entry(pos: 1000, other: 7); return e.pos; } }"

theorem shadowed_record_refused_zeuge : (emit shadowedRecord 256).toOption.isSome = false := by
  kernel_rfl

/-- A nonnumeric field cannot acquire an integer range through this sugar. -/
def booleanField : String :=
  "module field_narrow { type Entry = { flag : bool, }; impl fn main() -> u8 { let e : Entry = Entry(flag: true); narrow e.flag to 0 .. 1 else { return 7; } return 0; } }"

theorem boolean_field_refused_zeuge : (emit booleanField 256).toOption.isSome = false := by
  kernel_rfl

end Gabbro.Stage0.Pipeline.FieldNarrowingWitness
