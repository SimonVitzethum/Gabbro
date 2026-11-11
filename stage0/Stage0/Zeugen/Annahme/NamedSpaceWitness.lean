module
public import Stage0.IRBild
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
namespace Gabbro.Stage0.NamedSpaceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 400000

def text : String :=
  "module named_space_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main() -> u32 in 0 .. 100 effects { reads T.slots } { return T.slots[0].v; } }"

def pointerText : String :=
  "module named_space_pointer_probe { table T count 2 space sharedData { slot { v : u32 in 0 .. 100, } } impl fn main(p : ptr<sharedData, r> T) -> u32 in 0 .. 100 effects { reads p.slots } { return p.slots[0].v; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by
  kernel_rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output := except_ok_get candidate_present

def pointerCandidate : Except String (Emitted pointerText 64) := emit pointerText 64

theorem pointer_candidate_present : pointerCandidate.toOption.isSome = true := by
  kernel_rfl

def pointerOutput : Emitted pointerText 64 :=
  pointerCandidate.toOption.get pointer_candidate_present

theorem pointer_accepted_image : emit pointerText 64 = .ok pointerOutput :=
  except_ok_get pointer_candidate_present

theorem pointer_table_bound : 0 < pointerOutput.compiled.unit.tabs.length := by
  exact Nat.lt_of_lt_of_eq Nat.zero_lt_one (by kernel_rfl : (1 : Nat) = _)

/-- Both actual source units register a nonzero nominal space without an owner. -/
theorem table_space :
    output.compiled.unit.spaces = ["normal", "sharedData"] ∧
    (output.compiled.unit.tabs[0]?).map (fun table => (table.space, table.owner, table.count)) =
      some (1, none, 2) := by
  exact ⟨by kernel_rfl, by kernel_rfl⟩

/-- The written pointer retains the same space, table identity and exact read right. -/
theorem pointer_space :
    (declOf pointerOutput.compiled.unit).params pointerOutput.compiled.main =
      [.ptr ⟨1, ⟨true, false, none⟩, .table 0⟩] ∧
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      (declOf pointerOutput.compiled.unit).capTab 1 0 = some ⟨0, bound⟩ := by
  constructor
  · kernel_rfl
  · intro bound
    kernel_rfl

/-- The checked lowerer's own gate refuses a foreign space on the same actual
    source table; no inconsistent function metadata or fabricated image is used. -/
theorem incompatible_space_refused :
    ∀ bound : 0 < pointerOutput.compiled.unit.tabs.length,
      checkedTableCap pointerOutput.compiled.unit 0 0 bound =
        .error "pointer table space is not registered" := by
  intro bound
  kernel_rfl

theorem incompatible_table_cap_refused :
    checkedTableCap pointerOutput.compiled.unit 0 0 pointer_table_bound =
      .error "pointer table space is not registered" := incompatible_space_refused pointer_table_bound

/-- Space lookup still rejects a name not declared by either source table. -/
theorem unknown_pointer_space_refused :
    uTypIn [] pointerOutput.compiled.unit.tabs [] pointerOutput.compiled.unit.spaces []
      (.ptr "missing" "r" (.atom "T")) = .error "unknown data space: missing" := by
  kernel_rfl

/-- Repeated declarations share an ordinal; repeated binders in one header fail. -/
theorem space_declarations :
    uSpaces [.tableT "A" none (some (.lit 1)) none none false [] (some "Data"),
      .tableT "B" none (some (.lit 1)) none none false [] (some "Data"),
      .tableT "C" none (some (.lit 1)) none none false [] (some "Other")] =
      ["normal", "Data", "Other"] ∧
    parseTabellenKopf 8 [.wort "space", .wort "Data", .wort "space", .wort "Other", .zeichen "{"] =
      .error "duplicate table space binding" := by
  constructor <;> cbv

/-- Missing nominal names are grammar errors, never an implicit normal binding. -/
theorem malformed_space_refused :
    parseTabellenKopf 8 [.wort "space", .zeichen "{"] = .error "name expected" := by cbv

/-- Both binders retain their own field, and a space never declares a linear mark. -/
theorem owner_space_independent :
    parseTabellenKopf 8 [.wort "space", .wort "Data", .wort "owner", .wort "Mark", .zeichen "{"] =
      .ok ((none, none, none, some "Mark", false, some "Data"), [.zeichen "{"]) ∧
    uPruefEigner [] (some "Mark") = .error "owner without declared linear mark: Mark" := by
  constructor <;> cbv

theorem images_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct ∧ pointerOutput.Correct :=
  ⟨output.correct, pointerOutput.correct⟩

end Gabbro.Stage0.NamedSpaceWitness
