module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6

@[expose] public section

namespace Gabbro.Grammatik.Parser.Capabilities

open Uebersetze

def tables : List UTab := [{ name := "Bytes", count := 4, cols := [("value", (0, 255))] }]

/-- Both type and parameter elaboration normalize the complete rights union. -/
theorem uTableRight_sound_zeuge :
    uTyp [] tables [] (.ptr "normal" "w+r+r" (.atom "Bytes")) = .ok (.ptr (.table 0 (true, true))) ∧
    uParam [] tables [] [] [] 0 [] ("buffer", .ptr "normal" "w+r+r" (.atom "Bytes")) =
      .ok ("buffer", .ptr (.table 0 (true, true)), .ptr (.table 0 (true, true))) := by
  exact ⟨rfl, rfl⟩

theorem read_only_preserved :
    uTyp [] tables [] (.ptr "normal" "r+r" (.atom "Bytes")) = .ok (.ptr (.table 0 (true, false))) := by rfl

/-- No owner spelling is silently represented by the ordinary writable-pointer flag. -/
theorem owner_type_refused :
    (uTyp [] tables [] (.ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_parameter_refused :
    (uParam [] tables [] [] [] 0 [] ("buffer", .ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_in_union_refused :
    (uTyp [] tables [] (.ptr "normal" "rw+own@lease" (.atom "Bytes"))).toOption = none := by rfl

/-- A write-only descriptor preserves its missing read permission in both export paths. -/
theorem write_only_preserved :
    uTyp [] tables [] (.ptr "normal" "w+w" (.atom "Bytes")) = .ok (.ptr (.table 0 (false, true))) ∧
    uParam [] tables [] [] [] 0 [] ("buffer", .ptr "normal" "w+w" (.atom "Bytes")) =
      .ok ("buffer", .ptr (.table 0 (false, true)), .ptr (.table 0 (false, true))) := by
  exact ⟨rfl, rfl⟩

theorem data_execute_refused :
    (uTyp [] tables [] (.ptr "normal" "r+w+x" (.atom "Bytes"))).toOption = none := by rfl

theorem empty_component_refused :
    (uTyp [] tables [] (.ptr "normal" "rw+" (.atom "Bytes"))).toOption = none := by rfl

theorem unknown_component_refused :
    (uTyp [] tables [] (.ptr "normal" "r+unknown" (.atom "Bytes"))).toOption = none := by rfl

theorem nominal_space_without_binding_refused :
    (uTyp [] tables [] (.ptr "sharedData" "rw" (.atom "Bytes"))).toOption = none := by rfl

def context (access : Bool × Bool) : UCtx := { names := ["buffer"], kinds := [.ptr (.table 0 access)], types := [.ptr (.table 0 access)], tabs := tables, locks := [], held := [], res := none, fname := "capability_probe", alias := [], lits := [] }

/-- Passing a write-only argument cannot manufacture a read permission. -/
theorem widening_argument_refused :
    (uArg (context (false, true)) tables (.ptr (.table 0 (true, false))) (.variable "buffer")).toOption = none := by rfl

/-- An explicit re-view may discard read access while preserving the target and space. -/
theorem attenuated_argument_zeuge :
    uArg (context (true, true)) tables (.ptr (.table 0 (false, true))) (.variable "buffer") =
      .ok (.freshPtr "Bytes" (.table 0 (false, true))) := by rfl

theorem byte_grants_refused_by_name :
    uTyp [] tables [] (.ptr "normal" "rw" (.atom "u8")) =
      .error "live byte capability requires C01 value flow, C08 grant generations and C09 loans" := by rfl

theorem entry_handles_refused_by_name :
    uTyp [] tables [] (.entry "root" none) =
      .error "entry handle requires C08/C14 binding and C09 forwarding flow" := by rfl

end Gabbro.Grammatik.Parser.Capabilities
