module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values

@[expose] public section

namespace Gabbro.Grammatik.Parser.Capabilities

open Uebersetze

def tables : List UTab := [{ name := "Bytes", count := 4, cols := [("value", (0, 255))] }]

/-- Both type and parameter elaboration normalize the complete rights union. -/
theorem uTableRight_sound_zeuge :
    uTyp [] tables ["normal"] [] (.ptr "normal" "w+r+r" (.atom "Bytes")) = .ok (.ptr (.table 0 (true, true))) ∧
    uParam [] tables [] [] [] 0 ["normal"] [] [] ("buffer", .ptr "normal" "w+r+r" (.atom "Bytes")) =
      .ok ("buffer", .ptr (.table 0 (true, true)), .ptr (.table 0 (true, true))) := by
  exact ⟨rfl, rfl⟩

theorem read_only_preserved :
    uTyp [] tables ["normal"] [] (.ptr "normal" "r+r" (.atom "Bytes")) = .ok (.ptr (.table 0 (true, false))) := by rfl

/-- No owner spelling is silently represented by the ordinary writable-pointer flag. -/
theorem owner_type_refused :
    (uTyp [] tables ["normal"] [] (.ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

/-- The owner namespace resolves a declared mark to its index and nothing else. -/
theorem uEignerNr_zeuge :
    uEignerNr ["lease"] "lease" = some 0 ∧ uEignerNr ["lease"] "nope" = none := by
  exact ⟨rfl, rfl⟩

/-- `own@lease` resolves against the declared owner namespace and travels in
    the capability, never via the read/write flags. -/
def eignerLease : List String := ["lease"]

theorem owned_rights_resolve :
    uTyp [] tables ["normal"] (eigner := eignerLease) (.ptr "normal" "rw+own@lease" (.atom "Bytes")) =
      .ok (.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩) := by rfl

theorem owned_parameter_resolve :
    uParam [] tables [] [] [] 0 ["normal"] [] (eigner := eignerLease) ("buffer", .ptr "normal" "own@lease" (.atom "Bytes")) =
      .ok ("buffer", .ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩, .ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩) := by rfl

/-- An undeclared owner fails closed at export. -/
theorem unknown_owner_refused :
    (uTyp [] tables ["normal"] (eigner := eignerLease) (.ptr "normal" "rw+own@nope" (.atom "Bytes"))).toOption = none := by rfl

/-- Bare `own` stays refused: it is the consumes/allocs sugar and needs the
    C09 signature flow before admission. -/
theorem bare_own_still_refused :
    (uTyp [] tables ["normal"] (eigner := eignerLease) (.ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_parameter_refused :
    (uParam [] tables [] [] [] 0 ["normal"] [] [] ("buffer", .ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_in_union_refused :
    (uTyp [] tables ["normal"] [] (.ptr "normal" "rw+own@lease" (.atom "Bytes"))).toOption = none := by rfl

/-- A write-only descriptor preserves its missing read permission in both export paths. -/
theorem write_only_preserved :
    uTyp [] tables ["normal"] [] (.ptr "normal" "w+w" (.atom "Bytes")) = .ok (.ptr (.table 0 (false, true))) ∧
    uParam [] tables [] [] [] 0 ["normal"] [] [] ("buffer", .ptr "normal" "w+w" (.atom "Bytes")) =
      .ok ("buffer", .ptr (.table 0 (false, true)), .ptr (.table 0 (false, true))) := by
  exact ⟨rfl, rfl⟩

theorem data_execute_refused :
    (uTyp [] tables ["normal"] [] (.ptr "normal" "r+w+x" (.atom "Bytes"))).toOption = none := by rfl

theorem empty_component_refused :
    (uTyp [] tables ["normal"] [] (.ptr "normal" "rw+" (.atom "Bytes"))).toOption = none := by rfl

theorem unknown_component_refused :
    (uTyp [] tables ["normal"] [] (.ptr "normal" "r+unknown" (.atom "Bytes"))).toOption = none := by rfl

theorem nominal_space_without_binding_refused :
    (uTyp [] tables ["normal"] [] (.ptr "sharedData" "rw" (.atom "Bytes"))).toOption = none := by rfl

def context (access : Bool × Bool) : UCtx := { names := ["buffer"], kinds := [.ptr (.table 0 access)], types := [.ptr (.table 0 access)], tabs := tables, locks := [], held := [], res := none, fname := "capability_probe", alias := [], lits := [] }

/-- An owned capability passes through a call where the same owned
    capability is expected: the owner mark is carried, not checked away. -/
def ownedContext : UCtx := { names := ["buffer"], kinds := [.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩], types := [.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩], tabs := tables, locks := [], held := [], res := none, fname := "owned_probe", alias := [], lits := [] }

theorem owned_argument_passes :
    uArg ownedContext tables (.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩) (.variable "buffer") =
      .ok (.var "buffer") := by rfl

/-- An explicit re-view may discard access but never the owner mark. -/
theorem owned_attenuation_zeuge :
    uArg ownedContext tables (.ptr ⟨0, ⟨true, false, some 0⟩, .table 0⟩) (.variable "buffer") =
      .ok (.freshPtr "Bytes" ⟨0, ⟨true, false, some 0⟩, .table 0⟩) := by rfl

/-- A result type carries the owned capability unchanged into the return position. -/
def probeFn : UFn := { name := "f", params := [], kinds := [], res := none, held := [], puts := [], gives := [], needs := [], body := [], ret := .empty }

theorem owned_result_kind :
    Gabbro.Grammatik.Parser.UebersetzeAllg.resultKind probeFn (.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩) =
      .ok (.ptr ⟨0, ⟨true, true, some 0⟩, .table 0⟩) := by rfl

/-- A different space is a different capability, even with the same owner. -/
theorem cross_space_argument_refused :
    (uArg ownedContext tables (.ptr ⟨1, ⟨true, true, some 0⟩, .table 0⟩) (.variable "buffer")).toOption = none := by rfl

/-- Data execution stays refused, including beside a resolved owner. -/
theorem own_execute_refused :
    (uTyp [] tables ["normal"] (eigner := eignerLease) (.ptr "normal" "r+w+x+own@lease" (.atom "Bytes"))).toOption = none := by rfl

/-- An out-of-extent index is refused before any access. -/
theorem index_outside_count :
    (uIndex (context (true, true)) "Bytes" 0 (.lit 4)).toOption = none := by rfl

/-- Passing a write-only argument cannot manufacture a read permission. -/
theorem widening_argument_refused :
    (uArg (context (false, true)) tables (.ptr (.table 0 (true, false))) (.variable "buffer")).toOption = none := by rfl

/-- An explicit re-view may discard read access while preserving the target and space. -/
theorem attenuated_argument_zeuge :
    uArg (context (true, true)) tables (.ptr (.table 0 (false, true))) (.variable "buffer") =
      .ok (.freshPtr "Bytes" (.table 0 (false, true))) := by rfl

theorem byte_grants_refused_by_name :
    uTyp [] tables ["normal"] [] (.ptr "normal" "rw" (.atom "u8")) =
      .error "live byte capability requires C01 value flow, C08 grant generations and C09 loans" := by rfl

theorem entry_handles_refused_by_name :
    uTyp [] tables [] [] (.entry "root" none) =
      .error "entry handle requires C08/C14 binding and C09 forwarding flow" := by rfl

end Gabbro.Grammatik.Parser.Capabilities
