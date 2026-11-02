module

public import Grammatik.Parser.Elab.Uebersetze.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser.Capabilities

open Uebersetze

def tables : List UTab := [{ name := "Bytes", count := 4, cols := [("value", (0, 255))] }]

/-- Both type and parameter elaboration normalize the complete rights union. -/
theorem uTableRight_sound_zeuge :
    uTyp [] tables (.ptr "normal" "w+r+r" (.atom "Bytes")) = .ok (.ptr 0 true) ∧
    uParam [] tables [] [] [] 0 ("buffer", .ptr "normal" "w+r+r" (.atom "Bytes")) =
      .ok ("buffer", .ptr 0 true, .ptr 0 true) := by
  exact ⟨rfl, rfl⟩

theorem read_only_preserved :
    uTyp [] tables (.ptr "normal" "r+r" (.atom "Bytes")) = .ok (.ptr 0 false) := by rfl

/-- No owner spelling is silently represented by the ordinary writable-pointer flag. -/
theorem owner_type_refused :
    (uTyp [] tables (.ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_parameter_refused :
    (uParam [] tables [] [] [] 0 ("buffer", .ptr "normal" "own" (.atom "Bytes"))).toOption = none := by rfl

theorem owner_in_union_refused :
    (uTyp [] tables (.ptr "normal" "rw+own@lease" (.atom "Bytes"))).toOption = none := by rfl

/-- Until descriptor-indexed pointers are connected, write-only rights must remain refused. -/
theorem write_only_refused :
    (uTyp [] tables (.ptr "normal" "w+w" (.atom "Bytes"))).toOption = none := by rfl

theorem data_execute_refused :
    (uTyp [] tables (.ptr "normal" "r+w+x" (.atom "Bytes"))).toOption = none := by rfl

theorem empty_component_refused :
    (uTyp [] tables (.ptr "normal" "rw+" (.atom "Bytes"))).toOption = none := by rfl

theorem unknown_component_refused :
    (uTyp [] tables (.ptr "normal" "r+unknown" (.atom "Bytes"))).toOption = none := by rfl

theorem nominal_space_without_binding_refused :
    (uTyp [] tables (.ptr "sharedData" "rw" (.atom "Bytes"))).toOption = none := by rfl

end Gabbro.Grammatik.Parser.Capabilities
