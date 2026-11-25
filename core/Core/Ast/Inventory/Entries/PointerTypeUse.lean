module

public import Core.Ast.Inventory.Entries.PointerType
public import Core.Ast.Inventory.Entries.ScalarTypes

namespace Gabbro.Core.Ast.Semantik

open Waechter

/-- The pinned pointer type-use statement is the universal written-type use. Its proof is the
    `LocalTypeUseAussage` carried by the scalar registry entry for that same universal selector:
    a pointer-typed binding runs the same local-type recipe as every other written type. -/
public theorem pointerTypeUse : PointerTypeUseAussage := by
  unfold PointerTypeUseAussage
  exact boolTypeEntry.proof.2.1

end Gabbro.Core.Ast.Semantik
