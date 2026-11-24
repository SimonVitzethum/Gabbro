module

public import Core.Ast.Inventory.Productions
public import Core.Ast.Inventory.Existing
public import Core.Ast.Inventory.LowLevel
public import Core.Ast.Inventory.Further
public import Core.Ast.Inventory.Planned

@[expose] public section

namespace Gabbro.Core.Inventory

/-- The source inventory for M6, M6F, M6L, M9 and M9P. These references describe the
    work to admit a form. Coverage is over the actual constructors. -/
def forms : List SurfaceForm := documentedProductions ++ existingSurface ++ lowLevel ++ further ++ planned

end Gabbro.Core.Inventory
