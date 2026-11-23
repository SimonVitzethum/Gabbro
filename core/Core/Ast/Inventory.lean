module

public import Core.Ast.Inventory.Productions
public import Core.Ast.Inventory.Existing
public import Core.Ast.Inventory.LowLevel
public import Core.Ast.Inventory.Further

@[expose] public section

namespace Gabbro.Core.Inventory

/-- The source inventory for M6, M6F and M6L. These references describe the
    work to admit a form. Coverage is over the actual constructors. -/
def forms : List SurfaceForm := documentedProductions ++ existingSurface ++ lowLevel ++ further

end Gabbro.Core.Inventory
