module

public import Init.Data.String.Basic

@[expose] public section

namespace Gabbro.Core.Inventory

/-- A review reference in the repository, with a section, production, or declaration as locator. -/
structure SourceReference where
  file : String
  locator : String

/-- Inventory data records a source form before its rules are written.
    Its key is a review handle and is independent of Lean constructor identity. -/
structure SurfaceForm where
  key : String
  description : String
  reference : SourceReference

end Gabbro.Core.Inventory
