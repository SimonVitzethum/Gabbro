module
public import Grammatik.Parser.Elab.Export.ExportMetadata
public import Grammatik.Parser.Elab.Uebersetze
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The current image initializes world bytes to zero. A newly exported scalar initializer
    must not silently acquire that value when its canonical declared value is nonzero. -/
def uninitializedExport (items : List SItemTief) (unit : UProg) : Bool :=
  items.any fun item => match item with
    | .globT _ name _ _ _ _ _ => ExportMetadata.constantExpansion item &&
        (unit.globs.find? (fun global => global.name == name)).any (fun global => global.init != 0)
    | _ => false

def checkInitializers (items : List SItemTief) (unit : UProg) : Except String Unit :=
  if uninitializedExport items unit then
    .error "source export: nonzero scalar initializer requires initialized image memory"
  else .ok ()

theorem checkInitializers_sound (items : List SItemTief) (unit : UProg)
    (accepted : checkInitializers items unit = .ok ()) : uninitializedExport items unit = false := by
  unfold checkInitializers at accepted
  cases h : uninitializedExport items unit <;> simp_all

end Gabbro.Stage0.Frontend
