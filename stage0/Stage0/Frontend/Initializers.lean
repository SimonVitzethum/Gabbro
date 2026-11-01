import Grammatik.Parser.Elab.ExportMetadata
import Grammatik.Parser.Elab.Uebersetze

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

/-- A genuine nonzero expanded initializer is refused; an exactly zero one is admitted. -/
theorem checkInitializers_zeuge :
    checkInitializers [.globT false "VALUE" (.atom "u8") (.one (.bin "+" (.lit 20) (.lit 22))) none none false]
      {tabs := [], locks := [], fns := [], globs := [{name := "VALUE", ty := .int 0 255, init := 42}]} =
      .error "source export: nonzero scalar initializer requires initialized image memory" ∧
    checkInitializers [.globT false "VALUE" (.atom "u8") (.one (.bin "-" (.lit 42) (.lit 42))) none none false]
      {tabs := [], locks := [], fns := [], globs := [{name := "VALUE", ty := .int 0 255, init := 0}]} = .ok () := ⟨rfl, rfl⟩

end Gabbro.Stage0.Frontend
