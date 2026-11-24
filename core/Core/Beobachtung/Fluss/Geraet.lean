module

public import Core.Ast.LowLevel.DeviceUnit
public import Core.Beobachtung.Fluss.Satz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open Ast.LowLevel.Device (Denotation)

/-- Device steps are interpreted through the selected catalogue row in the actual unit. -/
def GeraeteNIAussage : Prop :=
  ∀ (k : Katalog) (scope : Ast.Scope) (locals : Ast.Umgebung scope) (d : Denotation k scope),
    RegelFluss (d.unit locals) () → RegelNIPflicht (d.unit locals) ()

end Gabbro.Core.Beobachtung
