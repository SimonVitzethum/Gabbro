module

public import Core.Ast.LowLevel.Execution
public import Core.Beobachtung.Fluss.Satz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open Ast.LowLevel (Instruction unit)

/-- Source instructions interpreted over entry regions, views and selected catalogue declarations. -/
def RegionNIAussage : Prop :=
  ∀ (k : Katalog) (op f : Instruction k), RegelFluss (unit op) f → RegelNIPflicht (unit op) f

end Gabbro.Core.Beobachtung
