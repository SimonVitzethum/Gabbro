module

public import Core.Ast.LowLevel.Mem.Execution
public import Core.Beobachtung.Fluss.Satz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog
open Ast.LowLevel (MemInstruction memProgram)

/-- Memory-management instructions execute in their actual program, including reachable
    prefixes that allocate a space or produce a revocation token. -/
def SpeicherverwaltungsNIAussage : Prop :=
  ∀ (k : Katalog) (code : List MemInstruction) (f : MemInstruction),
    RegelFluss (memProgram k code) f → RegelNIPflicht (memProgram k code) f

end Gabbro.Core.Beobachtung
