module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The zero test of the concrete loop (empty `cf` block, `frei = 10`) starts
    at offset 44: a literal zero in slot 15, the comparison of slots 15 and 16,
    and a conditional that jumps three instructions ahead when false. -/
theorem rfindSchleifeNulltestLage :
    (rfindSchleife ([] : List Befehl) 0 10).length = 53 ∧
    (rfindSchleife ([] : List Befehl) 0 10)[44]? = some (.literal 15 0) ∧
    (rfindSchleife ([] : List Befehl) 0 10)[45]? = some (.vergleichen .lt 15) ∧
    (rfindSchleife ([] : List Befehl) 0 10)[46]? = some (.springeWenn 15 false 3) := by
  repeat' constructor <;> rfl

/-- The back edge of the concrete loop sits at offset 49 and jumps to offset
    zero. -/
theorem rfindSchleifeRueckkehrLage :
    (rfindSchleife ([] : List Befehl) 0 10)[47]? = some (.literal 17 1) ∧
    (rfindSchleife ([] : List Befehl) 0 10)[48]? = some (.binaer .add 12) ∧
    (rfindSchleife ([] : List Befehl) 0 10)[49]? = some (.zurueckSprung 49) := by
  constructor
  · rfl
  constructor <;> rfl

/-- The false branch of the zero test (a zero result) jumps from offset 46 to
    offset 49, which is the back edge, not the copy segment starting at offset
    50. The minimisation loop therefore never reaches its end. -/
theorem rfindSchleifeNullsprungZiel : (46 : Nat) + 3 = 49 := rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
