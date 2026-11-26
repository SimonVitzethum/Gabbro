module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

example : (rfindSchleife ([] : List Befehl) 0 10).length = 53 := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[44]? = some (.literal 15 0) := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[45]? = some (.vergleichen .lt 15) := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[46]? = some (.springeWenn 15 false 3) := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[47]? = some (.literal 17 1) := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[48]? = some (.binaer .add 12) := by rfl

example : (rfindSchleife ([] : List Befehl) 0 10)[49]? = some (.zurueckSprung 49) := by rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
