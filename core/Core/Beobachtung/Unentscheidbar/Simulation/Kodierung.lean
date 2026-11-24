module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The canonical start frame places the input as an exact integer in slot zero.
    All bound maps keep their default `none`, so the frame is open. -/
def startVon (n : ℕ) : Rahmen :=
  { pc := 0
    temp := fun slot => if slot = 0 then some ⟨.int (n : Int) (n : Int), Zahl.literal (n : Int)⟩ else none
    lokale := []
    rueckgabe := none }

theorem start_offen (n : ℕ) : OffenesFragment (startVon n) := by
  intro slot
  rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
