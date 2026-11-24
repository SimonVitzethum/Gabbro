module

public import Core.Beobachtung.Unentscheidbar.Simulation.Programm

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The translator. The two base codes are compiled faithfully; the remaining
    constructors currently emit the constant-zero program. They are listed
    explicitly so the missing cases are visible and so the map is total. -/
def programm : Nat.Partrec.Code → List Befehl
  | .zero => progZahl 0
  | .succ => progSucc
  | .left => progZahl 0
  | .right => progZahl 0
  | .pair _ _ => progZahl 0
  | .comp _ _ => progZahl 0
  | .prec _ _ => progZahl 0
  | .rfind' _ => progZahl 0

theorem treue_zero (n a : Nat) :
    (Nat.Partrec.Code.eval .zero n = Part.some a ↔
      HaeltMit (programm .zero) (startVon n) a) := by
  change Part.some 0 = Part.some a ↔ HaeltMit (progZahl 0) (startVon n) a
  constructor
  · intro h
    exact (haeltMit_progZahl_iff 0 n a).mpr (Part.some_injective h).symm
  · intro h
    exact congrArg Part.some ((haeltMit_progZahl_iff 0 n a).mp h).symm

theorem treue_succ (n a : Nat) :
    (Nat.Partrec.Code.eval .succ n = Part.some a ↔
      HaeltMit (programm .succ) (startVon n) a) := by
  change Part.some (n + 1) = Part.some a ↔ HaeltMit progSucc (startVon n) a
  constructor
  · intro h
    exact (haeltMit_progSucc_iff n a).mpr (Part.some_injective h).symm
  · intro h
    exact congrArg Part.some ((haeltMit_progSucc_iff n a).mp h).symm

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
