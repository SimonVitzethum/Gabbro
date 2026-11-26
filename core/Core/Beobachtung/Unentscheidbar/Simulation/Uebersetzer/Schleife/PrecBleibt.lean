module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The primitive-recursion body stays inside itself. The two pairing segments
    are discharged by their concrete block lemma; the step block is discharged
    by the induction hypothesis `BleibtImBlock cgBlk`, shifted by the pairing
    prefix. Relocatability of the step block is the companion induction
    hypothesis and is needed only to align the shifted evaluation. -/
theorem bleibtImBlockPrecRumpf (cgBlk : List Befehl) (aus frei : Nat)
    (hcg : BleibtImBlock cgBlk) (hvCg : VerschiebbaresProgramm cgBlk) :
    BleibtImBlock (precRumpf cgBlk aus frei) := by
  rw [precRumpf]
  apply bleibtImBlockAppend
  · apply bleibtImBlockAppend
    · exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
    · exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
    · exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  · rw [← verschiebbarVonNull]
    exact verschiebbarPrecRumpf 0 cgBlk aus frei hvCg
  · exact hcg

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
