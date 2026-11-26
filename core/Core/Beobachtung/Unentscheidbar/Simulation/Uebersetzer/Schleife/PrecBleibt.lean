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
  let paar1 := paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  let paar2 := paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have h1 : BleibtImBlock paar1 := by
    dsimp only [paar1]
    exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  have h2 : BleibtImBlock paar2 := by
    dsimp only [paar2]
    exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hv2 : VerschiebbaresProgramm paar2 := by
    dsimp only [paar2]
    exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have h12 : BleibtImBlock (paar1 ++ paar2) :=
    bleibtImBlockAppend paar1 paar2 h1 hv2 h2
  have hres : BleibtImBlock ((paar1 ++ paar2) ++ cgBlk) :=
    bleibtImBlockAppend (paar1 ++ paar2) cgBlk h12 hvCg hcg
  simpa only [precRumpf, paar1, paar2] using hres

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
