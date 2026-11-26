module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The zero-test segment of the minimisation loop, on its own so its length and
    instruction positions can be named without recomputing the surrounding
    concatenations. -/
def rfindNullTest (frei : Nat) : List Befehl :=
  [.literal (frei + 5) 0, .vergleichen .lt (frei + 5),
    .springeWenn (frei + 5) false 4]

theorem rfindNullTestLaenge (frei : Nat) : (rfindNullTest frei).length = 3 := by
  rfl

/-- The back-edge segment of the minimisation loop. -/
def rfindRueck (cfBlk : List Befehl) (frei : Nat) : List Befehl :=
  [.literal (frei + 3) 1, .binaer .add (frei + 2),
    .zurueckSprung (49 + cfBlk.length)]

theorem rfindRueckLaenge (cfBlk : List Befehl) (frei : Nat) :
    (rfindRueck cfBlk frei).length = 3 := by
  rfl

/-- The pairing block followed by the translated block. -/
def rfindPaarVorne (cfBlk : List Befehl) (frei : Nat) : List Befehl :=
  paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10) ++ cfBlk

theorem rfindPaarVorneLaenge (cfBlk : List Befehl) (frei : Nat) :
    (rfindPaarVorne cfBlk frei).length = 44 + cfBlk.length := by
  simp only [rfindPaarVorne, List.length_append, paarBerechnungLaenge]

/-- Everything before the copy segment. -/
def rfindVorne (cfBlk : List Befehl) (frei : Nat) : List Befehl :=
  (rfindPaarVorne cfBlk frei ++ rfindNullTest frei) ++ rfindRueck cfBlk frei

theorem rfindVorneLaenge (cfBlk : List Befehl) (frei : Nat) :
    (rfindVorne cfBlk frei).length = 50 + cfBlk.length := by
  simp only [rfindVorne, List.length_append, rfindNullTestLaenge, rfindRueckLaenge,
    rfindPaarVorneLaenge]
  omega

/-- The loop is the part before the copy followed by the copy. -/
theorem rfindSchleifeGlied (cfBlk : List Befehl) (aus frei : Nat) :
    rfindSchleife cfBlk aus frei = rfindVorne cfBlk frei ++ kopie aus (frei + 2) := by
  simp only [rfindSchleife, rfindVorne, rfindPaarVorne, rfindNullTest, rfindRueck]

/-- The length of the minimisation loop. -/
theorem rfindSchleifeLaenge (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei).length = 53 + cfBlk.length := by
  rw [rfindSchleifeGlied]
  simp only [List.length_append, rfindVorneLaenge, kopieLaenge]
  omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
