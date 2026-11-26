module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

def precAddWert (s : Nat) : Dynamisch :=
  Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (s : Int)) (Zahl.literal (1 : Int))⟩

/-- The increment and back edge of one recursion iteration: add one to the
    counter and jump back to the check. -/
theorem precEndeLauf (cgBlk : List Befehl) (frei s : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hs : r.temp (frei + 2) = some (natVal s)) :
    ∃ r', (Schritt (precEnde cgBlk frei))^[3] (some r) = some r' ∧
      r'.pc = 0 ∧ r'.temp (frei + 2) = some (natVal (s + 1)) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  have g0 : (precEnde cgBlk frei)[0]? = some (.literal (frei + 3) 1) := by rfl
  have g1 : (precEnde cgBlk frei)[1]? = some (.binaer .add (frei + 2)) := by rfl
  have g2 : (precEnde cgBlk frei)[2]? = some (.zurueckSprung (cgBlk.length + 98)) := by rfl
  have e0 := schrittLiteral (precEnde cgBlk frei) r 0 (frei + 3) 1 hpc g0
  let r1 : Rahmen := r.schreibe (frei + 3) (some (natVal 1))
  have er1 : (Schritt (precEnde cgBlk frei))^[1] (some r) = some r1 := by
    simpa only [r1, Rahmen.schreibe, Function.iterate_one] using e0
  have hr1s : r1.temp (frei + 2) = some (natVal s) := by
    show Function.update r.temp (frei + 3) (some (natVal 1)) (frei + 2) = _
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 3))]
    exact hs
  have hr1e : r1.temp (frei + 3) = some (natVal 1) := by
    simp only [r1, Rahmen.schreibe, updateHit]
  have ha : r1.zahl (frei + 2) = some ⟨(s : Int), (s : Int), Zahl.literal (s : Int)⟩ :=
    zahlOfNat _ _ _ hr1s
  have hb : r1.zahl (frei + 3) = some ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ :=
    zahlOfNat _ _ _ hr1e
  have hpc1 : r1.pc = 1 := by
    simp only [r1, Rahmen.schreibe, hpc, Nat.zero_add]
  have e1 := schrittBinaer (precEnde cgBlk frei) r1 1 (frei + 2) .add
    ⟨(s : Int), (s : Int), Zahl.literal (s : Int)⟩
    ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ hpc1 ha hb g1
  let r2 : Rahmen := r1.schreibe (frei + 2) (some (precAddWert s))
  have er2 : (Schritt (precEnde cgBlk frei))^[1] (some r1) = some r2 := by
    simpa only [r2, Rahmen.schreibe, precAddWert, Function.iterate_one,
      Zahl.literal, Arith.auswerten] using e1
  have hpc2 : r2.pc = 2 := by
    simp only [r2, Rahmen.schreibe, hpc1]
  have e2 := schrittZurueck (precEnde cgBlk frei) r2 2 (cgBlk.length + 98) hpc2 g2
  let r3 : Rahmen := { r2 with pc := r2.pc - (cgBlk.length + 98) }
  have er3 : (Schritt (precEnde cgBlk frei))^[1] (some r2) = some r3 := by
    simpa only [r3, Function.iterate_one] using e2
  refine ⟨r3, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have ec : (Schritt (precEnde cgBlk frei))^[3] (some r) =
        (Schritt (precEnde cgBlk frei))^[1]
          ((Schritt (precEnde cgBlk frei))^[1]
            ((Schritt (precEnde cgBlk frei))^[1] (some r))) := by
      rfl
    rw [ec, er1, er2, er3]
  · show r2.pc - (cgBlk.length + 98) = 0
    rw [hpc2]
    omega
  · change (Function.update r1.temp (frei + 2) (some (precAddWert s))) (frei + 2) =
      some (natVal (s + 1))
    rw [updateHit]
    change some (precAddWert s) = some (natVal (s + 1))
    congr 1

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
