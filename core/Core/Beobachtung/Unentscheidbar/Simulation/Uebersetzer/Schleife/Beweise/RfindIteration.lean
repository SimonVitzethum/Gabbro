module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindExit
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Divergenz
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.PaarKorrekt
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.PaarFrame
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Verschiebung

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The pairing block of the minimisation loop, named so composed runs compare
    the same constant instead of a large expanded expression. -/
@[irreducible] def rfindPaar (frei : Nat) : List Befehl :=
  paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)

/-- The zero test, back edge and copy segment after the translated block. -/
@[irreducible] def rfindRest (cfBlk : List Befehl) (aus frei : Nat) : List Befehl :=
  (rfindNullTest frei ++ rfindRueck cfBlk frei) ++ kopie aus (frei + 2)

/-- The loop as the pairing block, the translated block and the tail. -/
theorem rfindSchleifeAlsAnhang (cfBlk : List Befehl) (aus frei : Nat) :
    rfindSchleife cfBlk aus frei = rfindPaar frei ++ cfBlk ++ rfindRest cfBlk aus frei := by
  simp only [rfindSchleife, rfindPaar, rfindRest, rfindNullTest, rfindRueck, List.append_assoc]

/-- A counter inside the front part of the loop reads the same instruction in the standalone front. -/
theorem rfindSchleifeBeiVorne (cfBlk : List Befehl) (aus frei j : Nat)
    (hj : j < 50 + cfBlk.length) :
    (rfindSchleife cfBlk aus frei)[j]? = (rfindVorne cfBlk frei)[j]? := by
  rw [rfindSchleifeGlied]
  exact List.getElem?_append_left (by rw [rfindVorneLaenge]; omega)

/-- The zero-test segment sits at offset `44 + cfBlk.length`. -/
theorem rfindVorneBeiNulltest (cfBlk : List Befehl) (frei i : Nat) (hi : i < 3) :
    (rfindVorne cfBlk frei)[44 + cfBlk.length + i]? = (rfindNullTest frei)[i]? := by
  unfold rfindVorne
  have hlt : 44 + cfBlk.length + i < (rfindPaarVorne cfBlk frei ++ rfindNullTest frei).length := by
    rw [List.length_append, rfindPaarVorneLaenge, rfindNullTestLaenge]
    omega
  rw [List.getElem?_append_left hlt]
  have hge : (rfindPaarVorne cfBlk frei).length ≤ 44 + cfBlk.length + i := by
    rw [rfindPaarVorneLaenge]
    omega
  rw [List.getElem?_append_right hge]
  rw [rfindPaarVorneLaenge]
  rw [show 44 + cfBlk.length + i - (44 + cfBlk.length) = i by omega]

/-- The back-edge segment sits at offset `47 + cfBlk.length`. -/
theorem rfindVorneBeiRueck (cfBlk : List Befehl) (frei i : Nat) (hi : i < 3) :
    (rfindVorne cfBlk frei)[47 + cfBlk.length + i]? = (rfindRueck cfBlk frei)[i]? := by
  unfold rfindVorne
  have hge : (rfindPaarVorne cfBlk frei ++ rfindNullTest frei).length ≤ 47 + cfBlk.length + i := by
    rw [List.length_append, rfindPaarVorneLaenge, rfindNullTestLaenge]
    omega
  rw [List.getElem?_append_right hge]
  rw [List.length_append, rfindPaarVorneLaenge, rfindNullTestLaenge]
  rw [show 47 + cfBlk.length + i - (44 + cfBlk.length + 3) = i by omega]

/-- The copy segment sits at offset `50 + cfBlk.length`. -/
theorem rfindSchleifeBeiKopie (cfBlk : List Befehl) (aus frei i : Nat) (hi : i < 3) :
    (rfindSchleife cfBlk aus frei)[50 + cfBlk.length + i]? = (kopie aus (frei + 2))[i]? := by
  rw [rfindSchleifeGlied]
  have hge : (rfindVorne cfBlk frei).length ≤ 50 + cfBlk.length + i := by
    rw [rfindVorneLaenge]
    omega
  rw [List.getElem?_append_right hge]
  rw [rfindVorneLaenge]
  rw [show 50 + cfBlk.length + i - (50 + cfBlk.length) = i by omega]

theorem rfindBeiNull0 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[44 + cfBlk.length]? = some (.literal (frei + 5) 0) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (44 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 44 + cfBlk.length = 44 + cfBlk.length + 0 by omega]
  rw [rfindVorneBeiNulltest cfBlk frei 0 (by omega)]
  rfl

theorem rfindBeiNull1 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[45 + cfBlk.length]? = some (.vergleichen .lt (frei + 5)) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (45 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 45 + cfBlk.length = 44 + cfBlk.length + 1 by omega]
  rw [rfindVorneBeiNulltest cfBlk frei 1 (by omega)]
  rfl

theorem rfindBeiNull2 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[46 + cfBlk.length]? = some (.springeWenn (frei + 5) false 4) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (46 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 46 + cfBlk.length = 44 + cfBlk.length + 2 by omega]
  rw [rfindVorneBeiNulltest cfBlk frei 2 (by omega)]
  rfl

theorem rfindBeiRueck0 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[47 + cfBlk.length]? = some (.literal (frei + 3) 1) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (47 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 47 + cfBlk.length = 47 + cfBlk.length + 0 by omega]
  rw [rfindVorneBeiRueck cfBlk frei 0 (by omega)]
  rfl

theorem rfindBeiRueck1 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[48 + cfBlk.length]? = some (.binaer .add (frei + 2)) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (48 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 48 + cfBlk.length = 47 + cfBlk.length + 1 by omega]
  rw [rfindVorneBeiRueck cfBlk frei 1 (by omega)]
  rfl

theorem rfindBeiRueck2 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[49 + cfBlk.length]? = some (.zurueckSprung (49 + cfBlk.length)) := by
  rw [rfindSchleifeBeiVorne cfBlk aus frei (49 + cfBlk.length) (by omega)]
  conv_lhs => rw [show 49 + cfBlk.length = 47 + cfBlk.length + 2 by omega]
  rw [rfindVorneBeiRueck cfBlk frei 2 (by omega)]
  rfl

theorem rfindBeiKopie0 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[50 + cfBlk.length]? = some (.binden nameX (frei + 2)) := by
  conv_lhs => rw [show 50 + cfBlk.length = 50 + cfBlk.length + 0 by omega]
  rw [rfindSchleifeBeiKopie cfBlk aus frei 0 (by omega)]
  rfl

theorem rfindBeiKopie1 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[51 + cfBlk.length]? = some (.lesen aus 0) := by
  conv_lhs => rw [show 51 + cfBlk.length = 50 + cfBlk.length + 1 by omega]
  rw [rfindSchleifeBeiKopie cfBlk aus frei 1 (by omega)]
  rfl

theorem rfindBeiKopie2 (cfBlk : List Befehl) (aus frei : Nat) :
    (rfindSchleife cfBlk aus frei)[52 + cfBlk.length]? = some (.blockEnde 1) := by
  conv_lhs => rw [show 52 + cfBlk.length = 50 + cfBlk.length + 2 by omega]
  rw [rfindSchleifeBeiKopie cfBlk aus frei 2 (by omega)]
  rfl

/-- A positive `cf` value makes the zero test write true, so the conditional falls through. -/
theorem rfindNulltestPosLauf (cfBlk : List Befehl) (aus frei v : Nat) (r : Rahmen)
    (hpc : r.pc = 44 + cfBlk.length)
    (h6 : r.temp (frei + 6) = some (natVal v)) (hv : 0 < v) :
    ∃ r3 : Rahmen,
      (Schritt (rfindSchleife cfBlk aus frei))^[3] (some r) = some r3 ∧
      r3.pc = 47 + cfBlk.length ∧ r3.temp (frei + 5) = some ⟨.bool, true⟩ ∧
      (∀ s, s ≠ frei + 5 → r3.temp s = r.temp s) ∧
      r3.lokale = r.lokale ∧ r3.rueckgabe = r.rueckgabe ∧ r3.stopp = r.stopp := by
  let blk := rfindSchleife cfBlk aus frei
  let r1 : Rahmen := { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 5) (some (natVal 0)) }
  have e1 : Schritt blk (some r) = some r1 := by
    change Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 5) (some (natVal 0)) }
    exact schrittLiteral blk r (44 + cfBlk.length) (frei + 5) 0 hpc (rfindBeiNull0 cfBlk aus frei)
  have hpc1 : r1.pc = 45 + cfBlk.length := by dsimp only [r1]; rw [hpc]; omega
  have h15 : r1.temp (frei + 5) = some (natVal 0) := by dsimp only [r1]; rw [updateHit]
  have h16 : r1.temp (frei + 6) = some (natVal v) := by
    dsimp only [r1]
    rw [updateMiss _ _ _ _ (by omega)]
    exact h6
  let r2 : Rahmen := { r1 with pc := (45 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 5) (some ⟨.bool, true⟩) }
  have e2 : Schritt blk (some r1) = some r2 := by
    change Schritt blk (some r1) = some { r1 with pc := (45 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 5) (some ⟨.bool, true⟩) }
    have h := schrittVergleichNat blk r1 (45 + cfBlk.length) (frei + 5) 0 v hpc1 h15 h16
      (rfindBeiNull1 cfBlk aus frei)
    rw [show Compare.eval .lt ((0 : Nat) : Int) ((v : Nat) : Int) = true by
      exact (vergleichLtNat 0 v).2 hv] at h
    exact h
  have hpc2 : r2.pc = 46 + cfBlk.length := by dsimp only [r2]; omega
  have h25 : r2.temp (frei + 5) = some ⟨.bool, true⟩ := by dsimp only [r2]; rw [updateHit]
  let r3 : Rahmen := { r2 with pc := r2.pc + 1 }
  have e3 : Schritt blk (some r2) = some r3 := by
    change Schritt blk (some r2) = some { r2 with pc := r2.pc + 1 }
    exact schrittSpringeWennFalsch blk r2 (46 + cfBlk.length) (frei + 5) false true 4
      hpc2 h25 (by decide) (rfindBeiNull2 cfBlk aus frei)
  have e1' : (Schritt blk)^[1] (some r) = some r1 := by rw [schrittAlsIterate]; exact e1
  have e2' : (Schritt blk)^[1] (some r1) = some r2 := by rw [schrittAlsIterate]; exact e2
  have e3' : (Schritt blk)^[1] (some r2) = some r3 := by rw [schrittAlsIterate]; exact e3
  have hrun2 : (Schritt blk)^[2] (some r) = some r2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, e1', e2']
  have hrun3 : (Schritt blk)^[3] (some r) = some r3 := by
    rw [show (3 : Nat) = 1 + 2 by omega, Function.iterate_add_apply, hrun2, e3']
  refine ⟨r3, hrun3, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · dsimp only [r3]
    omega
  · exact h25
  · intro s hs
    dsimp only [r3, r2, r1]
    rw [updateMiss _ _ _ _ hs, updateMiss _ _ _ _ hs]

/-- A zero `cf` value makes the conditional jump straight to the copy segment. -/
theorem rfindNulltestNullLauf (cfBlk : List Befehl) (aus frei : Nat) (r : Rahmen)
    (hpc : r.pc = 44 + cfBlk.length)
    (h6 : r.temp (frei + 6) = some (natVal 0)) :
    ∃ r3 : Rahmen,
      (Schritt (rfindSchleife cfBlk aus frei))^[3] (some r) = some r3 ∧
      r3.pc = 50 + cfBlk.length ∧ r3.temp (frei + 5) = some ⟨.bool, false⟩ ∧
      (∀ s, s ≠ frei + 5 → r3.temp s = r.temp s) ∧
      r3.lokale = r.lokale ∧ r3.rueckgabe = r.rueckgabe ∧ r3.stopp = r.stopp := by
  let blk := rfindSchleife cfBlk aus frei
  let r1 : Rahmen := { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 5) (some (natVal 0)) }
  have e1 : Schritt blk (some r) = some r1 := by
    change Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 5) (some (natVal 0)) }
    exact schrittLiteral blk r (44 + cfBlk.length) (frei + 5) 0 hpc (rfindBeiNull0 cfBlk aus frei)
  have hpc1 : r1.pc = 45 + cfBlk.length := by dsimp only [r1]; rw [hpc]; omega
  have h15 : r1.temp (frei + 5) = some (natVal 0) := by dsimp only [r1]; rw [updateHit]
  have h16 : r1.temp (frei + 6) = some (natVal 0) := by
    dsimp only [r1]
    rw [updateMiss _ _ _ _ (by omega)]
    exact h6
  let r2 : Rahmen := { r1 with pc := (45 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 5) (some ⟨.bool, false⟩) }
  have e2 : Schritt blk (some r1) = some r2 := by
    change Schritt blk (some r1) = some { r1 with pc := (45 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 5) (some ⟨.bool, false⟩) }
    have h := schrittVergleichNat blk r1 (45 + cfBlk.length) (frei + 5) 0 0 hpc1 h15 h16
      (rfindBeiNull1 cfBlk aus frei)
    rw [show Compare.eval .lt ((0 : Nat) : Int) ((0 : Nat) : Int) = false by
      simp only [Compare.eval, Nat.cast_lt, decide_eq_false_iff_not]; omega] at h
    exact h
  have hpc2 : r2.pc = 46 + cfBlk.length := by dsimp only [r2]; omega
  have h25 : r2.temp (frei + 5) = some ⟨.bool, false⟩ := by dsimp only [r2]; rw [updateHit]
  let r3 : Rahmen := { r2 with pc := r2.pc + 4 }
  have e3 : Schritt blk (some r2) = some r3 := by
    change Schritt blk (some r2) = some { r2 with pc := r2.pc + 4 }
    exact schrittSpringeWennWahr blk r2 (46 + cfBlk.length) (frei + 5) false false 4
      hpc2 h25 rfl (rfindBeiNull2 cfBlk aus frei)
  have e1' : (Schritt blk)^[1] (some r) = some r1 := by rw [schrittAlsIterate]; exact e1
  have e2' : (Schritt blk)^[1] (some r1) = some r2 := by rw [schrittAlsIterate]; exact e2
  have e3' : (Schritt blk)^[1] (some r2) = some r3 := by rw [schrittAlsIterate]; exact e3
  have hrun2 : (Schritt blk)^[2] (some r) = some r2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, e1', e2']
  have hrun3 : (Schritt blk)^[3] (some r) = some r3 := by
    rw [show (3 : Nat) = 1 + 2 by omega, Function.iterate_add_apply, hrun2, e3']
  refine ⟨r3, hrun3, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · dsimp only [r3]
    omega
  · exact h25
  · intro s hs
    dsimp only [r3, r2, r1]
    rw [updateMiss _ _ _ _ hs, updateMiss _ _ _ _ hs]

/-- The increment and the back edge return to the loop entry with the successor candidate. -/
theorem rfindRueckLauf (cfBlk : List Befehl) (aus frei y : Nat) (r : Rahmen)
    (hpc : r.pc = 47 + cfBlk.length)
    (h2 : r.temp (frei + 2) = some (natVal y)) :
    ∃ r3 : Rahmen,
      (Schritt (rfindSchleife cfBlk aus frei))^[3] (some r) = some r3 ∧
      r3.pc = 0 ∧ r3.temp (frei + 2) = some (natVal (y + 1)) ∧
      (∀ s, s ≠ frei + 2 → s ≠ frei + 3 → r3.temp s = r.temp s) ∧
      r3.lokale = r.lokale ∧ r3.rueckgabe = r.rueckgabe ∧ r3.stopp = r.stopp := by
  let blk := rfindSchleife cfBlk aus frei
  let r1 : Rahmen := { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 3) (some (natVal 1)) }
  have e1 : Schritt blk (some r) = some r1 := by
    change Schritt blk (some r) = some { r with pc := r.pc + 1, temp := Function.update r.temp (frei + 3) (some (natVal 1)) }
    exact schrittLiteral blk r (47 + cfBlk.length) (frei + 3) 1 hpc (rfindBeiRueck0 cfBlk aus frei)
  have hpc1 : r1.pc = 48 + cfBlk.length := by dsimp only [r1]; rw [hpc]; omega
  have h12 : r1.temp (frei + 2) = some (natVal y) := by
    dsimp only [r1]
    rw [updateMiss _ _ _ _ (by omega)]
    exact h2
  have h13 : r1.temp (frei + 3) = some (natVal 1) := by dsimp only [r1]; rw [updateHit]
  let r2 : Rahmen := { r1 with pc := (48 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 2) (some (natVal (y + 1))) }
  have e2 : Schritt blk (some r1) = some r2 := by
    change Schritt blk (some r1) = some { r1 with pc := (48 + cfBlk.length) + 1, temp := Function.update r1.temp (frei + 2) (some (natVal (y + 1))) }
    exact schrittAddNat blk r1 (48 + cfBlk.length) (frei + 2) y 1 hpc1 h12 h13
      (rfindBeiRueck1 cfBlk aus frei)
  have hpc2 : r2.pc = 49 + cfBlk.length := by dsimp only [r2]; omega
  let r3 : Rahmen := { r2 with pc := r2.pc - (49 + cfBlk.length) }
  have e3 : Schritt blk (some r2) = some r3 := by
    change Schritt blk (some r2) = some { r2 with pc := r2.pc - (49 + cfBlk.length) }
    exact schrittZurueck blk r2 (49 + cfBlk.length) (49 + cfBlk.length) hpc2
      (rfindBeiRueck2 cfBlk aus frei)
  have e1' : (Schritt blk)^[1] (some r) = some r1 := by rw [schrittAlsIterate]; exact e1
  have e2' : (Schritt blk)^[1] (some r1) = some r2 := by rw [schrittAlsIterate]; exact e2
  have e3' : (Schritt blk)^[1] (some r2) = some r3 := by rw [schrittAlsIterate]; exact e3
  have hrun2 : (Schritt blk)^[2] (some r) = some r2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, e1', e2']
  have hrun3 : (Schritt blk)^[3] (some r) = some r3 := by
    rw [show (3 : Nat) = 1 + 2 by omega, Function.iterate_add_apply, hrun2, e3']
  refine ⟨r3, hrun3, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · dsimp only [r3]
    rw [hpc2]
    omega
  · dsimp only [r3, r2]
    rw [updateHit]
  · intro s hs2 hs3
    dsimp only [r3, r2, r1]
    rw [updateMiss _ _ _ _ hs2, updateMiss _ _ _ _ hs3]

/-- The copy segment writes the candidate into the output slot and stops at the loop end. -/
theorem rfindKopieLauf (cfBlk : List Befehl) (aus frei y : Nat) (r : Rahmen)
    (hpc : r.pc = 50 + cfBlk.length)
    (h2 : r.temp (frei + 2) = some (natVal y)) :
    ∃ rE : Rahmen,
      (Schritt (rfindSchleife cfBlk aus frei))^[3] (some r) = some rE ∧
      rE.pc = (rfindSchleife cfBlk aus frei).length ∧ rE.temp aus = some (natVal y) ∧
      (∀ s, s ≠ aus → rE.temp s = r.temp s) ∧
      rE.lokale = r.lokale ∧ rE.rueckgabe = r.rueckgabe ∧ rE.stopp = r.stopp := by
  let blk := rfindSchleife cfBlk aus frei
  let r1 : Rahmen := { r with pc := r.pc + 1, lokale := r.temp (frei + 2) :: r.lokale }
  have e1 : Schritt blk (some r) = some r1 := by
    change Schritt blk (some r) = some { r with pc := r.pc + 1, lokale := r.temp (frei + 2) :: r.lokale }
    exact schrittBinden blk r (50 + cfBlk.length) (frei + 2) hpc (rfindBeiKopie0 cfBlk aus frei)
  have hpc1 : r1.pc = 51 + cfBlk.length := by dsimp only [r1]; rw [hpc]; omega
  have hloc : r1.lokale[0]?.join = some (natVal y) := by
    dsimp only [r1]
    rw [h2]
    rfl
  let r2 : Rahmen := { r1 with pc := r1.pc + 1, temp := Function.update r1.temp aus (some (natVal y)) }
  have e2 : Schritt blk (some r1) = some r2 := by
    change Schritt blk (some r1) = some { r1 with pc := r1.pc + 1, temp := Function.update r1.temp aus (some (natVal y)) }
    exact schrittLesen blk r1 (51 + cfBlk.length) aus y hpc1 hloc (rfindBeiKopie1 cfBlk aus frei)
  have hpc2 : r2.pc = 52 + cfBlk.length := by dsimp only [r2, r1]; rw [hpc]; omega
  let r3 : Rahmen := { r2 with pc := r2.pc + 1, lokale := r1.lokale.drop 1 }
  have e3 : Schritt blk (some r2) = some r3 := by
    change Schritt blk (some r2) = some { r2 with pc := r2.pc + 1, lokale := r1.lokale.drop 1 }
    exact schrittBlockEnde blk r2 (52 + cfBlk.length) 1 hpc2 (rfindBeiKopie2 cfBlk aus frei)
  have e1' : (Schritt blk)^[1] (some r) = some r1 := by rw [schrittAlsIterate]; exact e1
  have e2' : (Schritt blk)^[1] (some r1) = some r2 := by rw [schrittAlsIterate]; exact e2
  have e3' : (Schritt blk)^[1] (some r2) = some r3 := by rw [schrittAlsIterate]; exact e3
  have hrun2 : (Schritt blk)^[2] (some r) = some r2 := by
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, e1', e2']
  have hrun3 : (Schritt blk)^[3] (some r) = some r3 := by
    rw [show (3 : Nat) = 1 + 2 by omega, Function.iterate_add_apply, hrun2, e3']
  refine ⟨r3, hrun3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [r3]
    rw [hpc2]
    rw [rfindSchleifeLaenge]
    omega
  · dsimp only [r3, r2]
    rw [updateHit]
  · intro s hs
    simp [r3, r2, r1, updateMiss, hs]
  · simp [r3, r1]
  · simp [r3, r2, r1]
  · simp [r3, r2, r1]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
