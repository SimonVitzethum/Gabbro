module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarSegmenteF

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

theorem pbPrefixLauf (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a))
    (hb : r.temp bSlot = some (natVal b))
    (haF : aSlot < frei) (hbF : bSlot < frei) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[13] (some r) = some (pb5 r a b frei) := by
  have haf : aSlot ≠ frei := by omega
  have haf1 : aSlot ≠ frei + 1 := by omega
  have hbf : bSlot ≠ frei := by omega
  have hbf1 : bSlot ≠ frei + 1 := by omega
  have hbf2 : bSlot ≠ frei + 2 := by omega
  have h1 := pb1Lauf aSlot bSlot aus frei r a hpc ha
  have h2 := pb2Lauf aSlot bSlot aus frei r a b ha hb hbf
  have h3 := pb3Lauf aSlot bSlot aus frei r a b ha hb haf haf1
  have h4 := pb4Lauf aSlot bSlot aus frei r a b hb hbf hbf1 hbf2
  have h5 := pb5Lauf aSlot bSlot aus frei r a b
  have h12 := kettenSchritt _ r (pb1 r a frei) (pb2 r a b frei) 3 3 h1 h2
  have h123 := kettenSchritt _ r (pb2 r a b frei) (pb3 r a b frei) 6 3 h12 h3
  have h1234 := kettenSchritt _ r (pb3 r a b frei) (pb4 r a b frei) 9 3 h123 h4
  exact kettenEinSchritt _ r (pb4 r a b frei) (pb5 r a b frei) 12 h1234 h5

theorem paarVorwaertsWahr (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a))
    (hb : r.temp bSlot = some (natVal b))
    (haF : aSlot < frei) (hbF : bSlot < frei) (hab : a < b) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[28] (some r) = some (pb12w r a b aus frei) := by
  have h5 := pbPrefixLauf aSlot bSlot aus frei r a b hpc ha hb haF hbF
  have h6 := pb6wLauf aSlot bSlot aus frei r a b hab
  have h7 := pb7wLauf aSlot bSlot aus frei r a b
  have h8 := pb8wLauf aSlot bSlot aus frei r a b
  have h9 := pb9wLauf aSlot bSlot aus frei r a b
  have h10 := pb10wLauf aSlot bSlot aus frei r a b (by omega) (by omega)
  have h11 := pb11wLauf aSlot bSlot aus frei r a b
  have h12 := pb12wLauf aSlot bSlot aus frei r a b (by omega)
  have h14 := kettenEinSchritt _ r (pb5 r a b frei) (pb6w r a b frei) 13 h5 h6
  have h17 := kettenSchritt _ r (pb6w r a b frei) (pb7w r a b frei) 14 3 h14 h7
  have h20 := kettenSchritt _ r (pb7w r a b frei) (pb8w r a b frei) 17 3 h17 h8
  have h21 := kettenEinSchritt _ r (pb8w r a b frei) (pb9w r a b frei) 20 h20 h9
  have h24 := kettenSchritt _ r (pb9w r a b frei) (pb10w r a b frei) 21 3 h21 h10
  have h25 := kettenEinSchritt _ r (pb10w r a b frei) (pb11w r a b frei) 24 h24 h11
  exact kettenSchritt _ r (pb11w r a b frei) (pb12w r a b aus frei) 25 3 h25 h12

theorem paarVorwaertsFalsch (aSlot bSlot aus frei : Nat) (r : Rahmen) (a b : Nat)
    (hpc : r.pc = 0) (ha : r.temp aSlot = some (natVal a))
    (hb : r.temp bSlot = some (natVal b))
    (haF : aSlot < frei) (hbF : bSlot < frei) (hab : ¬ a < b) :
    (Schritt (paarBerechnung aSlot bSlot aus frei))^[30] (some r) = some (pb14f r a b aus frei) := by
  have h5 := pbPrefixLauf aSlot bSlot aus frei r a b hpc ha hb haF hbF
  have h6 := pb6fLauf aSlot bSlot aus frei r a b hab
  have h7 := pb7fLauf aSlot bSlot aus frei r a b
  have h8 := pb8fLauf aSlot bSlot aus frei r a b
  have h9 := pb9fLauf aSlot bSlot aus frei r a b
  have h10 := pb10fLauf aSlot bSlot aus frei r a b
  have h11 := pb11fLauf aSlot bSlot aus frei r a b
  have h12 := pb12fLauf aSlot bSlot aus frei r a b
  have h13 := pb13fLauf aSlot bSlot aus frei r a b
  have h14 := pb14fLauf aSlot bSlot aus frei r a b
  have h14' := kettenEinSchritt _ r (pb5 r a b frei) (pb6f r a b frei) 13 h5 h6
  have h17 := kettenSchritt _ r (pb6f r a b frei) (pb7f r a b frei) 14 3 h14' h7
  have h20 := kettenSchritt _ r (pb7f r a b frei) (pb8f r a b frei) 17 3 h17 h8
  have h21 := kettenEinSchritt _ r (pb8f r a b frei) (pb9f r a b frei) 20 h20 h9
  have h22 := kettenEinSchritt _ r (pb9f r a b frei) (pb10f r a b frei) 21 h21 h10
  have h25 := kettenSchritt _ r (pb10f r a b frei) (pb11f r a b frei) 22 3 h22 h11
  have h26 := kettenEinSchritt _ r (pb11f r a b frei) (pb12f r a b frei) 25 h25 h12
  have h29 := kettenSchritt _ r (pb12f r a b frei) (pb13f r a b aus frei) 26 3 h26 h13
  exact kettenEinSchritt _ r (pb13f r a b aus frei) (pb14f r a b aus frei) 29 h29 h14

theorem pb12wPres (r : Rahmen) (a b aus frei s : Nat) (hs : s < frei) (hne : s ≠ aus) :
    (pb12w r a b aus frei).temp s = r.temp s := by
  have h0 : s ≠ frei := ltNeAdd hs
  have h1 : s ≠ frei + 1 := ltNeAdd hs
  have h2 : s ≠ frei + 2 := ltNeAdd hs
  have h3 : s ≠ frei + 3 := ltNeAdd hs
  have h4 : s ≠ frei + 4 := ltNeAdd hs
  have h5 : s ≠ frei + 5 := ltNeAdd hs
  show Function.update (pb11w r a b frei).temp aus (some (natVal (b * b + a))) s = _
  rw [updateMiss _ _ _ _ hne]
  show Function.update (pb10w r a b frei).temp (frei + 4) (some (natVal (b * b + a))) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb9w r a b frei).temp (frei + 5) (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h5]
  show Function.update (pb8w r a b frei).temp (frei + 4) (some (natVal (b * b))) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb7w r a b frei).temp (frei + 5) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h5]
  show Function.update (pb6w r a b frei).temp (frei + 4) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) s = _
  rw [updateMiss _ _ _ _ h0]
  show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h3]
  show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h2]
  show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h1]
  show Function.update r.temp frei (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h0]

theorem pb14fPres (r : Rahmen) (a b aus frei s : Nat) (hs : s < frei) (hne : s ≠ aus) :
    (pb14f r a b aus frei).temp s = r.temp s := by
  have h0 : s ≠ frei := ltNeAdd hs
  have h1 : s ≠ frei + 1 := ltNeAdd hs
  have h2 : s ≠ frei + 2 := ltNeAdd hs
  have h3 : s ≠ frei + 3 := ltNeAdd hs
  have h4 : s ≠ frei + 4 := ltNeAdd hs
  have h5 : s ≠ frei + 5 := ltNeAdd hs
  show (pb13f r a b aus frei).temp s = _
  show Function.update (pb12f r a b frei).temp aus (some (natVal (a * a + a + b))) s = _
  rw [updateMiss _ _ _ _ hne]
  show Function.update (pb11f r a b frei).temp (frei + 4) (some (natVal (a * a + a + b))) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb10f r a b frei).temp (frei + 5) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h5]
  show Function.update (pb9f r a b frei).temp (frei + 4) (some (natVal (a * a + a))) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb8f r a b frei).temp (frei + 4) (some (natVal (a * a))) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb7f r a b frei).temp (frei + 5) (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h5]
  show Function.update (pb6f r a b frei).temp (frei + 4) (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h4]
  show Function.update (pb4 r a b frei).temp frei (some ⟨.bool, Compare.eval .lt (a : Int) (b : Int)⟩) s = _
  rw [updateMiss _ _ _ _ h0]
  show Function.update (pb3 r a b frei).temp (frei + 3) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h3]
  show Function.update (pb2 r a b frei).temp (frei + 2) (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h2]
  show Function.update (pb1 r a frei).temp (frei + 1) (some (natVal b)) s = _
  rw [updateMiss _ _ _ _ h1]
  show Function.update r.temp frei (some (natVal a)) s = _
  rw [updateMiss _ _ _ _ h0]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
