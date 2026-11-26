module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindIterationRun
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindEval

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The exit copy, with explicit preservation of every slot but the output. -/
theorem rfindKopieLaufPres (cfBlk : List Befehl) (aus frei y : Nat) (r : Rahmen)
    (hpc : r.pc = 50 + cfBlk.length)
    (h2 : r.temp (frei + 2) = some (natVal y)) :
    ∃ rE : Rahmen,
      (Schritt (rfindSchleife cfBlk aus frei))^[3] (some r) = some rE ∧
      rE.pc = (rfindSchleife cfBlk aus frei).length ∧
      rE.temp aus = some (natVal y) ∧
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
    change Schritt blk (some r1) = some { r1 with pc := r1.pc + 1,
      temp := Function.update r1.temp aus (some (natVal y)) }
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
    dsimp only [r3, r2, r1]
    rw [updateMiss r1.temp s aus (some (natVal y)) hs]
    rfl
  · dsimp only [r3, r1]
    simp only [List.drop_cons]
  · dsimp only [r3, r2]
    rfl
  · dsimp only [r3, r2]
    rfl

/-- One non-exiting iteration, also preserving the low slots. -/
theorem rfindWeiterIterPres (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf : Nat) (m0 y : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (ha : r.temp (frei + 0) = some (natVal a))
    (hm : r.temp (frei + 1) = some (natVal m0))
    (hy : r.temp (frei + 2) = some (natVal y))
    (hcfBlk : BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf)
    (hvBlk : VerschiebbaresProgramm cfBlk)
    (hvEval : ∃ v, Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v)
    (hnz : Nat.Partrec.Code.eval cf (Nat.pair a y) ≠ Part.some 0) :
    ∃ k r1, 0 < k ∧
      (Schritt (rfindSchleife cfBlk aus frei))^[k] (some r) = some r1 ∧
      r1.pc = 0 ∧
      r1.temp (frei + 0) = some (natVal a) ∧
      r1.temp (frei + 1) = some (natVal m0) ∧
      r1.temp (frei + 2) = some (natVal (y + 1)) ∧
      r1.lokale = r.lokale ∧ r1.rueckgabe = r.rueckgabe ∧ r1.stopp = r.stopp ∧
      (∀ s, s < frei → s ≠ aus → r1.temp s = r.temp s) := by
  obtain ⟨k, r1, hkpos, hrun, hpc1, ha1, hm1, hy1, hlok1, hrueck1, hstopp1⟩ :=
    rfindWeiterIter cfBlk cf a aus frei freiCf m0 y r hpc ha hm hy hcfBlk hvBlk hvEval hnz
  have h4Lt : frei + 4 < freiCf := hcfBlk.1
  obtain ⟨kp, rp, hrunP, hpcP, h4P, hpresP, hlokP, hrueckP, hstoppP⟩ :=
    paarVorwaerts (frei + 0) (frei + 2) (frei + 4) (frei + 10) r a y
      hpc ha hy (by omega) (by omega)
  rcases hcfBlk with ⟨_, _, _, hcfNr⟩
  obtain ⟨v, hv⟩ := hvEval
  obtain ⟨kcf, rc, hrunC, hpcC, h6C, hpresC, hlokC, hrueckC, hstoppC⟩ :=
    (hcfNr (Nat.pair a y) { rp with pc := 0 } rfl (by
      change rp.temp (frei + 4) = some (natVal (Nat.pair a y))
      exact h4P)).1 v hv
  have hvpos : 0 < v := by
    by_contra h
    have : v = 0 := by omega
    subst v
    exact hnz hv
  obtain ⟨rN, hrunN, hpcN, hNbool, hNpres, hlokN, hrueckN, hstoppN⟩ :=
    rfindNulltestPosLauf cfBlk aus frei v (mitPc 44 rc) (by
      simp only [mitPc]
      rw [hpcC]
      omega) (by simp only [mitPc]; exact h6C) hvpos
  have hN2 : rN.temp (frei + 2) = some (natVal y) := by
    rw [hNpres (frei + 2) (by omega)]
    simp only [mitPc]
    change rc.temp (frei + 2) = _
    rw [hpresC (frei + 2) (by omega) (by omega)]
    change rp.temp (frei + 2) = _
    rw [hpresP (frei + 2) (by omega) (by omega)]
    exact hy
  obtain ⟨rR, hrunR, hpcR, hR2, hRpres, hlokR, hrueckR, hstoppR⟩ :=
    rfindRueckLauf cfBlk aus frei y rN (by rw [hpcN]) hN2
  have hEq : r1 = rR := by
    have hrunRef : (Schritt (rfindSchleife cfBlk aus frei))^[(6 + kcf) + kp] (some r) = some rR := by
      have hpcPaarEnde : rp.pc = (rfindPaar frei).length := by
        rw [hpcP, rfindPaar, paarBerechnungLaenge]
      rw [← rfindPaar] at hrunP
      have hbleibP := laufBleibtVorEnde (rfindPaar frei) r kp rp hrunP hpcPaarEnde
      have hrunPAll : (Schritt (rfindSchleife cfBlk aus frei))^[kp] (some r) = some rp := by
        rw [rfindSchleifeAlsAnhang]
        have hh := (laufAnhang (rfindPaar frei) (cfBlk ++ rfindRest cfBlk aus frei) r kp hbleibP).trans hrunP
        simpa only [List.append_assoc] using hh
      have hbleibC := laufBleibtVorEnde cfBlk { rp with pc := 0 } kcf rc hrunC (by rw [hpcC])
      have hshift := laufMitPc (rfindPaar frei) cfBlk (rfindRest cfBlk aus frei) hvBlk
        { rp with pc := 0 } kcf hbleibC
      have hpaarLen : (rfindPaar frei).length = 44 := by rw [rfindPaar, paarBerechnungLaenge]
      rw [hpaarLen, hrunC] at hshift
      have hrunCAll : (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) = some (mitPc 44 rc) := by
        change (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) =
          some (mitPc (rfindPaar frei).length rc)
        rw [← show { rp with pc := 0 } = { rp with pc := 0 } by rfl]
        rw [rfindSchleifeAlsAnhang]
        exact hshift
      have htail : (Schritt (rfindSchleife cfBlk aus frei))^[6] (some (mitPc 44 rc)) = some rR := by
        rw [show (6 : Nat) = 3 + 3 by omega, Function.iterate_add_apply, hrunN, hrunR]
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hrunPAll, hrunCAll, htail]
    have hkEq : (6 + kcf) + kp = k := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r ((6 + kcf) + kp) k rR r1 hrunRef (by rw [hpcR]) hrun hlt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r k ((6 + kcf) + kp) r1 rR hrun hpc1 hrunRef hgt
    subst k
    exact Option.some.inj (hrun.symm.trans hrunRef)
  refine ⟨k, r1, hkpos, hrun, hpc1, ha1, hm1, hy1, hlok1, hrueck1, hstopp1, ?_⟩
  intro s hsl hsaus
  rw [hEq]
  rw [hRpres s (by omega) (by omega)]
  rw [hNpres s (by omega)]
  simp only [mitPc]
  change rc.temp s = r.temp s
  rw [hpresC s (by omega) (by omega)]
  change rp.temp s = r.temp s
  rw [hpresP s (by omega) (by omega)]

/-- One exiting iteration, also preserving the low slots. -/
theorem rfindExitIterPres (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf : Nat) (m0 y : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (ha : r.temp (frei + 0) = some (natVal a))
    (hm : r.temp (frei + 1) = some (natVal m0))
    (hy : r.temp (frei + 2) = some (natVal y))
    (hcfBlk : BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf)
    (hvBlk : VerschiebbaresProgramm cfBlk)
    (hzero : Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some 0) :
    ∃ k rE,
      (Schritt (rfindSchleife cfBlk aus frei))^[k] (some r) = some rE ∧
      rE.pc = (rfindSchleife cfBlk aus frei).length ∧
      rE.temp aus = some (natVal y) ∧
      (∀ s, s < frei → s ≠ aus → rE.temp s = r.temp s) ∧
      rE.lokale = r.lokale ∧ rE.rueckgabe = r.rueckgabe ∧ rE.stopp = r.stopp := by
  obtain ⟨k, rE, hrun, hpcE, haus⟩ :=
    rfindExitIter cfBlk cf a aus frei freiCf m0 y r hpc ha hm hy hcfBlk hvBlk hzero
  have h4Lt : frei + 4 < freiCf := hcfBlk.1
  obtain ⟨kp, rp, hrunP, hpcP, h4P, hpresP, hlokP, hrueckP, hstoppP⟩ :=
    paarVorwaerts (frei + 0) (frei + 2) (frei + 4) (frei + 10) r a y
      hpc ha hy (by omega) (by omega)
  rcases hcfBlk with ⟨_, _, _, hcfNr⟩
  obtain ⟨kcf, rc, hrunC, hpcC, h6C, hpresC, hlokC, hrueckC, hstoppC⟩ :=
    (hcfNr (Nat.pair a y) { rp with pc := 0 } rfl (by
      change rp.temp (frei + 4) = some (natVal (Nat.pair a y))
      exact h4P)).1 0 hzero
  obtain ⟨rN, hrunN, hpcN, hNbool, hNpres, hlokN, hrueckN, hstoppN⟩ :=
    rfindNulltestNullLauf cfBlk aus frei (mitPc 44 rc) (by
      simp only [mitPc]
      rw [hpcC]
      omega) (by simp only [mitPc]; exact h6C)
  have hN2 : rN.temp (frei + 2) = some (natVal y) := by
    rw [hNpres (frei + 2) (by omega)]
    simp only [mitPc]
    change rc.temp (frei + 2) = _
    rw [hpresC (frei + 2) (by omega) (by omega)]
    change rp.temp (frei + 2) = _
    rw [hpresP (frei + 2) (by omega) (by omega)]
    exact hy
  obtain ⟨rK, hrunK, hpcK, hausK, hpresK, hlokK, hrueckK, hstoppK⟩ :=
    rfindKopieLaufPres cfBlk aus frei y rN (by rw [hpcN]) hN2
  have hEq : rE = rK := by
    have hpcPaarEnde : rp.pc = (rfindPaar frei).length := by
      rw [hpcP, rfindPaar, paarBerechnungLaenge]
    rw [← rfindPaar] at hrunP
    have hbleibP := laufBleibtVorEnde (rfindPaar frei) r kp rp hrunP hpcPaarEnde
    have hrunPAll : (Schritt (rfindSchleife cfBlk aus frei))^[kp] (some r) = some rp := by
      rw [rfindSchleifeAlsAnhang]
      have hh := (laufAnhang (rfindPaar frei) (cfBlk ++ rfindRest cfBlk aus frei) r kp hbleibP).trans hrunP
      simpa only [List.append_assoc] using hh
    have hbleibC := laufBleibtVorEnde cfBlk { rp with pc := 0 } kcf rc hrunC (by rw [hpcC])
    have hshift := laufMitPc (rfindPaar frei) cfBlk (rfindRest cfBlk aus frei) hvBlk
      { rp with pc := 0 } kcf hbleibC
    have hpaarLen : (rfindPaar frei).length = 44 := by rw [rfindPaar, paarBerechnungLaenge]
    rw [hpaarLen, hrunC] at hshift
    have hrunCAll : (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) = some (mitPc 44 rc) := by
      change (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) =
        some (mitPc (rfindPaar frei).length rc)
      rw [rfindSchleifeAlsAnhang]
      exact hshift
    have htail : (Schritt (rfindSchleife cfBlk aus frei))^[6] (some (mitPc 44 rc)) = some rK := by
      rw [show (6 : Nat) = 3 + 3 by omega, Function.iterate_add_apply, hrunN, hrunK]
    have hrunRef : (Schritt (rfindSchleife cfBlk aus frei))^[(6 + kcf) + kp] (some r) = some rK := by
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hrunPAll, hrunCAll, htail]
    have hkEq : (6 + kcf) + kp = k := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r ((6 + kcf) + kp) k rK rE hrunRef hpcK hrun hlt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r k ((6 + kcf) + kp) rE rK hrun hpcE hrunRef hgt
    subst k
    exact Option.some.inj (hrun.symm.trans hrunRef)
  refine ⟨k, rE, hrun, hpcE, haus, ?_, ?_, ?_, ?_⟩
  · intro s hsl hsaus
    rw [hEq]
    rw [hpresK s hsaus]
    simp only [mitPc]
    change rc.temp s = r.temp s
    rw [hpresC s (by omega) (by omega)]
    change rp.temp s = r.temp s
    rw [hpresP s (by omega) (by omega)]
  · rw [hEq]
    rw [hlokK]
    simp only [mitPc]
    change rc.lokale = r.lokale
    rw [hlokC]
    change rp.lokale = r.lokale
    exact hlokP
  · rw [hEq]
    rw [hrueckK]
    simp only [mitPc]
    change rc.rueckgabe = r.rueckgabe
    rw [hrueckC]
    change rp.rueckgabe = r.rueckgabe
    exact hrueckP
  · rw [hEq]
    rw [hstoppK]
    simp only [mitPc]
    change rc.stopp = r.stopp
    rw [hstoppC]
    change rp.stopp = r.stopp
    exact hstoppP

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
