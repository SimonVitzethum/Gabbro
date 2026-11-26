module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindIteration

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- One iteration that does not exit: the pairing block, the translated block,
    the false zero test and the back edge bring the counter back to zero with
    the successor candidate. -/
theorem rfindWeiterIter (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
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
      r1.lokale = r.lokale ∧ r1.rueckgabe = r.rueckgabe ∧ r1.stopp = r.stopp := by
  have h4Lt : frei + 4 < freiCf := hcfBlk.1
  obtain ⟨kp, rp, hrunP, hpcP, h4P, hpresP, hlokP, hrueckP, hstoppP⟩ :=
    paarVorwaerts (frei + 0) (frei + 2) (frei + 4) (frei + 10) r a y
      hpc ha hy (by omega) (by omega)
  have hpcPaarEnde : rp.pc = (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)).length := by
    rw [hpcP, paarBerechnungLaenge]
  have hbleibP := laufBleibtVorEnde (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) r kp rp hpcPaarEnde
  have hrunPAll : (Schritt (rfindSchleife cfBlk aus frei))^[kp] (some r) = some rp := by
    rw [rfindSchleifeAlsAnhang]
    exact (laufAnhang (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) _ r kp hbleibP).trans hrunP
  let r0 : Rahmen := { rp with pc := 0 }
  have hmit0 : mitPc 44 r0 = rp := by
    change { rp with pc := 44 + 0 } = rp
    rw [show (44 : Nat) + 0 = rp.pc by rw [hpcP]]
  have h04 : r0.temp (frei + 4) = some (natVal (Nat.pair a y)) := by
    change rp.temp (frei + 4) = _
    exact h4P
  rcases hcfBlk with ⟨_, _, _, hcfNr⟩
  obtain ⟨v, hv⟩ := hvEval
  obtain ⟨kcf, rc, hrunC, hpcC, h6C, hpresC, hlokC, hrueckC, hstoppC⟩ :=
    (hcfNr (Nat.pair a y) r0 rfl h04).1 v hv
  have hpcCEnde : rc.pc = cfBlk.length := by rw [hpcC]
  have hbleibC := laufBleibtVorEnde cfBlk r0 kcf rc hpcCEnde
  have hshift := laufMitPc (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) cfBlk ((rfindNullTest frei ++ rfindRueck cfBlk frei) ++
    kopie aus (frei + 2)) hvBlk r0 kcf hbleibC
  rw [paarBerechnungLaenge, hrunC] at hshift
  have hrunCAll : (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) = some (mitPc 44 rc) := by
    rw [← hmit0]
    rw [rfindSchleifeAlsAnhang]
    exact hshift
  have hrunBis : (Schritt (rfindSchleife cfBlk aus frei))^[kcf + kp] (some r) = some (mitPc 44 rc) := by
    rw [Function.iterate_add_apply, hrunPAll, hrunCAll]
  have hvpos : 0 < v := by
    by_contra h
    have : v = 0 := by omega
    subst v
    exact hnz hv
  have hstartpc : (mitPc 44 rc).pc = 44 + cfBlk.length := by
    simp only [mitPc]
    rw [hpcC]
  have hstart6 : (mitPc 44 rc).temp (frei + 6) = some (natVal v) := by
    simp only [mitPc]
    exact h6C
  have hstart2 : (mitPc 44 rc).temp (frei + 2) = some (natVal y) := by
    simp only [mitPc]
    change rc.temp (frei + 2) = _
    rw [hpresC (frei + 2) (by omega) (by omega)]
    change r0.temp (frei + 2) = _
    change rp.temp (frei + 2) = _
    rw [hpresP (frei + 2) (by omega) (by omega)]
    exact hy
  obtain ⟨rN, hrunN, hpcN, hNbool, hNpres, hlokN, hrueckN, hstoppN⟩ :=
    rfindNulltestPosLauf cfBlk aus frei v (mitPc 44 rc) hstartpc hstart6 hvpos
  have hN2 : rN.temp (frei + 2) = some (natVal y) := by
    rw [hNpres (frei + 2) (by omega)]
    exact hstart2
  obtain ⟨r1, hrunR, hpc1, hR2, hRpres, hlokR, hrueckR, hstoppR⟩ :=
    rfindRueckLauf cfBlk aus frei y rN (by rw [hpcN]) hN2
  have hrunTail : (Schritt (rfindSchleife cfBlk aus frei))^[6] (some (mitPc 44 rc)) = some r1 := by
    rw [show (6 : Nat) = 3 + 3 by omega, Function.iterate_add_apply, hrunN, hrunR]
  let k := (6 + kcf) + kp
  refine ⟨k, r1, by omega, ?_, hpc1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [k]
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hrunPAll, hrunCAll, hrunTail]
  · rw [hRpres (frei + 0) (by omega) (by omega)]
    rw [hNpres (frei + 0) (by omega)]
    simp only [mitPc]
    change rc.temp (frei + 0) = _
    rw [hpresC (frei + 0) (by omega) (by omega)]
    change r0.temp (frei + 0) = _
    change rp.temp (frei + 0) = _
    rw [hpresP (frei + 0) (by omega) (by omega)]
    exact ha
  · rw [hRpres (frei + 1) (by omega) (by omega)]
    rw [hNpres (frei + 1) (by omega)]
    simp only [mitPc]
    change rc.temp (frei + 1) = _
    rw [hpresC (frei + 1) (by omega) (by omega)]
    change r0.temp (frei + 1) = _
    change rp.temp (frei + 1) = _
    rw [hpresP (frei + 1) (by omega) (by omega)]
    exact hm
  · exact hR2
  · rw [hlokR, hlokN]
    change rc.lokale = r.lokale
    rw [hlokC]
    change rp.lokale = r.lokale
    exact hlokP
  · rw [hrueckR, hrueckN]
    change rc.rueckgabe = r.rueckgabe
    rw [hrueckC]
    change rp.rueckgabe = r.rueckgabe
    exact hrueckP
  · rw [hstoppR, hstoppN]
    change rc.stopp = r.stopp
    rw [hstoppC]
    change rp.stopp = r.stopp
    exact hstoppP

/-- One iteration that exits: the zero result makes the conditional jump to
    the copy segment, which writes the candidate into the output slot. -/
theorem rfindExitIter (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf : Nat) (m0 y : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (ha : r.temp (frei + 0) = some (natVal a))
    (hm : r.temp (frei + 1) = some (natVal m0))
    (hy : r.temp (frei + 2) = some (natVal y))
    (hcfBlk : BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf)
    (hvBlk : VerschiebbaresProgramm cfBlk)
    (hzero : Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some 0) :
    ∃ k rEnd,
      (Schritt (rfindSchleife cfBlk aus frei))^[k] (some r) = some rEnd ∧
      rEnd.pc = (rfindSchleife cfBlk aus frei).length ∧
      rEnd.temp aus = some (natVal y) := by
  have h4Lt : frei + 4 < freiCf := hcfBlk.1
  obtain ⟨kp, rp, hrunP, hpcP, h4P, hpresP, hlokP, hrueckP, hstoppP⟩ :=
    paarVorwaerts (frei + 0) (frei + 2) (frei + 4) (frei + 10) r a y
      hpc ha hy (by omega) (by omega)
  have hpcPaarEnde : rp.pc = (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)).length := by
    rw [hpcP, paarBerechnungLaenge]
  have hbleibP := laufBleibtVorEnde (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) r kp rp hpcPaarEnde
  have hrunPAll : (Schritt (rfindSchleife cfBlk aus frei))^[kp] (some r) = some rp := by
    rw [rfindSchleifeAlsAnhang]
    exact (laufAnhang (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) _ r kp hbleibP).trans hrunP
  let r0 : Rahmen := { rp with pc := 0 }
  have hmit0 : mitPc 44 r0 = rp := by
    change { rp with pc := 44 + 0 } = rp
    rw [show (44 : Nat) + 0 = rp.pc by rw [hpcP]]
  have h04 : r0.temp (frei + 4) = some (natVal (Nat.pair a y)) := by
    change rp.temp (frei + 4) = _
    exact h4P
  rcases hcfBlk with ⟨_, _, _, hcfNr⟩
  obtain ⟨kcf, rc, hrunC, hpcC, h6C, hpresC, hlokC, hrueckC, hstoppC⟩ :=
    (hcfNr (Nat.pair a y) r0 rfl h04).1 0 hzero
  have hpcCEnde : rc.pc = cfBlk.length := by rw [hpcC]
  have hbleibC := laufBleibtVorEnde cfBlk r0 kcf rc hpcCEnde
  have hshift := laufMitPc (paarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)) cfBlk ((rfindNullTest frei ++ rfindRueck cfBlk frei) ++
    kopie aus (frei + 2)) hvBlk r0 kcf hbleibC
  rw [paarBerechnungLaenge, hrunC] at hshift
  have hrunCAll : (Schritt (rfindSchleife cfBlk aus frei))^[kcf] (some rp) = some (mitPc 44 rc) := by
    rw [← hmit0]
    rw [rfindSchleifeAlsAnhang]
    exact hshift
  have hrunBis : (Schritt (rfindSchleife cfBlk aus frei))^[kcf + kp] (some r) = some (mitPc 44 rc) := by
    rw [Function.iterate_add_apply, hrunPAll, hrunCAll]
  have hstartpc : (mitPc 44 rc).pc = 44 + cfBlk.length := by
    simp only [mitPc]
    rw [hpcC]
  have hstart6 : (mitPc 44 rc).temp (frei + 6) = some (natVal 0) := by
    simp only [mitPc]
    exact h6C
  obtain ⟨rN, hrunN, hpcN, hNbool, hNpres, hlokN, hrueckN, hstoppN⟩ :=
    rfindNulltestNullLauf cfBlk aus frei (mitPc 44 rc) hstartpc hstart6
  have hN2 : rN.temp (frei + 2) = some (natVal y) := by
    rw [hNpres (frei + 2) (by omega)]
    simp only [mitPc]
    change rc.temp (frei + 2) = _
    rw [hpresC (frei + 2) (by omega) (by omega)]
    change r0.temp (frei + 2) = _
    change rp.temp (frei + 2) = _
    rw [hpresP (frei + 2) (by omega) (by omega)]
    exact hy
  obtain ⟨rE, hrunE, hpcE, hausE⟩ := rfindKopieLauf cfBlk aus frei y rN (by rw [hpcN]) hN2
  have hrunTail : (Schritt (rfindSchleife cfBlk aus frei))^[6] (some (mitPc 44 rc)) = some rE := by
    rw [show (6 : Nat) = 3 + 3 by omega, Function.iterate_add_apply, hrunN, hrunE]
  let k := (6 + kcf) + kp
  refine ⟨k, rE, ?_, hpcE, hausE⟩
  dsimp only [k]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hrunPAll, hrunCAll, hrunTail]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
