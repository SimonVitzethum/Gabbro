module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecEinSchritt
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBleibt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The check and its untaken conditional, run inside their own eight-instruction
    block: the counter is below the limit, so the jump is not taken. -/
theorem precCheckCondLauf (cgBlk : List Befehl) (aus frei y k : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hy : r.temp (frei + 2) = some (natVal y))
    (hk : r.temp (frei + 1) = some (natVal k)) (hyk : y < k) :
    ∃ r7 : Rahmen,
      (Schritt (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]))^[8] (some r) = some r7 ∧
      r7.pc = 8 ∧
      (∀ s, s ≠ frei + 6 → s ≠ frei + 7 → r7.temp s = r.temp s) ∧
      r7.lokale = r.lokale ∧ r7.rueckgabe = r.rueckgabe ∧ r7.stopp = r.stopp := by
  obtain ⟨rC, hrunC, hpcC, hCb, hCk, hCpres, hlokC, hrueckC, hstoppC⟩ :=
    precCheckLauf r frei y k hpc hy hk
  have hbleibC := laufBleibtVorEnde (precCheck frei) r 7 rC hrunC hpcC
  let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
  have hrunV7 : (Schritt V)^[7] (some r) = some rC := by
    dsimp only [V]
    exact (laufAnhang (precCheck frei)
      [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)] r 7 hbleibC).trans hrunC
  have hboolval : precBool y k = true := by
    rw [precBoolEq, decide_eq_true_eq]
    exact hyk
  have hCbool : rC.temp (frei + 6) = some ⟨.bool, true⟩ := by
    rw [hCb]
    change some (precBoolWert y k) = some ⟨.bool, true⟩
    congr 1
    simp only [precBoolWert, hboolval]
  have hget7 : V[7]? = some (.springeWenn (frei + 6) false (cgBlk.length + 92)) := by
    dsimp only [V]
    rw [List.getElem?_append_right (by rw [precCheckLaenge])]
    rw [show 7 - (precCheck frei).length = 0 by rw [precCheckLaenge]]
    simp only [List.getElem?_cons_zero]
  have eJump := schrittSpringeWennFalsch V rC 7 (frei + 6) false true
    (cgBlk.length + 92) hpcC hCbool (by decide) hget7
  let r7 : Rahmen := { rC with pc := 8 }
  have eJump' : (Schritt V)^[1] (some rC) = some r7 := by
    change Schritt V (some rC) = some r7
    rw [eJump]
    congr 1
    rw [hpcC]
  refine ⟨r7, ?_, rfl, ?_, hlokC, hrueckC, hstoppC⟩
  · rw [show (8 : Nat) = 1 + 7 by omega, Function.iterate_add_apply, hrunV7, eJump']
  · intro s hs6 hs7
    change rC.temp s = r.temp s
    exact hCpres s hs6 hs7

/-- The two pairing segments of the body write the paired step argument. Any
    run of the pairing part that reaches its end identifies that value; the two
    boundaries are located with `randAusEndePrefix`. -/
theorem precPaarPaarWert (cgBlk : List Befehl) (aus frei y i a : Nat)
    (r rEnd : Rahmen) (k : Nat)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei)
    (hk : (Schritt (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
      paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = 44 + 44) :
    rEnd.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) ∧
      (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  let paar1 := paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  let paar2 := paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hlen1 : 0 < paar1.length := by dsimp only [paar1]; rw [paarBerechnungLaenge]; omega
  have hlen2 : 0 < paar2.length := by dsimp only [paar2]; rw [paarBerechnungLaenge]; omega
  have hlocal1 : BleibtImBlock paar1 := by
    dsimp only [paar1]
    exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  have hlocal2 : BleibtImBlock paar2 := by
    dsimp only [paar2]
    exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hv2 : VerschiebbaresProgramm paar2 := by
    dsimp only [paar2]
    exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hk' : (Schritt (paar1 ++ paar2))^[k] (some r) = some rEnd := by
    simpa only [paar1, paar2] using hk
  have hpcEnd' : rEnd.pc = (paar1 ++ paar2).length := by
    dsimp only [paar1, paar2]
    simpa only [List.length_append, paarBerechnungLaenge] using hpcEnd
  obtain ⟨j2, r1, hj2k, hrunC, hrun1, hpc1⟩ :=
    randAusEndePrefix paar1 paar2 hlocal1 hlen1 hlen2 r k rEnd hpc hk' hpcEnd'
  obtain ⟨hr1q, hpres1, hlok1, hrueck1, hstopp1⟩ :=
    paarRueck (frei + 2) aus (frei + 4) (frei + 10) r y i rfl hy hi
      (by omega) (by omega) j2 r1 hrun1 hpc1
  have hkdecomp : (Schritt (paar1 ++ paar2))^[k] (some r) =
      (Schritt (paar1 ++ paar2))^[k - j2]
        ((Schritt (paar1 ++ paar2))^[j2] (some r)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hkS : (Schritt (paar1 ++ paar2))^[k - j2] (some r1) = some rEnd := by
    rw [hkdecomp, hrunC] at hk'
    exact hk'
  let r1_0 : Rahmen := { r1 with pc := 0 }
  have hr1_0a : r1_0.temp (frei + 0) = some (natVal a) := by
    change r1.temp (frei + 0) = some (natVal a)
    rw [hpres1 (frei + 0) (by omega) (by omega)]
    exact ha
  have hr1_0q : r1_0.temp (frei + 4) = some (natVal (Nat.pair y i)) := hr1q
  have hmit1 : mitPc paar1.length r1_0 = r1 := by
    show { r1 with pc := paar1.length + 0 } = r1
    rw [show paar1.length + 0 = r1.pc by rw [hpc1]]
  have hpcEnd2 : rEnd.pc = paar1.length + paar2.length := by
    dsimp only [paar1, paar2]
    simpa only [List.length_append, paarBerechnungLaenge] using hpcEnd
  have hkS' : (Schritt (paar1 ++ paar2))^[k - j2] (some (mitPc paar1.length r1_0)) = some rEnd := by
    rw [hmit1]
    exact hkS
  obtain ⟨rEnd2, hrun2, hpc2, hEq2⟩ :=
    rueckMitPc paar1 paar2 hv2 r1_0 (k - j2) rEnd hkS' hpcEnd2
  obtain ⟨hr2pair, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    paarRueck (frei + 0) (frei + 4) (frei + 5) (frei + 20) r1_0 a (Nat.pair y i)
      rfl hr1_0a hr1_0q (by omega) (by omega) (k - j2) rEnd2 hrun2 hpc2
  have hEnd : rEnd = mitPc 44 rEnd2 := by
    rw [hEq2]
    simp only [paar1, paar2, paarBerechnungLaenge, mitPc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEnd]
    change rEnd2.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i)))
    exact hr2pair
  · intro s hs hneAus hne4 hne5
    rw [hEnd]
    change rEnd2.temp s = r.temp s
    rw [hpres2 s (by omega) hneAus]
    change r1.temp s = r.temp s
    rw [hpres1 s (by omega) hne4 hne5]
  · rw [hEnd]
    change rEnd2.lokale = r.lokale
    exact hlok2.trans hlok1
  · rw [hEnd]
    change rEnd2.rueckgabe = r.rueckgabe
    exact hrueck2.trans hrueck1
  · rw [hEnd]
    change rEnd2.stopp = r.stopp
    exact hstopp2.trans hstopp1

/-- Reverse direction of the primitive-recursion body. Any run of the body that
    reaches its end determines the value of the step code at the paired input.
    The boundary before the step block is located with `randAusEndePrefix`;
    the pairing lemma supplies the paired input to the step block's own reverse
    lemma. -/
theorem precRumpfRueck (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hlenCg : 0 < cgBlk.length)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hk : (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (precRumpf cgBlk aus frei).length) :
    ∃ v, Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  rcases hcg with ⟨hcgEin, hcgAus, hcgUn, hcgNr⟩
  let paar1 := paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
  let paar2 := paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hlen12 : 0 < (paar1 ++ paar2).length := by
    dsimp only [paar1, paar2]
    simp only [List.length_append, paarBerechnungLaenge]
    omega
  have hlocal12 : BleibtImBlock (paar1 ++ paar2) := by
    apply bleibtImBlockAppend
    · dsimp only [paar1]
      exact bleibtImBlockPaarBerechnung (frei + 2) aus (frei + 4) (frei + 10)
    · dsimp only [paar2]
      exact verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
    · dsimp only [paar2]
      exact bleibtImBlockPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hkC : (Schritt ((paar1 ++ paar2) ++ cgBlk))^[k] (some r) = some rEnd := by
    simpa only [precRumpf, paar1, paar2] using hk
  have hpcEndC : rEnd.pc = (paar1 ++ paar2).length + cgBlk.length := by
    simpa only [precRumpf, paar1, paar2, List.length_append] using hpcEnd
  obtain ⟨j1, r2, hj1k, hrunC1, hrun12, hpc2⟩ :=
    randAusEndePrefix (paar1 ++ paar2) cgBlk hlocal12 hlen12 hlenCg r k rEnd hpc hkC hpcEndC
  have hkdecomp : (Schritt ((paar1 ++ paar2) ++ cgBlk))^[k] (some r) =
      (Schritt ((paar1 ++ paar2) ++ cgBlk))^[k - j1]
        ((Schritt ((paar1 ++ paar2) ++ cgBlk))^[j1] (some r)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hkS : (Schritt ((paar1 ++ paar2) ++ cgBlk))^[k - j1] (some r2) = some rEnd := by
    rw [hkdecomp, hrunC1] at hkC
    exact hkC
  let r2_0 : Rahmen := { r2 with pc := 0 }
  have hmit2 : mitPc (paar1 ++ paar2).length r2_0 = r2 := by
    show { r2 with pc := (paar1 ++ paar2).length + 0 } = r2
    rw [show (paar1 ++ paar2).length + 0 = r2.pc by rw [hpc2]]
  have hkS' : (Schritt ((paar1 ++ paar2) ++ cgBlk))^[k - j1]
      (some (mitPc (paar1 ++ paar2).length r2_0)) = some rEnd := by
    rw [hmit2]
    exact hkS
  obtain ⟨rCg, hrunCg, hpcCg, hEqCg⟩ :=
    rueckMitPc (paar1 ++ paar2) cgBlk hvCg r2_0 (k - j1) rEnd hkS' hpcEndC
  have hk12' : (Schritt (paar1 ++ paar2))^[j1] (some r) = some r2 := by
    exact hrun12
  have hpc2' : r2.pc = 44 + 44 := by
    dsimp only [paar1, paar2]
    simpa only [List.length_append, paarBerechnungLaenge] using hpc2
  obtain ⟨hr2pair, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    precPaarPaarWert cgBlk aus frei y i a r r2 j1 hpc hy hi ha hausFrei hk12' hpc2'
  have hr2_0p : r2_0.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) := hr2pair
  obtain ⟨v, hvEval, hrCgaus, hpresCg, hlokCg, hrueckCg, hstoppCg⟩ :=
    (hcgNr (Nat.pair a (Nat.pair y i)) r2_0 rfl hr2_0p).2 (k - j1) rCg hrunCg hpcCg
  have hEqEnd : rEnd = mitPc 44 rCg := by
    rw [hEqCg]
    simp only [paar1, paar2, paarBerechnungLaenge, List.length_append, mitPc]
  refine ⟨v, hvEval, ?_, ?_, ?_, ?_⟩
  · rw [hEqEnd]
    change rCg.temp aus = some (natVal v)
    exact hrCgaus
  · intro s hs hneAus hne4 hne5
    rw [hEqEnd]
    change rCg.temp s = r.temp s
    rw [hpresCg s (by omega) hneAus]
    change r2.temp s = r.temp s
    exact hpres2 s (by omega) hneAus hne4 hne5
  · rw [hEqEnd]
    change rCg.lokale = r.lokale
    exact hlokCg.trans hlok2
  · rw [hEqEnd]
    change rCg.rueckgabe = r.rueckgabe
    exact hrueckCg.trans hrueck2
  · rw [hEqEnd]
    change rCg.stopp = r.stopp
    exact hstoppCg.trans hstopp2

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
