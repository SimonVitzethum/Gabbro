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
  admit

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
