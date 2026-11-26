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


end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
