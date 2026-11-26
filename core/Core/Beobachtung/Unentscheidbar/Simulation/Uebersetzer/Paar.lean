module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.BlockKette

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Mathlib's pairing function is exactly the closed arithmetic expression used
    by the pairing block: the smaller value is paired into the square. -/
theorem natPairFormel (a b : Nat) :
    Nat.pair a b = (if a < b then b * b + a else a * a + a + b) := rfl

/-- Two blocks reading the same input slot: the first preserves the input, so
    the second can compute from it as well. Both results are left in their own
    slots and every slot below `frei` other than the two outputs is preserved.
    This is the preparation step for the pairing block. -/
theorem zweiEingaengeVor (blkA blkB : List Befehl) (cA cB : Nat.Partrec.Code)
    (ein mitA mitB frei freiA freiB : Nat)
    (hA : BlockKorrekt blkA cA ein mitA freiA)
    (hvB : VerschiebbaresProgramm blkB)
    (hB : BlockKorrekt blkB cB ein mitB freiB)
    (heinFrei : ein < frei) (hmitAFrei : mitA < frei) (hmitBFrei : mitB < frei)
    (hfreiA : frei ≤ freiA) (hfreiB : frei ≤ freiB)
    (heinNeMitA : ein ≠ mitA) (hmitANeMitB : mitA ≠ mitB)
    (n : Nat) (r : Rahmen) (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (a b : Nat) (ha : Nat.Partrec.Code.eval cA n = Part.some a)
    (hb : Nat.Partrec.Code.eval cB n = Part.some b) :
    ∃ k r', (Schritt (blkA ++ blkB))^[k] (some r) = some r' ∧
      r'.pc = (blkA ++ blkB).length ∧ r'.temp mitA = some (natVal a) ∧
      r'.temp mitB = some (natVal b) ∧
      (∀ t, t < frei → t ≠ mitA → t ≠ mitB → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  rcases hA with ⟨hAein, hAmit, hAun, hAnr⟩
  rcases hB with ⟨hBein, hBaus, hBun, hBnr⟩
  rcases hAnr n r hpc hr with ⟨hAfwd, hAbwd⟩
  obtain ⟨kA, rA, hrunA, hpcA, htempA, hpresA, hlokA, hrueckA, hstoppA⟩ := hAfwd a ha
  have hbleibA := laufBleibtVorEnde blkA r kA rA hrunA hpcA
  have hprefixA : (Schritt (blkA ++ blkB))^[kA] (some r) = some rA :=
    (laufAnhang blkA blkB r kA hbleibA).trans hrunA
  let rA0 : Rahmen := { rA with pc := 0 }
  have hrA0pc : rA0.pc = 0 := rfl
  have hrA0ein : rA0.temp ein = some (natVal n) := by
    change rA.temp ein = some (natVal n)
    rw [hpresA ein (by omega) heinNeMitA]
    exact hr
  rcases hBnr n rA0 hrA0pc hrA0ein with ⟨hBfwd, hBbwd⟩
  obtain ⟨kB, rB, hrunB, hpcB, htempB, hpresB, hlokB, hrueckB, hstoppB⟩ := hBfwd b hb
  have hbleibB := laufBleibtVorEnde blkB rA0 kB rB hrunB hpcB
  have hshift := laufMitPc blkA blkB [] hvB rA0 kB hbleibB
  have hmitPcA : mitPc blkA.length rA0 = rA := by
    show { rA with pc := blkA.length + 0 } = rA
    rw [show blkA.length + 0 = rA.pc by omega]
  have hKB : (Schritt (blkA ++ blkB))^[kB] (some rA) = some (mitPc blkA.length rB) := by
    simpa only [List.append_nil, hmitPcA, hrunB] using hshift
  refine ⟨kB + kA, mitPc blkA.length rB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hprefixA, hKB]
  · simp only [mitPc, hpcB, List.length_append]
  · change rB.temp mitA = some (natVal a)
    rw [hpresB mitA (by omega) hmitANeMitB]
    change rA.temp mitA = some (natVal a)
    exact htempA
  · change rB.temp mitB = some (natVal b)
    exact htempB
  · intro t ht hneA hneB
    have htA : t < freiA := by omega
    have htB : t < freiB := by omega
    change rB.temp t = r.temp t
    rw [hpresB t htB hneB]
    change rA.temp t = r.temp t
    rw [hpresA t htA hneA]
  · change rB.lokale = r.lokale
    exact hlokB.trans hlokA
  · change rB.rueckgabe = r.rueckgabe
    exact hrueckB.trans hrueckA
  · change rB.stopp = r.stopp
    exact hstoppB.trans hstoppA

/-- Reverse direction for two blocks reading the same input slot. A composite
    run reaching the overall end crosses the first block's boundary once; the
    first block computes `a` into `mitA` while preserving the input, so the
    second block sees the original input and computes `b` into `mitB`. -/
theorem zweiEingaengeRueck (blkA blkB : List Befehl) (cA cB : Nat.Partrec.Code)
    (ein mitA mitB frei freiA freiB : Nat)
    (hA : BlockKorrekt blkA cA ein mitA freiA)
    (hlocal : BleibtImBlock blkA) (hlenA : 0 < blkA.length)
    (hvB : VerschiebbaresProgramm blkB)
    (hB : BlockKorrekt blkB cB ein mitB freiB) (hlenB : 0 < blkB.length)
    (heinFrei : ein < frei) (hmitAFrei : mitA < frei) (hmitBFrei : mitB < frei)
    (hfreiA : frei ≤ freiA) (hfreiB : frei ≤ freiB)
    (heinNeMitA : ein ≠ mitA) (hmitANeMitB : mitA ≠ mitB)
    (n : Nat) (r : Rahmen) (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (k : Nat) (rEnd : Rahmen)
    (hk : (Schritt (blkA ++ blkB))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (blkA ++ blkB).length) :
    ∃ a b : Nat,
      Nat.Partrec.Code.eval cA n = Part.some a ∧
      Nat.Partrec.Code.eval cB n = Part.some b ∧
      rEnd.temp mitA = some (natVal a) ∧ rEnd.temp mitB = some (natVal b) ∧
      (∀ t, t < frei → t ≠ mitA → t ≠ mitB → rEnd.temp t = r.temp t) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  rcases hA with ⟨hAein, hAmit, hAun, hAnr⟩
  rcases hB with ⟨hBein, hBaus, hBun, hBnr⟩
  obtain ⟨j, rA, hjFind, hrunC, hrunA, hpcA⟩ :=
    randAusEndePrefix blkA blkB hlocal hlenA hlenB r k rEnd hpc hk hpcEnd
  obtain ⟨a, haAeval, hrAmitA, hpresA, hlokA, hrueckA, hstoppA⟩ :=
    (hAnr n r hpc hr).2 j rA hrunA hpcA
  have hrAein : rA.temp ein = some (natVal n) := by
    rw [hpresA ein (by omega) heinNeMitA]
    exact hr
  let rA0 : Rahmen := { rA with pc := 0 }
  have hrA0ein : rA0.temp ein = some (natVal n) := hrAein
  have hmitPcA : mitPc blkA.length rA0 = rA := by
    show { rA with pc := blkA.length + 0 } = rA
    rw [show blkA.length + 0 = rA.pc by omega]
  have hkdecomp : (Schritt (blkA ++ blkB))^[k] (some r) =
      (Schritt (blkA ++ blkB))^[k - j] ((Schritt (blkA ++ blkB))^[j] (some r)) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  have hkS : (Schritt (blkA ++ blkB))^[k - j] (some rA) = some rEnd := by
    rw [hkdecomp, hrunC] at hk
    exact hk
  have hkS' : (Schritt (blkA ++ blkB))^[k - j] (some (mitPc blkA.length rA0)) = some rEnd := by
    rw [hmitPcA]
    exact hkS
  have hpcEnd' : rEnd.pc = blkA.length + blkB.length := by
    simpa only [List.length_append] using hpcEnd
  obtain ⟨rB, hrunB, hpcB, hEqEnd⟩ :=
    rueckMitPc blkA blkB hvB rA0 (k - j) rEnd hkS' hpcEnd'
  obtain ⟨b, hbBeval, hrBmitB, hpresB, hlokB, hrueckB, hstoppB⟩ :=
    (hBnr n rA0 rfl hrA0ein).2 (k - j) rB hrunB hpcB
  refine ⟨a, b, haAeval, hbBeval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEqEnd]
    change rB.temp mitA = some (natVal a)
    rw [hpresB mitA (by omega) hmitANeMitB]
    change rA.temp mitA = some (natVal a)
    exact hrAmitA
  · rw [hEqEnd]
    change rB.temp mitB = some (natVal b)
    exact hrBmitB
  · intro t ht hneA hneB
    rw [hEqEnd]
    change rB.temp t = r.temp t
    rw [hpresB t (by omega) hneB]
    change rA.temp t = r.temp t
    rw [hpresA t (by omega) hneA]
  · rw [hEqEnd]
    change rB.lokale = r.lokale
    exact hlokB.trans hlokA
  · rw [hEqEnd]
    change rB.rueckgabe = r.rueckgabe
    exact hrueckB.trans hrueckA
  · rw [hEqEnd]
    change rB.stopp = r.stopp
    exact hstoppB.trans hstoppA

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
