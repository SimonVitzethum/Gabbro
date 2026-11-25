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

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
