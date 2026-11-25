module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Verschiebung

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Forward correctness of composing two translator blocks. The first block
    computes `cA` from `ein` into the fresh slot `mit`; the second block reads
    `mit` and computes `cB` into `aus`. The composite freedom bound `frei` must
    lie at or below `mit`, so the intermediate slot is scratch, not a preserved
    user slot. -/
theorem ketteVorwaerts (blkA blkB : List Befehl) (cA cB : Nat.Partrec.Code)
    (ein mit aus frei freiA freiB : Nat)
    (hA : BlockKorrekt blkA cA ein mit freiA)
    (hvB : VerschiebbaresProgramm blkB)
    (hB : BlockKorrekt blkB cB mit aus freiB)
    (heinFrei : ein < frei) (hausFrei : aus < frei) (hfreiMit : frei ≤ mit)
    (heina : ein ≠ aus)
    (n : Nat) (r : Rahmen) (hpc : r.pc = 0) (hr : r.temp ein = some (natVal n))
    (a : Nat) (ha : Nat.Partrec.Code.eval (Nat.Partrec.Code.comp cB cA) n = Part.some a) :
    ∃ k r', (Schritt (blkA ++ blkB))^[k] (some r) = some r' ∧
      r'.pc = (blkA ++ blkB).length ∧ r'.temp aus = some (natVal a) ∧
      (∀ t, t < frei → t ≠ aus → r'.temp t = r.temp t) ∧
      r'.lokale = r.lokale ∧ r'.rueckgabe = r.rueckgabe ∧ r'.stopp = r.stopp := by
  rcases hA with ⟨hAein, hAmit, hAun, hAnr⟩
  rcases hB with ⟨hBein, hBaus, hBun, hBnr⟩
  rcases hAnr n r hpc hr with ⟨hAfwd, hAbwd⟩
  have ha' : (Nat.Partrec.Code.eval cA n).bind Nat.Partrec.Code.eval cB = Part.some a := ha
  obtain ⟨b, hbA, hbB⟩ := (Part.bind_eq_some_iff.mp ha')
  obtain ⟨kA, rA, hrunA, hpcA, htempA, hpresA, hlokA, hrueckA, hstoppA⟩ :=
    hAfwd b hbA
  have hbleibA := laufBleibtVorEnde blkA r kA rA hrunA hpcA
  have hprefixA : (Schritt (blkA ++ blkB))^[kA] (some r) = some rA :=
    laufAnhang blkA blkB r kA hbleibA
  let rA0 : Rahmen := { rA with pc := 0 }
  have hrA0pc : rA0.pc = 0 := rfl
  have hrA0temp : rA0.temp mit = some (natVal b) := htempA
  rcases hBnr b rA0 hrA0pc hrA0temp with ⟨hBfwd, hBbwd⟩
  obtain ⟨kB, rB, hrunB, hpcB, htempB, hpresB, hlokB, hrueckB, hstoppB⟩ :=
    hBfwd a hbB
  have hbleibB := laufBleibtVorEnde blkB rA0 kB rB hrunB hpcB
  have hshift := laufMitPc blkA blkB [] hvB rA0 kB hbleibB
  have hmitPcA : mitPc blkA.length rA0 = rA := by
    simp only [mitPc, rA0]
    rw [show blkA.length + 0 = rA.pc by rw [hpcA]; omega]
  have hKB : (Schritt (blkA ++ blkB))^[kB] (some rA) = some (mitPc blkA.length rB) := by
    simpa only [List.append_nil, hmitPcA, hrunB] using hshift
  refine ⟨kB + kA, mitPc blkA.length rB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hprefixA, hKB]
  · simp only [mitPc, hpcB, List.length_append]
  · change rB.temp aus = some (natVal a)
    exact htempB
  · intro t ht hne
    have htMit : t ≠ mit := by omega
    have htFreiA : t < freiA := by omega
    have htFreiB : t < freiB := by omega
    change rB.temp t = r.temp t
    rw [hpresB t htFreiB hne, hpresA t htFreiA htMit]
  · change rB.lokale = r.lokale
    exact hlokB.trans hlokA
  · change rB.rueckgabe = r.rueckgabe
    exact hrueckB.trans hrueckA
  · change rB.stopp = r.stopp
    exact hstoppB.trans hstoppA

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
