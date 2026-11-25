module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.KetteRand

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Block correctness of two composed blocks. The forward direction is the
    forward composition lemma. For the reverse direction, a run reaching the
    overall end crosses the block boundary exactly once; the standalone first
    block's arrival there gives the intermediate value, the shifted run of the
    second block gives the final value, and `laufStirbtNach` identifies any
    other arrival with the constructed one. -/
theorem blockKette (blkA blkB : List Befehl) (cA cB : Nat.Partrec.Code)
    (ein mit aus frei freiA freiB : Nat)
    (hA : BlockKorrekt blkA cA ein mit freiA)
    (hlocal : BleibtImBlock blkA) (hlenA : 0 < blkA.length)
    (hvB : VerschiebbaresProgramm blkB)
    (hB : BlockKorrekt blkB cB mit aus freiB) (hlenB : 0 < blkB.length)
    (heinFrei : ein < frei) (hausFrei : aus < frei) (hfreiMit : frei ≤ mit)
    (heina : ein ≠ aus) :
    BlockKorrekt (blkA ++ blkB) (Nat.Partrec.Code.comp cB cA) ein aus frei := by
  unfold BlockKorrekt
  refine ⟨heinFrei, hausFrei, heina, ?_⟩
  rcases hA with ⟨hAein, hAmit, hAun, hAnr⟩
  rcases hB with ⟨hBein, hBaus, hBun, hBnr⟩
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ketteVorwaerts blkA blkB cA cB ein mit aus frei freiA freiB
      ⟨hAein, hAmit, hAun, hAnr⟩ hvB ⟨hBein, hBaus, hBun, hBnr⟩
      heinFrei hausFrei hfreiMit heina n r hpc hr a ha
  · intro k r' hk hpcEnd
    obtain ⟨j, rA, hjk, hrunC, hrunA, hpcA⟩ :=
      randAusEndePrefix blkA blkB hlocal hlenA hlenB r k r' hpc hk hpcEnd
    rcases hAnr n r hpc hr with ⟨hAfwd, hAbwd⟩
    obtain ⟨b, hbAeval, hrAmit, hpresA, hlokA, hrueckA, hstoppA⟩ :=
      hAbwd j rA hrunA hpcA
    have hkdecomp : (Schritt (blkA ++ blkB))^[k] (some r) =
        (Schritt (blkA ++ blkB))^[k - j] ((Schritt (blkA ++ blkB))^[j] (some r)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hkS : (Schritt (blkA ++ blkB))^[k - j] (some rA) = some r' := by
      rw [hkdecomp, hrunC] at hk
      exact hk
    let rA0 : Rahmen := { rA with pc := 0 }
    have hrA0mit : rA0.temp mit = some (natVal b) := hrAmit
    have hmitA : mitPc blkA.length rA0 = rA := by
      show { rA with pc := blkA.length + 0 } = rA
      rw [show blkA.length + 0 = rA.pc by omega]
    have hkS' : (Schritt (blkA ++ blkB))^[k - j] (some (mitPc blkA.length rA0)) = some r' := by
      rw [hmitA]
      exact hkS
    have hpcEnd' : r'.pc = blkA.length + blkB.length := by
      simpa only [List.length_append] using hpcEnd
    obtain ⟨rB, hrunB, hpcB, hEqEnd⟩ :=
      rueckMitPc blkA blkB hvB rA0 (k - j) r' hkS' hpcEnd'
    rcases hBnr b rA0 rfl hrA0mit with ⟨hBfwd, hBbwd⟩
    obtain ⟨a, hbBeval, hrBaus, hpresB, hlokB, hrueckB, hstoppB⟩ :=
      hBbwd (k - j) rB hrunB hpcB
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hres : (Nat.Partrec.Code.eval cA n).bind (fun x => Nat.Partrec.Code.eval cB x) =
          Part.some a := by
        apply Part.bind_eq_some_iff.mpr
        exact ⟨b, hbAeval, hbBeval⟩
      exact hres
    · rw [hEqEnd]
      change rB.temp aus = some (natVal a)
      exact hrBaus
    · intro t ht hne
      rw [hEqEnd]
      change rB.temp t = r.temp t
      have htMit : t < mit := by omega
      have htA : t < freiA := by omega
      have htB : t < freiB := by omega
      have htNeMit : t ≠ mit := by omega
      rw [hpresB t htB hne]
      change rA.temp t = r.temp t
      rw [hpresA t htA htNeMit]
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
