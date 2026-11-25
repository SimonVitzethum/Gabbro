module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen
public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Block correctness for `.pair`. Two blocks read the same input and leave
    their values in `mitA` and `mitB`; the pairing computation then writes
    `Nat.pair` of those values into `aus`. The intermediate slots `mitA`, `mitB`
    and all scratch slots sit at or above `frei`, so only the user-visible slots
    below `frei` other than `aus` survive unchanged. -/
theorem blockPair (blkA blkB : List Befehl) (cf cg : Nat.Partrec.Code)
    (ein mitA mitB aus frei freiA freiB freiV freiP : Nat)
    (hA : BlockKorrekt blkA cf ein mitA freiA)
    (hlocalA : BleibtImBlock blkA) (hlenA : 0 < blkA.length)
    (hvB : VerschiebbaresProgramm blkB)
    (hB : BlockKorrekt blkB cg ein mitB freiB)
    (hlocalB : BleibtImBlock blkB) (hlenB : 0 < blkB.length)
    (heinFrei : ein < frei) (hausFrei : aus < frei) (heinNeAus : ein ≠ aus)
    (hfreiV : frei ≤ freiV) (hmitAFreiV : mitA < freiV) (hmitBFreiV : mitB < freiV)
    (hfreiVA : freiV ≤ freiA) (hfreiVB : freiV ≤ freiB)
    (hmitANeMitB : mitA ≠ mitB)
    (hmitAFrei : frei ≤ mitA) (hmitBFrei : frei ≤ mitB)
    (hfreiP : frei ≤ freiP) (hmitAFreiP : mitA < freiP) (hmitBFreiP : mitB < freiP) :
    BlockKorrekt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP)
      (.pair cf cg) ein aus frei := by
  rcases hA with ⟨hAein, hAmit, hAun, hAnr⟩
  rcases hB with ⟨hBein, hBmit, hBun, hBnr⟩
  unfold BlockKorrekt
  refine ⟨heinFrei, hausFrei, heinNeAus, ?_⟩
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpMem : p ∈ Nat.Partrec.Code.eval (.pair cf cg) n := Part.eq_some_iff.mp hp
    simp only [Nat.Partrec.Code.eval, Seq.seq, Part.map_eq_map,
      Part.mem_bind_iff, Part.mem_map_iff, exists_exists_and_eq_and,
      exists_const] at hpMem
    rcases hpMem with ⟨b, hbMem, c, hcMem, hbc⟩
    have hb : Nat.Partrec.Code.eval cf n = Part.some b := Part.eq_some_iff.mpr hbMem
    have hc : Nat.Partrec.Code.eval cg n = Part.some c := Part.eq_some_iff.mpr hcMem
    obtain ⟨kV, rV, hrunV, hpcV, hrVmitA, hrVmitB, hpresV, hlokV, hrueckV, hstoppV⟩ :=
      zweiEingaengeVor blkA blkB cf cg ein mitA mitB freiV freiA freiB
        ⟨hAein, hAmit, hAun, hAnr⟩ hvB ⟨hBein, hBmit, hBun, hBnr⟩
        (by omega) hmitAFreiV hmitBFreiV hfreiVA hfreiVB hAun hmitANeMitB
        n r hpc hr b c hb hc
    have hbleibV := laufBleibtVorEnde (blkA ++ blkB) r kV rV hrunV hpcV
    have hprefix : (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[kV]
        (some r) = some rV :=
      (laufAnhang (blkA ++ blkB) (paarBerechnung mitA mitB aus freiP) r kV hbleibV).trans hrunV
    let rV0 : Rahmen := { rV with pc := 0 }
    have hrV0pc : rV0.pc = 0 := rfl
    have hrV0mitA : rV0.temp mitA = some (natVal b) := hrVmitA
    have hrV0mitB : rV0.temp mitB = some (natVal c) := hrVmitB
    have hmitPcV : mitPc (blkA ++ blkB).length rV0 = rV := by
      show { rV with pc := (blkA ++ blkB).length + 0 } = rV
      rw [show (blkA ++ blkB).length + 0 = rV.pc by omega]
    obtain ⟨kP, rP, hrunP, hpcP, hrPaus, hpresP, hlokP, hrueckP, hstoppP⟩ :=
      paarVorwaerts mitA mitB aus freiP rV0 b c hrV0pc hrV0mitA hrV0mitB
        hmitAFreiP hmitBFreiP
    have hpcP' : rP.pc = (paarBerechnung mitA mitB aus freiP).length := by
      rw [hpcP, paarBerechnungLaenge]
    have hbleibP := laufBleibtVorEnde (paarBerechnung mitA mitB aus freiP) rV0 kP rP hrunP hpcP'
    have hvP := verschiebbarPaarBerechnung mitA mitB aus freiP
    have hshift := laufMitPc (blkA ++ blkB) (paarBerechnung mitA mitB aus freiP) [] hvP rV0 kP hbleibP
    have hKB : (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[kP]
        (some rV) = some (mitPc (blkA ++ blkB).length rP) := by
      simpa only [List.append_nil, hmitPcV, hrunP] using hshift
    refine ⟨kP + kV, mitPc (blkA ++ blkB).length rP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hprefix, hKB]
    · simp only [mitPc, hpcP', List.length_append]
    · change rP.temp aus = some (natVal p)
      rw [← hbc]
      exact hrPaus
    · intro s hs hne
      change rP.temp s = r.temp s
      have hsP : s < freiP := by omega
      rw [hpresP s hsP hne]
      change rV.temp s = r.temp s
      have hsV : s < freiV := by omega
      have hsNeA : s ≠ mitA := by omega
      have hsNeB : s ≠ mitB := by omega
      exact hpresV s hsV hsNeA hsNeB
    · change rP.lokale = r.lokale
      exact hlokP.trans hlokV
    · change rP.rueckgabe = r.rueckgabe
      exact hrueckP.trans hrueckV
    · change rP.stopp = r.stopp
      exact hstoppP.trans hstoppV
  · intro k rEnd hk hpcEnd
    have hlocalVor := bleibtImBlockAppend blkA blkB hlocalA hvB hlocalB
    have hlenVor : 0 < (blkA ++ blkB).length := by
      simp only [List.length_append]
      omega
    have hlenP : 0 < (paarBerechnung mitA mitB aus freiP).length := by
      rw [paarBerechnungLaenge]
      omega
    obtain ⟨j, rV, hjFind, hrunJ, hrunVorJ, hpcV⟩ :=
      randAusEndePrefix (blkA ++ blkB) (paarBerechnung mitA mitB aus freiP)
        hlocalVor hlenVor hlenP r k rEnd hpc hk hpcEnd
    obtain ⟨a, b, ha, hb, hrVmitA, hrVmitB, hpresV, hlokV, hrueckV, hstoppV⟩ :=
      zweiEingaengeRueck blkA blkB cf cg ein mitA mitB freiV freiA freiB
        ⟨hAein, hAmit, hAun, hAnr⟩ hlocalA hlenA hvB ⟨hBein, hBmit, hBun, hBnr⟩ hlenB
        (by omega) hmitAFreiV hmitBFreiV hfreiVA hfreiVB hAun hmitANeMitB
        n r hpc hr j rV hrunVorJ hpcV
    let rV0 : Rahmen := { rV with pc := 0 }
    have hrV0pc : rV0.pc = 0 := rfl
    have hrV0mitA : rV0.temp mitA = some (natVal a) := hrVmitA
    have hrV0mitB : rV0.temp mitB = some (natVal b) := hrVmitB
    have hmitPcV : mitPc (blkA ++ blkB).length rV0 = rV := by
      show { rV with pc := (blkA ++ blkB).length + 0 } = rV
      rw [show (blkA ++ blkB).length + 0 = rV.pc by omega]
    have hkdecomp : (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[k] (some r) =
        (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[k - j]
          ((Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[j] (some r)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hkS : (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[k - j]
        (some rV) = some rEnd := by
      rw [hkdecomp, hrunJ] at hk
      exact hk
    have hkS' : (Schritt ((blkA ++ blkB) ++ paarBerechnung mitA mitB aus freiP))^[k - j]
        (some (mitPc (blkA ++ blkB).length rV0)) = some rEnd := by
      rw [hmitPcV]
      exact hkS
    have hpcEnd' : rEnd.pc = (blkA ++ blkB).length +
        (paarBerechnung mitA mitB aus freiP).length := by
      simpa only [List.length_append] using hpcEnd
    have hvP := verschiebbarPaarBerechnung mitA mitB aus freiP
    obtain ⟨rP, hrunP, hpcP, hEqEnd⟩ :=
      rueckMitPc (blkA ++ blkB) (paarBerechnung mitA mitB aus freiP) hvP rV0
        (k - j) rEnd hkS' hpcEnd'
    have hpcP' : rP.pc = 44 := hpcP.trans (paarBerechnungLaenge mitA mitB aus freiP)
    obtain ⟨hrPaus, hpresP, hlokP, hrueckP, hstoppP⟩ :=
      paarRueck mitA mitB aus freiP rV0 a b hrV0pc hrV0mitA hrV0mitB
        hmitAFreiP hmitBFreiP (k - j) rP hrunP hpcP'
    refine ⟨Nat.pair a b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Part.eq_some_iff.mpr
      simp only [Nat.Partrec.Code.eval, Seq.seq, Part.map_eq_map,
        Part.mem_bind_iff, Part.mem_map_iff, exists_exists_and_eq_and,
        exists_const]
      exact ⟨a, Part.eq_some_iff.mp ha, b, Part.eq_some_iff.mp hb, rfl⟩
    · rw [hEqEnd]
      change rP.temp aus = some (natVal (Nat.pair a b))
      exact hrPaus
    · intro s hs hne
      rw [hEqEnd]
      change rP.temp s = r.temp s
      have hsP : s < freiP := by omega
      rw [hpresP s hsP hne]
      change rV.temp s = r.temp s
      have hsV : s < freiV := by omega
      have hsNeA : s ≠ mitA := by omega
      have hsNeB : s ≠ mitB := by omega
      exact hpresV s hsV hsNeA hsNeB
    · rw [hEqEnd]
      change rP.lokale = r.lokale
      exact hlokP.trans hlokV
    · rw [hEqEnd]
      change rP.rueckgabe = r.rueckgabe
      exact hrueckP.trans hrueckV
    · rw [hEqEnd]
      change rP.stopp = r.stopp
      exact hstoppP.trans hstoppV

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
