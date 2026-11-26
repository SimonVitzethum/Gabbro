module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecIteration
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.PaarKorrekt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Forward run of the primitive-recursion body. Two pairing computations form
    `pair (y, i)` and then `pair (a, pair (y, i))`; the step block then reads that
    value from slot `frei+5` and writes its result into the accumulator `aus`.
    Slots below `frei` other than `aus` are preserved. -/
theorem precRumpfLauf (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a v : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei)
    (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hv : Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v) :
    ∃ k rEnd, (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd ∧
      rEnd.pc = (precRumpf cgBlk aus frei).length ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  rcases hcg with ⟨hcgEin, hcgAus, hcgUn, hcgNr⟩
  obtain ⟨k1, r1, hrun1, hpc1, hr1q, hpres1, hlok1, hrueck1, hstopp1⟩ :=
    paarVorwaerts (frei + 2) aus (frei + 4) (frei + 10) r y i hpc hy hi
      (by omega) (by omega)
  have hbleib1 := laufBleibtVorEnde (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10))
    r k1 r1 hrun1 (by rw [hpc1, paarBerechnungLaenge])
  have hprefix1 : (Schritt (precRumpf cgBlk aus frei))^[k1] (some r) = some r1 := by
    change (Schritt ((paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
      paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)) ++ cgBlk))^[k1] (some r) = some r1
    exact (laufAnhang (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10))
      (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20) ++ cgBlk)
      r k1 hbleib1).trans hrun1
  let r1_0 : Rahmen := { r1 with pc := 0 }
  have hr1_0pc : r1_0.pc = 0 := rfl
  have hr1_0a : r1_0.temp (frei + 0) = some (natVal a) := by
    change r1.temp (frei + 0) = some (natVal a)
    rw [hpres1 (frei + 0) (by omega) (by omega)]
    exact ha
  have hr1_0q : r1_0.temp (frei + 4) = some (natVal (Nat.pair y i)) := hr1q
  have hmitPc1 : mitPc (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10)).length r1_0 = r1 := by
    show { r1 with pc := 44 + 0 } = r1
    rw [show (44 : Nat) + 0 = r1.pc by rw [hpc1, paarBerechnungLaenge]]
  obtain ⟨k2, r2, hrun2, hpc2, hr2p, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    paarVorwaerts (frei + 0) (frei + 4) (frei + 5) (frei + 20) r1_0 a (Nat.pair y i)
      hr1_0pc hr1_0a hr1_0q (by omega) (by omega)
  have hbleib2 := laufBleibtVorEnde (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20))
    r1_0 k2 r2 hrun2 (by rw [hpc2, paarBerechnungLaenge])
  have hvPaar2 := verschiebbarPaarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)
  have hprefix2 : (Schritt (precRumpf cgBlk aus frei))^[k2] (some r1) =
      some (mitPc 44 r2) := by
    have hshift := laufMitPc (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10))
      (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)) cgBlk hvPaar2
      r1_0 k2 hbleib2
    rw [List.length_append] at hshift
    simp only [paarBerechnungLaenge] at hshift
    simpa only [hmitPc1, hrun2] using hshift
  let r2_0 : Rahmen := { r2 with pc := 0 }
  have hr2_0pc : r2_0.pc = 0 := rfl
  have hr2_0p : r2_0.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) := hr2p
  have hmitPc2 : mitPc 88 r2_0 = mitPc 44 r2 := by
    show { r2 with pc := 44 + (88 + 0) } = { r2 with pc := 44 + r2.pc }
    rw [hpc2, paarBerechnungLaenge]
    omega
  obtain ⟨k3, r3, hrun3, hpc3, hr3aus, hpres3, hlok3, hrueck3, hstopp3⟩ :=
    hcgNr (Nat.pair a (Nat.pair y i)) r2_0 hr2_0pc hr2_0p v hv
  have hbleib3 := laufBleibtVorEnde cgBlk r2_0 k3 r3 hrun3 (by rw [hpc3])
  have hprefix3 : (Schritt (precRumpf cgBlk aus frei))^[k3] (some (mitPc 44 r2)) =
      some (mitPc 88 r3) := by
    rw [← hmitPc2]
    have hshift := laufMitPc ((paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
      paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20))) cgBlk [] hvCg r2_0 k3 hbleib3
    simp only [List.append_nil] at hshift
    have hlen : (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
      paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20)).length = 88 := by
      simp only [paarBerechnungLaenge, List.length_append]
    rw [hlen] at hshift
    simpa only [hrun3] using hshift
  refine ⟨k3 + k2 + k1, mitPc 88 r3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, hprefix1, hprefix2, hprefix3]
  · simp only [mitPc]
    rw [hpc3]
    exact precRumpfLaenge cgBlk aus frei
  · change r3.temp aus = some (natVal v)
    exact hr3aus
  · intro s hs hne
    change r3.temp s = r.temp s
    rw [hpres3 s (by omega) hne]
    change r2.temp s = r.temp s
    rw [hpres2 s (by omega) (by omega)]
    change r1.temp s = r.temp s
    rw [hpres1 s (by omega) (by omega)]
    rfl
  · change r3.lokale = r.lokale
    exact hlok3.trans (hlok2.trans hlok1)
  · change r3.rueckgabe = r.rueckgabe
    exact hrueck3.trans (hrueck2.trans hrueck1)
  · change r3.stopp = r.stopp
    exact hstopp3.trans (hstopp2.trans hstopp1)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
