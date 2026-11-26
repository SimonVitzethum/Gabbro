module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindEval
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueckRand
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindIterationRun

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Reverse direction of the minimisation loop. Any run from a loop entry that
    reaches the loop end determines a first zero candidate for the source code;
    the minimisation evaluation returns that candidate, and the whole frame is
    preserved outside the output slot. -/
theorem rfindSchleifeRueck (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf freiP : Nat) :
    ∀ (m0 y : Nat) (r rEnd : Rahmen) (schr : Nat),
      r.pc = 0 →
      r.temp (frei + 0) = some (natVal a) →
      r.temp (frei + 1) = some (natVal m0) →
      r.temp (frei + 2) = some (natVal y) →
      m0 ≤ y →
      (∀ z, m0 ≤ z → z < y → ∃ v,
        Nat.Partrec.Code.eval cf (Nat.pair a z) = Part.some v ∧ v ≠ 0) →
      BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf →
      VerschiebbaresProgramm cfBlk →
      BleibtImBlock cfBlk →
      frei + 20 ≤ freiCf → frei + 10 ≤ freiP →
      (Schritt (rfindSchleife cfBlk aus frei))^[schr] (some r) = some rEnd →
      rEnd.pc = (rfindSchleife cfBlk aus frei).length →
      ∃ z, Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m0) = Part.some z ∧
        y ≤ z ∧
        rEnd.temp aus = some (natVal z) ∧
        (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
        rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  intro m0 y r rEnd schr
  revert m0 y r rEnd
  refine Nat.strong_induction_on schr ?_
  intro schr ih m0 y r rEnd hpc ha hm hy hmy hvor hcf hv hbl hfreiCf hfreiP hrun hpcEnd
  by_cases hzero : Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some 0
  · obtain ⟨k, rRef, hrunRef, hpcRef, hausRef, hpresRef, hlokRef, hrueckRef, hstoppRef⟩ :=
      rfindExitIter cfBlk cf a aus frei freiCf m0 y r hpc ha hm hy hcf hv hzero
    have hkEq : k = schr := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r k schr rRef rEnd
          hrunRef hpcRef hrun hlt
      · exact laufStirbtNach (rfindSchleife cfBlk aus frei) r schr k rEnd rRef
          hrun hpcEnd hrunRef hgt
    subst k
    have hEq : rEnd = rRef := Option.some.inj (hrun.symm.trans hrunRef)
    refine ⟨y, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact rfindEvalAusVor cf a m0 y hmy hzero hvor
    · rw [hEq]
      exact hausRef
    · rw [hEq]
      exact hpresRef
    · rw [hEq]
      exact hlokRef
    · rw [hEq]
      exact hrueckRef
    · rw [hEq]
      exact hstoppRef
  · by_cases hdef : ∃ v, Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v
    · obtain ⟨k, r1, hkpos, hrun1, hpc1, ha1, hm1, hy1, hlok1, hrueck1, hstopp1, hpres1⟩ :=
        rfindWeiterIter cfBlk cf a aus frei freiCf m0 y r hpc ha hm hy hcf hv hdef hzero
      have hkLe : k ≤ schr := by
        by_contra hle
        have hkgt : schr < k := Nat.lt_of_not_ge hle
        have hstepEnd : Schritt (rfindSchleife cfBlk aus frei) (some rEnd) = none :=
          schrittAmEnde _ rEnd hpcEnd
        have h1none : (Schritt (rfindSchleife cfBlk aus frei))^[schr + 1] (some r) = none := by
          rw [show schr + 1 = 1 + schr by omega, Function.iterate_add_apply, hrun]
          simpa only [Function.iterate_one] using hstepEnd
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (by omega : schr + 1 ≤ k)
        have hknone : (Schritt (rfindSchleife cfBlk aus frei))^[k] (some r) = none := by
          rw [← ht]
          exact laufVerlaengertKein (rfindSchleife cfBlk aus frei) r (schr + 1) t h1none
        rw [hknone] at hrun1
        cases hrun1
      have htail : (Schritt (rfindSchleife cfBlk aus frei))^[schr - k] (some r1) = some rEnd := by
        rw [show schr = k + (schr - k) by omega] at hrun
        rw [Function.iterate_add_apply, hrun1] at hrun
        exact hrun
      have hvorErweitert : ∀ zz, m0 ≤ zz → zz < y + 1 → ∃ vv,
          Nat.Partrec.Code.eval cf (Nat.pair a zz) = Part.some vv ∧ vv ≠ 0 := by
        intro zz hmzz hzzy
        by_cases hzy : zz = y
        · subst zz
          obtain ⟨vv, hvv⟩ := hdef
          refine ⟨vv, hvv, ?_⟩
          intro hv0
          apply hzero
          rw [hvv, hv0]
        · exact hvor zz hmzz (by omega)
      obtain ⟨z, hEvalZ, hy1le, hausZ, hpresTail, hlokTail, hrueckTail, hstoppTail⟩ :=
        ih (schr - k) (by omega) m0 (y + 1) r1 rEnd hpc1 ha1 hm1 hy1 (by omega)
          hvorErweitert hcf hv hbl hfreiCf hfreiP htail hpcEnd
      have hyz : y ≤ z := by omega
      refine ⟨z, hEvalZ, hyz, hausZ, ?_, ?_, ?_, ?_⟩
      · intro s hsl hsaus
        rw [hpresTail s hsl hsaus]
        exact hpres1 s hsl hsaus
      · rw [hlokTail]
        exact hlok1
      · rw [hrueckTail]
        exact hrueck1
      · rw [hstoppTail]
        exact hstopp1
    · -- undefined source value at the current candidate: the run cannot pass the code block
      obtain ⟨kp, rp, hrunP, hpcP, h4P, hpresP, hlokP, hrueckP, hstoppP⟩ :=
        paarVorwaerts (frei + 0) (frei + 2) (frei + 4) (frei + 10) r a y
          hpc ha hy (by omega) (by omega)
      have hpcPaarEnde : rp.pc = (rfindPaar frei).length := by
        rw [hpcP, rfindPaar, paarBerechnungLaenge]
      rw [← rfindPaar] at hrunP
      have hbleibP := laufBleibtVorEnde (rfindPaar frei) r kp rp hrunP hpcPaarEnde
      have hrunPAll : (Schritt (rfindSchleife cfBlk aus frei))^[kp] (some r) = some rp := by
        rw [rfindSchleifeAlsAnhang]
        have hh := (laufAnhang (rfindPaar frei) (cfBlk ++ rfindRest cfBlk aus frei) r kp hbleibP).trans hrunP
        simpa only [List.append_assoc] using hh
      have hrunComp : (Schritt ((rfindPaar frei) ++ (cfBlk ++ rfindRest cfBlk aus frei)))^[schr] (some r) = some rEnd := by
        simpa only [rfindSchleifeAlsAnhang, List.append_assoc] using hrun
      have hpcEndComp : rEnd.pc = ((rfindPaar frei) ++ (cfBlk ++ rfindRest cfBlk aus frei)).length := by
        simpa only [rfindSchleifeAlsAnhang, List.append_assoc] using hpcEnd
      have hlenRest : 0 < (cfBlk ++ rfindRest cfBlk aus frei).length := by
        rw [List.length_append]
        simp only [rfindRest, rfindNullTestLaenge, rfindRueckLaenge, kopieLaenge,
          List.length_append]
        omega
      obtain ⟨hkple, hrunRefComp⟩ :=
        randAusEndeMitRef (rfindPaar frei) (cfBlk ++ rfindRest cfBlk aus frei) hlenRest
          r kp rp hpc hrunP hpcPaarEnde schr rEnd hrunComp hpcEndComp
      have htail : (Schritt (rfindSchleife cfBlk aus frei))^[schr - kp] (some rp) = some rEnd := by
        rw [show schr = kp + (schr - kp) by omega, Function.iterate_add_apply, hrunPAll] at hrun
        exact hrun
      let rp0 : Rahmen := { rp with pc := 0 }
      have hmit : mitPc (rfindPaar frei).length rp0 = rp := by
        show { rp with pc := (rfindPaar frei).length + 0 } = rp
        rw [show (rfindPaar frei).length = rp.pc by rw [hpcP, rfindPaar, paarBerechnungLaenge], Nat.add_zero]
      have htail' : (Schritt ((rfindPaar frei) ++ cfBlk ++ rfindRest cfBlk aus frei))^[schr - kp]
          (some (mitPc (rfindPaar frei).length rp0)) = some rEnd := by
        rw [hmit]
        simpa only [rfindSchleifeAlsAnhang] using htail
      have hpcEnd' : rEnd.pc = (rfindPaar frei).length + cfBlk.length +
          (rfindRest cfBlk aus frei).length := by
        rw [show (rfindPaar frei).length + cfBlk.length + (rfindRest cfBlk aus frei).length =
            (rfindSchleife cfBlk aus frei).length by
          rw [rfindSchleifeAlsAnhang]
          simp only [List.length_append]
          omega]
        exact hpcEnd
      have h4 : rp0.temp (frei + 4) = some (natVal (Nat.pair a y)) := by
        dsimp only [rp0]
        exact h4P
      rcases hcf with ⟨_, _, _, hcfNr⟩
      by_cases hlenCg : cfBlk.length = 0
      · have hp0pc : rp0.pc = cfBlk.length := by
          dsimp only [rp0]
          rw [hpcP]
          rw [rfindPaar, paarBerechnungLaenge]
          omega
        obtain ⟨v, hv⟩ := (hcfNr (Nat.pair a y) rp0 rfl h4).2 0 rp0
          (by rw [Function.iterate_zero_apply]) hp0pc
        exact (hdef ⟨v, hv⟩).elim
      · obtain ⟨jB, rB, rMid, hjB, hrunB, hpcB, hrBMid, hrunMid, hpcMid⟩ :=
          randAusEndeMitPc (rfindPaar frei) cfBlk (rfindRest cfBlk aus frei) hv hbl
            (by omega) hlenRest rp0 rfl (schr - kp) rEnd htail' hpcEnd'
        obtain ⟨v, hv⟩ := (hcfNr (Nat.pair a y) rp0 rfl h4).2 jB rMid hrunMid
          (by rw [hpcMid])
        exact (hdef ⟨v, hv⟩).elim

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
