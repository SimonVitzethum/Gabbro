module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueckSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Stronger reverse direction of the loop: a run reaching the end determines
    both the step-sequence result and the exact natural value in the output
    slot. The pinned statement fixes the latter as a premise; here it is part
    of the conclusion, which is what the whole block's reverse needs. -/
theorem precSchleifeRueckStark (cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (a aus frei freiCg : Nat) :
    ∀ (j i k : Nat) (r rEnd : Rahmen) (schr : Nat),
      r.pc = 0 →
      r.temp (frei + 0) = some (natVal a) →
      r.temp (frei + 1) = some (natVal (j + k)) →
      r.temp (frei + 2) = some (natVal j) →
      r.temp aus = some (natVal i) →
      aus < frei → frei + 20 ≤ freiCg →
      BlockKorrekt cgBlk cg (frei + 5) aus freiCg →
      VerschiebbaresProgramm cgBlk → BleibtImBlock cgBlk →
      (Schritt (precSchleife cgBlk aus frei))^[schr] (some r) = some rEnd →
      rEnd.pc = (precSchleife cgBlk aus frei).length →
      ∃ v, precFolgeVon cg a j k i = Part.some v ∧ rEnd.temp aus = some (natVal v) := by
  intro j i k
  induction k generalizing j i with
  | zero =>
      intro j i v0 r rEnd schr hpc ha hk hy hi haus hcgf hcg hcgv hbl hrun hpcEnd
      have hk0 : r.temp (frei + 1) = some (natVal j) := by
        simpa only [Nat.add_zero] using hk
      obtain ⟨rRef, hRef, hpcRef, hpresRef, hlokRef, hrueckRef, hstoppRef⟩ :=
        precExitLauf cgBlk aus frei j r hpc hy hk0
      have hschr : schr = 8 := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact laufStirbtNach (precSchleife cgBlk aus frei) r schr 8 rEnd rRef
            hrun hpcEnd hRef hlt
        · exact laufStirbtNach (precSchleife cgBlk aus frei) r 8 schr rRef rEnd
            hRef hpcRef hrun hgt
      subst schr
      have hEq : rEnd = rRef := Option.some.inj (hrun.symm.trans hRef)
      have hrEndAus : rEnd.temp aus = some (natVal i) := by
        rw [hEq]
        rw [hpresRef aus (by omega) (by omega)]
        exact hi
      exact ⟨i, rfl, hrEndAus⟩
  | succ k ih =>
      intro j i v0 r rEnd schr hpc ha hk hy hi haus hcgf hcg hcgv hbl hrun hpcEnd
      let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
      let Rm := precRumpf cgBlk aus frei
      let En := precEnde cgBlk frei
      have hVlen : V.length = 8 := by
        dsimp only [V]
        simp only [List.length_append, precCheckLaenge, List.length_cons, List.length_nil]
      have hylen : 0 < En.length := by
        dsimp only [En]
        rw [precEndeLaenge]
        omega
      have hyk : j < j + (k + 1) := by omega
      obtain ⟨r7, hRef8, hpc7, hpres7, hlok7, hrueck7, hstopp7⟩ :=
        precCheckCondLauf cgBlk aus frei j (j + (k + 1)) r hpc hy hk hyk
      have hpc7' : r7.pc = V.length := by rw [hVlen]; exact hpc7
      have hKprog : (Schritt (V ++ (Rm ++ En)))^[schr] (some r) = some rEnd := by
        simpa only [V, Rm, En, precSchleife, List.append_assoc] using hrun
      have hKend : rEnd.pc = (V ++ (Rm ++ En)).length := by
        simpa only [V, Rm, En, precSchleife, List.append_assoc] using hpcEnd
      obtain ⟨h8le, hrun8⟩ :=
        randAusEndeMitRef V (Rm ++ En) (by
          dsimp only [Rm, En]
          rw [List.length_append, precRumpfLaenge, precEndeLaenge]
          omega) r 8 r7 hpc hRef8 hpc7' schr rEnd hKprog hKend
      have hkdecomp : (Schritt (V ++ (Rm ++ En)))^[schr] (some r) =
          (Schritt (V ++ (Rm ++ En)))^[schr - 8]
            ((Schritt (V ++ (Rm ++ En)))^[8] (some r)) := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      have htail : (Schritt (V ++ (Rm ++ En)))^[schr - 8] (some r7) = some rEnd := by
        rw [hkdecomp, hrun8] at hKprog
        exact hKprog
      let r7_0 : Rahmen := { r7 with pc := 0 }
      have hmit7 : mitPc V.length r7_0 = r7 := by
        show { r7 with pc := V.length + 0 } = r7
        rw [show V.length + 0 = r7.pc by rw [hVlen, hpc7, Nat.add_zero]]
      have htail' : (Schritt (V ++ Rm ++ En))^[schr - 8]
          (some (mitPc V.length r7_0)) = some rEnd := by
        rw [hmit7]
        simpa only [List.append_assoc] using htail
      have hKend' : rEnd.pc = V.length + Rm.length + En.length := by
        rw [hKend]
        simp only [List.length_append]
        omega
      have hvRm : VerschiebbaresProgramm Rm := by
        dsimp only [Rm]
        exact (verschiebbarVonNull (precRumpf cgBlk aus frei)).mp
          (verschiebbarPrecRumpf 0 cgBlk aus frei hcgv)
      have hlRm : BleibtImBlock Rm := by
        dsimp only [Rm]
        exact bleibtImBlockPrecRumpf cgBlk aus frei hbl hcgv
      obtain ⟨jB, rB, rMid, hjB, hrunB, hpcB, hrBMid, hrunMid, hpcMid⟩ :=
        randAusEndeMitPc V Rm En hvRm hlRm (by
          dsimp only [Rm]
          rw [precRumpfLaenge]
          omega) hylen r7_0 rfl (schr - 8) rEnd htail' hKend'
      have hr7_0y : r7_0.temp (frei + 2) = some (natVal j) := by
        change r7.temp (frei + 2) = some (natVal j)
        rw [hpres7 (frei + 2) (by omega) (by omega)]
        exact hy
      have hr7_0a : r7_0.temp (frei + 0) = some (natVal a) := by
        change r7.temp (frei + 0) = some (natVal a)
        rw [hpres7 (frei + 0) (by omega) (by omega)]
        exact ha
      have hr7_0i : r7_0.temp aus = some (natVal i) := by
        change r7.temp aus = some (natVal i)
        rw [hpres7 aus (by omega) (by omega)]
        exact hi
      obtain ⟨v1, hv1, hrMidAus, hpresMid, hlokMid, hrueckMid, hstoppMid⟩ :=
        precRumpfRueckOhneHlen cgBlk cg aus frei freiCg j i a r7_0 rMid jB
          rfl hr7_0y hr7_0i hr7_0a haus hcgf hcg hcgv hrunMid hpcMid
      have hrBy : rB.temp (frei + 2) = some (natVal j) := by
        rw [hrBMid]
        change rMid.temp (frei + 2) = some (natVal j)
        rw [hpresMid (frei + 2) (by omega) (by omega) (by omega) (by omega)]
        exact hr7_0y
      have hrBpc : rB.pc = cgBlk.length + 96 := by
        rw [hpcB, hVlen]
        dsimp only [Rm]
        rw [precRumpfLaenge]
        omega
      obtain ⟨rBack, hrunBack, hpcBack, hyBack, hpresBack, hlokBack, hrueckBack, hstoppBack⟩ :=
        precEndeGanzLauf cgBlk aus frei j rB hrBpc hrBy
      have hrBacky : rBack.temp (frei + 2) = some (natVal (j + 1)) := hyBack
      have hrBackpc : rBack.pc = 0 := hpcBack
      have hrBa : rB.temp (frei + 0) = some (natVal a) := by
        rw [hrBMid]
        change rMid.temp (frei + 0) = some (natVal a)
        rw [hpresMid (frei + 0) (by omega) (by omega) (by omega) (by omega)]
        exact hr7_0a
      have hrBk : rB.temp (frei + 1) = some (natVal ((j + 1) + k)) := by
        rw [hrBMid]
        change rMid.temp (frei + 1) = some (natVal ((j + 1) + k))
        rw [hpresMid (frei + 1) (by omega) (by omega) (by omega) (by omega)]
        change r7.temp (frei + 1) = some (natVal ((j + 1) + k))
        rw [hpres7 (frei + 1) (by omega) (by omega)]
        rw [hk]
        exact congrArg natVal (show j + (k + 1) = (j + 1) + k by omega)
      have hrBi : rB.temp aus = some (natVal v1) := by
        rw [hrBMid]
        change rMid.temp aus = some (natVal v1)
        exact hrMidAus
      have hrBacka : rBack.temp (frei + 0) = some (natVal a) := by
        rw [hpresBack (frei + 0) (by omega) (by omega)]
        exact hrBa
      have hrBackk : rBack.temp (frei + 1) = some (natVal ((j + 1) + k)) := by
        rw [hpresBack (frei + 1) (by omega) (by omega)]
        exact hrBk
      have hrBacki : rBack.temp aus = some (natVal v1) := by
        rw [hpresBack aus (by omega) (by omega)]
        exact hrBi
      have hprog8 : (Schritt (precSchleife cgBlk aus frei))^[8] (some r) = some r7 := by
        simpa only [V, precSchleife, List.append_assoc] using hrun8
      have hprogB : (Schritt (precSchleife cgBlk aus frei))^[jB] (some r7) = some rB := by
        rw [← hmit7]
        simpa only [V, Rm, En, precSchleife, List.append_assoc] using hrunB
      have hrunToBack : (Schritt (precSchleife cgBlk aus frei))^[8 + jB + 3] (some r) = some rBack := by
        rw [show 8 + jB + 3 = 3 + (jB + 8) by omega, Function.iterate_add_apply,
          Function.iterate_add_apply, hprog8, hprogB, hrunBack]
      have hrunToB : (Schritt (precSchleife cgBlk aus frei))^[8 + jB] (some r) = some rB := by
        rw [show 8 + jB = jB + 8 by omega, Function.iterate_add_apply, hprog8, hprogB]
      have hstepsLe : 8 + jB + 3 ≤ schr := by
        by_contra hnot
        have hbase : 8 + jB ≤ schr := by omega
        obtain ⟨rT, hrT⟩ := laufHatZwischen (precSchleife cgBlk aus frei) r schr (8 + jB) rEnd hrun hbase
        have hT : rT = rB := Option.some.inj (hrT.symm.trans hrunToB)
        have hcases : schr = 8 + jB ∨ schr = 8 + jB + 1 ∨ schr = 8 + jB + 2 := by omega
        rcases hcases with hs0 | hs1 | hs2
        · have hE : rEnd = rB := by
            have hh : some rEnd = some rT := by
              rw [hs0] at hrun
              exact hrun.symm.trans hrT
            exact (Option.some.inj hh).trans hT
          have hpB : rB.pc = (precSchleife cgBlk aus frei).length := by
            rw [← hE]
            exact hpcEnd
          rw [hrBpc, precSchleifeLaenge] at hpB
          omega
        · obtain ⟨r1, hr1⟩ := laufHatZwischen (precSchleife cgBlk aus frei) r schr (8 + jB + 1)
            rEnd hrun (by omega)
          have hr1Mid : (Schritt (precSchleife cgBlk aus frei))^[8 + jB + 1] (some r) = some r1 := hr1
          rw [show 8 + jB + 1 = Nat.succ (8 + jB) by omega, Function.iterate_succ_apply',
            hrunToB] at hr1
          have hg : (precSchleife cgBlk aus frei)[rB.pc]? = some (.literal (frei + 3) 1) := by
            rw [hrBpc]
            exact precSchleifeBeiEnde0 cgBlk aus frei
          have hs : Schritt (precSchleife cgBlk aus frei) (some rB) =
              some (rB.schreibe (frei + 3) (some (natVal 1))) := by
            simpa only [Rahmen.schreibe] using
              (schrittLiteral (precSchleife cgBlk aus frei) rB rB.pc (frei + 3) 1 rfl hg)
          rw [hs] at hr1
          have hr1Eq : r1 = rB.schreibe (frei + 3) (some (natVal 1)) := Option.some.inj hr1.symm
          have hp : r1.pc = cgBlk.length + 97 := by
            rw [hr1Eq]
            change rB.pc + 1 = cgBlk.length + 97
            rw [hrBpc]
          have hr1end : r1 = rEnd := Option.some.inj (by
            have hrun1 := hrun
            rw [hs1] at hrun1
            exact hr1Mid.symm.trans hrun1)
          have hpEnd : r1.pc = (precSchleife cgBlk aus frei).length := by
            rw [hr1end]
            exact hpcEnd
          rw [hp, precSchleifeLaenge] at hpEnd
          omega
        · obtain ⟨r2, hr2⟩ := laufHatZwischen (precSchleife cgBlk aus frei) r schr (8 + jB + 2)
            rEnd hrun (by omega)
          have hr2Mid : (Schritt (precSchleife cgBlk aus frei))^[8 + jB + 2] (some r) = some r2 := hr2
          obtain ⟨rTwo, hTwo, hpTwo, hyTwo, hthree, hpresTwo, hlokTwo, hrueckTwo, hstoppTwo⟩ :=
            precEndeZweiSchritte cgBlk aus frei j rB hrBpc hrBy
          have hT2 : r2 = rTwo := Option.some.inj (by
            rw [show 8 + jB + 2 = 2 + (8 + jB) by omega, Function.iterate_add_apply, hrunToB] at hr2
            exact hr2.symm.trans hTwo)
          have hr2end : r2 = rEnd := Option.some.inj (by
            have hrun2 := hrun
            rw [hs2] at hrun2
            exact hr2Mid.symm.trans hrun2)
          have hpEnd2 : r2.pc = (precSchleife cgBlk aus frei).length := by
            rw [hr2end]
            exact hpcEnd
          rw [hT2, hpTwo, precSchleifeLaenge] at hpEnd2
          omega
      have hkdecomp2 : (Schritt (precSchleife cgBlk aus frei))^[schr] (some r) =
          (Schritt (precSchleife cgBlk aus frei))^[schr - (8 + jB + 3)]
            ((Schritt (precSchleife cgBlk aus frei))^[8 + jB + 3] (some r)) := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      have hRest : (Schritt (precSchleife cgBlk aus frei))^[schr - (8 + jB + 3)]
          (some rBack) = some rEnd := by
        rw [hkdecomp2, hrunToBack] at hrun
        exact hrun
      obtain ⟨v, hihFolge, hihTemp⟩ := ih (j + 1) v1 v rBack rEnd (schr - (8 + jB + 3))
        hrBackpc hrBacka hrBackk hrBacky hrBacki haus hcgf hcg hcgv hbl hRest hpcEnd
      refine ⟨v, ?_, hihTemp⟩
      rw [precFolgeVonSchritt, hv1, Part.bind_some]
      exact hihFolge

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
