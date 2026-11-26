module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueck
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueckRand
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleifeVorwaerts

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The body reverse statement with no positivity premise on the step block.
    The empty step block is handled directly: the body is then just the two
    pairing segments, and the step block's own reverse rule runs in zero steps. -/
theorem precRumpfRueckOhneHlen (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (aus frei freiCg y i a : Nat) (r rEnd : Rahmen) (k : Nat)
    (hpc : r.pc = 0)
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (ha : r.temp (frei + 0) = some (natVal a))
    (hausFrei : aus < frei) (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hk : (Schritt (precRumpf cgBlk aus frei))^[k] (some r) = some rEnd)
    (hpcEnd : rEnd.pc = (precRumpf cgBlk aus frei).length) :
    ∃ v, Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei + 10 → s ≠ aus → s ≠ frei + 4 → s ≠ frei + 5 → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  by_cases hlen : 0 < cgBlk.length
  · exact precRumpfRueck cgBlk cg aus frei freiCg y i a r rEnd k hlen
      hpc hy hi ha hausFrei hfreiCg hcg hvCg hk hpcEnd
  · have hnil : cgBlk = [] := by
      apply List.eq_nil_of_length_eq_zero
      exact Nat.eq_zero_of_not_pos hlen
    subst cgBlk
    rcases hcg with ⟨hcgEin, hcgAus, hcgUn, hcgNr⟩
    have hkP : (Schritt (precPaarEins aus frei ++ precPaarZwei aus frei))^[k]
        (some r) = some rEnd := by
      simpa only [precRumpf, precPaarEinsGleich, precPaarZweiGleich, List.append_nil] using hk
    have hpcP : rEnd.pc = 44 + 44 := by
      rw [hpcEnd, precRumpfLaenge]
      omega
    obtain ⟨hrPair, hpres2, hlok2, hrueck2, hstopp2⟩ :=
      precPaarPaarWert aus frei y i a r rEnd k hpc hy hi ha hausFrei hkP hpcP
    let rEnd0 : Rahmen := { rEnd with pc := 0 }
    have hrEnd0p : rEnd0.temp (frei + 5) = some (natVal (Nat.pair a (Nat.pair y i))) := hrPair
    have hrunNil : (Schritt ([] : List Befehl))^[0] (some rEnd0) = some rEnd0 := rfl
    obtain ⟨v, hvEval, hrAus, hpres0, hlok0, hrueck0, hstopp0⟩ :=
      (hcgNr (Nat.pair a (Nat.pair y i)) rEnd0 rfl hrEnd0p).2 0 rEnd0 hrunNil rfl
    refine ⟨v, hvEval, ?_, ?_, ?_, ?_, ?_⟩
    · change rEnd0.temp aus = some (natVal v)
      exact hrAus
    · intro s hs hneAus hne4 hne5
      change rEnd0.temp s = r.temp s
      exact hpres2 s hs hneAus hne4 hne5
    · change rEnd0.lokale = r.lokale
      exact hlok2
    · change rEnd0.rueckgabe = r.rueckgabe
      exact hrueck2
    · change rEnd0.stopp = r.stopp
      exact hstopp2

/-- Reverse direction of the primitive-recursion loop, as a theorem over the
    pinned obligation. The first conditional is forced not to be taken; a
    relocated boundary lemma isolates one body run and its back edge, and the
    induction hypothesis closes the remaining iterations. -/
theorem precSchleifeRueck (cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (a aus frei freiCg : Nat) :
    precSchleifeRueckAussage cgBlk cf cg a aus frei freiCg := by
  intro j i k
  induction k generalizing j i with
  | zero =>
      intro v r rEnd schr hpc ha hk hy hi hausFrei hfreiCg hcg hvCg hbl hrun hpcEnd hvEnd
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
      have hval : some (natVal v) = some (natVal i) := hvEnd.symm.trans hrEndAus
      have hnat : natVal v = natVal i := Option.some.inj hval
      have hvi : v = i := by
        exact Option.some.inj (by
          simpa only [natValAusgabe] using congrArg NatAusgabe hnat)
      subst v
      rfl
  | succ k ih =>
      intro v r rEnd schr hpc ha hk hy hi hausFrei hfreiCg hcg hvCg hbl hrun hpcEnd hvEnd
      let V := precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]
      let Rm := precRumpf cgBlk aus frei
      let En := precEnde cgBlk frei
      have hVlen : V.length = 8 := by
        dsimp only [V]
        simp only [List.length_append, precCheckLaenge, List.length_cons, List.length_nil]
      have hylen : 0 < (En.length) := by
        dsimp only [En]
        rw [precEndeLaenge]
        omega
      have hyk : j < j + (k + 1) := by omega
      obtain ⟨r7, hRef8, hpc7, hpres7, hlok7, hrueck7, hstopp7⟩ :=
        precCheckCondLauf cgBlk aus frei j (j + (k + 1)) r hpc hy hk hyk
      have hpc7' : r7.pc = V.length := by
        rw [hVlen]
        exact hpc7
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
          (verschiebbarPrecRumpf 0 cgBlk aus frei hvCg)
      have hlRm : BleibtImBlock Rm := by
        dsimp only [Rm]
        exact bleibtImBlockPrecRumpf cgBlk aus frei hbl hvCg
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
          rfl hr7_0y hr7_0i hr7_0a hausFrei hfreiCg hcg hvCg hrunMid hpcMid
      have hrBMid' : rB = mitPc V.length rMid := hrBMid
      have hrBy : rB.temp (frei + 2) = some (natVal j) := by
        rw [hrBMid']
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
        rw [hrBMid']
        change rMid.temp (frei + 0) = some (natVal a)
        rw [hpresMid (frei + 0) (by omega) (by omega) (by omega) (by omega)]
        exact hr7_0a
      have hrBk : rB.temp (frei + 1) = some (natVal ((j + 1) + k)) := by
        rw [hrBMid']
        change rMid.temp (frei + 1) = some (natVal ((j + 1) + k))
        rw [hpresMid (frei + 1) (by omega) (by omega) (by omega) (by omega)]
        change r7.temp (frei + 1) = some (natVal ((j + 1) + k))
        rw [hpres7 (frei + 1) (by omega) (by omega)]
        rw [hk]
        congr 1
        exact (show j + (k + 1) = (j + 1) + k by omega)
      have hrBi : rB.temp aus = some (natVal v1) := by
        rw [hrBMid']
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
        have hT : rT = rB := Option.some.inj (hrunToB.symm.trans hrT)
        have hcases : schr = 8 + jB ∨ schr = 8 + jB + 1 ∨ schr = 8 + jB + 2 := by omega
        rcases hcases with hs0 | hs1 | hs2
        · have hE : rEnd = rB := by
            have hh : some rEnd = some rT := by
              rw [hs0] at hrun
              exact hrun.symm.trans hrT
            exact (Option.some.inj hh).trans hT
          rw [hE, hrBpc, hpcEnd, precSchleifeLaenge] at hrun
          omega
        · obtain ⟨r1, hr1⟩ := laufHatZwischen (precSchleife cgBlk aus frei) r schr (8 + jB + 1)
            rEnd hrun (by omega)
          rw [show 8 + jB + 1 = Nat.succ (8 + jB) by omega, Function.iterate_succ_apply',
            hrunToB] at hr1
          have hg : (precSchleife cgBlk aus frei)[rB.pc]? =
              some (.literal (frei + 3) 1) := by
            rw [hrBpc]
            exact precSchleifeBeiEnde0 cgBlk aus frei
          have hs : Schritt (precSchleife cgBlk aus frei) (some rB) =
              some (rB.schreibe (frei + 3) (some (natVal 1))) := by
            show (match (precSchleife cgBlk aus frei)[rB.pc]? with
              | none => none | some b => some (b.auswerten rB)) =
              some (rB.schreibe (frei + 3) (some (natVal 1)))
            rw [hg]
            simp only [Befehl.auswerten]
          rw [hs] at hr1
          have hp : r1.pc = cgBlk.length + 97 := by
            change rB.pc + 1 = cgBlk.length + 97
            rw [hrBpc]
          rw [hp, hpcEnd, precSchleifeLaenge] at hr1
          omega
        · obtain ⟨r2, hr2⟩ := laufHatZwischen (precSchleife cgBlk aus frei) r schr (8 + jB + 2)
            rEnd hrun (by omega)
          obtain ⟨rTwo, hTwo, hpTwo, hyTwo, hthree, hpresTwo, hlokTwo, hrueckTwo, hstoppTwo⟩ :=
            precEndeZweiSchritte cgBlk aus frei j rB hrBpc hrBy
          have hT2 : r2 = rTwo := Option.some.inj (by
            rw [show 8 + jB + 2 = 2 + (8 + jB) by omega, Function.iterate_add_apply, hrunToB] at hr2
            exact hr2.symm.trans hTwo)
          rw [hT2, hpTwo, hpcEnd, precSchleifeLaenge] at hr2
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
      have hih := ih (j + 1) v1 v rBack rEnd (schr - (8 + jB + 3))
        hrBackpc hrBacka hrBackk hrBacky hrBacki hausFrei hfreiCg hcg hvCg hbl hRest hpcEnd hvEnd
      rw [precFolgeVonSchritt, hv1, Part.bind_some]
      exact hih

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
