module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindBlockHilfen
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindEval
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindSchleifeRueck

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Block correctness of the `rfind'` block. The projections supply the two
    components of the input, the copy seeds the candidate, and the loop's
    convergence and reverse theorems connect the two halves to Mathlib's
    minimisation semantics. -/
theorem blockRfind (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (ein aus frei freiL freiCf freiP : Nat) :
    blockRfindAussage cfBlk cf ein aus frei freiL freiCf freiP := by
  intro hein haus heinAus hfreiL0 hfreiL1 hfreiCf4 hfreiCf6 hfreiCf10 hfreiP10
    hcfBlk hcfBl hcfV hKonv hDiv
  let L := leftBlk ein (frei + 0) freiL
  let R := rightBlk ein (frei + 1) freiL
  let LR := L ++ R
  let K := kopie (frei + 2) (frei + 1)
  let S := rfindSchleife cfBlk aus frei
  let P := LR ++ K
  have hblock : rfindBlk cfBlk ein aus frei freiL = P ++ S := by
    simp only [rfindBlk, P, LR, K, L, R, S, List.append_assoc]
  have hLok : BleibtImBlock L := by dsimp only [L]; exact bleibtImBlockLeft ein (frei + 0) freiL
  have hvR : VerschiebbaresProgramm R := by dsimp only [R]; exact verschiebbarRight ein (frei + 1) freiL
  have hRok : BleibtImBlock R := by dsimp only [R]; exact bleibtImBlockRight ein (frei + 1) freiL
  have hLRok : BleibtImBlock LR := by
    dsimp only [LR]
    exact bleibtImBlockAppend L R hLok hvR hRok
  have hvK : VerschiebbaresProgramm K := by dsimp only [K]; exact verschiebbarKopie (frei + 2) (frei + 1)
  have hKok : BleibtImBlock K := by dsimp only [K]; exact bleibtImBlockKopie (frei + 2) (frei + 1)
  have hvS : VerschiebbaresProgramm S := by dsimp only [S]; exact verschiebbarRfindSchleife cfBlk aus frei hcfV
  have hlenL : 0 < L.length := by dsimp only [L]; rw [leftBlkLaenge]; omega
  have hlenR : 0 < R.length := by dsimp only [R]; rw [rightBlkLaenge]; omega
  have hlenLR : 0 < LR.length := by dsimp only [LR]; rw [List.length_append, leftBlkLaenge, rightBlkLaenge]; omega
  have hlenK : 0 < K.length := by dsimp only [K]; rw [kopieLaenge]; omega
  have hlenS : 0 < S.length := by dsimp only [S]; rw [rfindSchleifeLaenge]; omega
  have hlenP : 0 < P.length := by dsimp only [P]; rw [List.length_append]; omega
  have hP : BleibtImBlock P := by dsimp only [P]; exact bleibtImBlockAppend LR K hLRok hvK hKok
  have hK0 : K[0]? = some (.binden nameX (frei + 1)) := by
    dsimp only [K, kopie]
    simp only [List.getElem?_cons_zero]
  have hK1 : K[1]? = some (.lesen (frei + 2) 0) := by
    dsimp only [K, kopie]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hK2 : K[2]? = some (.blockEnde 1) := by
    dsimp only [K, kopie]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_zero]
  rcases hcfBlk with ⟨hcfEin, hcfAus, hcfUn, hcfNr⟩
  unfold BlockKorrekt
  refine ⟨hein, haus, heinAus, ?_⟩
  intro n r hpc hr
  constructor
  · intro v hv
    let a := (Nat.unpair n).1
    let m := (Nat.unpair n).2
    have hn : Nat.pair a m = n := by
      dsimp only [a, m]
      exact Nat.pair_unpair n
    have hv' : Nat.Partrec.Code.eval (.rfind' cf) (Nat.pair a m) = Part.some v := by
      rw [hn]
      exact hv
    obtain ⟨hmv, hzero, hvor⟩ := rfindEvalZeigt cf a m v hv'
    have haEval : Nat.Partrec.Code.eval .left n = Part.some a := by rfl
    have hmEval : Nat.Partrec.Code.eval .right n = Part.some m := by rfl
    obtain ⟨kLR, rLR, hrunLR, hpcLR, hrLRa, hrLRm, hpresLR, hlokLR, hrueckLR, hstoppLR⟩ :=
      zweiEingaengeVor L R .left .right ein (frei + 0) (frei + 1) freiL freiL freiL
        (blockLeft ein (frei + 0) freiL (by omega) (by omega) (by omega)) hvR
        (blockRight ein (frei + 1) freiL (by omega) (by omega) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        n r hpc hr a m haEval hmEval
    let rLR0 : Rahmen := { rLR with pc := 0 }
    let rK : Rahmen := { rLR0 with pc := 3, temp := Function.update rLR0.temp (frei + 2) (some (natVal m)) }
    have hKrun : (Schritt K)^[3] (some rLR0) = some rK := by
      exact laufKopie K rLR0 0 (frei + 2) (frei + 1) (some (natVal m)) rfl hrLRm hK0 hK1 hK2
    have hpcK : rK.pc = K.length := by dsimp only [rK]; rw [kopieLaenge]
    have hmitLR : mitPc LR.length rLR0 = rLR := by
      show { rLR with pc := LR.length + 0 } = rLR
      rw [show LR.length = rLR.pc by rw [hpcLR], Nat.add_zero]
    have hbleibK := laufBleibtVorEnde K rLR0 3 rK (by rw [hKrun]) hpcK
    have hrunLRfull : (Schritt (P ++ S))^[kLR] (some r) = some rLR := by
      have hbleibLR := laufBleibtVorEnde LR r kLR rLR hrunLR hpcLR
      have hh := laufAnhang LR (K ++ S) r kLR hbleibLR
      simpa only [P, S, List.append_assoc] using hh.trans hrunLR
    have hrunKfull : (Schritt (P ++ S))^[3] (some rLR) = some (mitPc LR.length rK) := by
      have hs := laufMitPc LR K S hvK rLR0 3 hbleibK
      rw [hKrun] at hs
      rw [hmitLR] at hs
      simpa only [P, S, List.append_assoc] using hs
    have hrKa : rK.temp (frei + 0) = some (natVal a) := by
      dsimp only [rK, rLR0]
      rw [updateMiss _ (frei + 0) (frei + 2) _ (by omega)]
      exact hrLRa
    have hrKm1 : rK.temp (frei + 1) = some (natVal m) := by
      dsimp only [rK, rLR0]
      rw [updateMiss _ (frei + 1) (frei + 2) _ (by omega)]
      exact hrLRm
    have hrKm2 : rK.temp (frei + 2) = some (natVal m) := by
      dsimp only [rK]
      rw [updateHit]
    let rEntry : Rahmen := { (mitPc LR.length rK) with pc := 0 }
    have hmitEntry : mitPc P.length rEntry = mitPc LR.length rK := by
      show { mitPc LR.length rK with pc := P.length + 0 } = mitPc LR.length rK
      rw [show P.length = (mitPc LR.length rK).pc by
        dsimp only [rK]
        change P.length = LR.length + 3
        dsimp only [P, K]
        rw [List.length_append, kopieLaenge], Nat.add_zero]
    have hrEntrya : rEntry.temp (frei + 0) = some (natVal a) := hrKa
    have hrEntrym1 : rEntry.temp (frei + 1) = some (natVal m) := hrKm1
    have hrEntrym2 : rEntry.temp (frei + 2) = some (natVal m) := hrKm2
    obtain ⟨kE, rE, hrunE, hpcE, hausE, hpresE, hlokE, hrueckE, hstoppE⟩ :=
      rfindErreich cfBlk cf a aus frei freiCf ⟨hcfEin, hcfAus, hcfUn, hcfNr⟩ hcfV
        (v - m) m m v rfl (by omega) hmv rEntry rfl hrEntrya hrEntrym1 hrEntrym2 hzero
        (fun y hy1 hy2 => by
          obtain ⟨vv, hvv, hvne⟩ := hvor y (by omega) hy2
          exact ⟨vv, hvv⟩)
        (fun y hy1 hy2 => by
          obtain ⟨vv, hvv, hvne⟩ := hvor y (by omega) hy2
          intro hzy
          apply hvne
          rw [hvv] at hzy
          exact hvne (Part.some_injective hzy))
    have hbleibE := laufBleibtVorEnde S rEntry kE rE hrunE hpcE
    have hrunEfull : (Schritt (P ++ S))^[kE] (some (mitPc LR.length rK)) = some (mitPc P.length rE) := by
      have hs := laufMitPc P S [] hvS rEntry kE hbleibE
      rw [hrunE] at hs
      rw [hmitEntry] at hs
      simpa only [List.append_nil] using hs
    have hrunTotal : (Schritt (P ++ S))^[kLR + 3 + kE] (some r) = some (mitPc P.length rE) := by
      rw [show kLR + 3 + kE = kE + (3 + kLR) by omega, Function.iterate_add_apply,
        Function.iterate_add_apply, hrunLRfull, hrunKfull, hrunEfull]
    refine ⟨kLR + 3 + kE, mitPc P.length rE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hblock]
      exact hrunTotal
    · change P.length + rE.pc = (rfindBlk cfBlk ein aus frei freiL).length
      rw [hpcE]
      change P.length + S.length = (rfindBlk cfBlk ein aus frei freiL).length
      rw [hblock]
      simp only [List.length_append]
    · change rE.temp aus = some (natVal v)
      exact hausE
    · intro s hs hsa
      change rE.temp s = r.temp s
      rw [hpresE s hs hsa]
      change (mitPc LR.length rK).temp s = r.temp s
      change rK.temp s = r.temp s
      dsimp only [rK, rLR0]
      rw [updateMiss _ s (frei + 2) _ (by omega)]
      change rLR.temp s = r.temp s
      rw [hpresLR s (by omega) (by omega) (by omega)]
    · change rE.lokale = r.lokale
      rw [hlokE]
      change (mitPc LR.length rK).lokale = r.lokale
      change rK.lokale = r.lokale
      dsimp only [rK, rLR0]
      rw [hlokLR]
    · change rE.rueckgabe = r.rueckgabe
      rw [hrueckE]
      change rK.rueckgabe = r.rueckgabe
      dsimp only [rK, rLR0]
      rw [hrueckLR]
    · change rE.stopp = r.stopp
      rw [hstoppE]
      change rK.stopp = r.stopp
      dsimp only [rK, rLR0]
      rw [hstoppLR]
  · intro k rEnd hrun hpcEnd
    rw [hblock] at hrun hpcEnd
    have hlenKS : 0 < (K ++ S).length := by
      dsimp only [K, S]
      rw [List.length_append, kopieLaenge, rfindSchleifeLaenge]
      omega
    have hrun3 : (Schritt (LR ++ (K ++ S)))^[k] (some r) = some rEnd := by
      simpa only [P, List.append_assoc] using hrun
    have hpcEnd3 : rEnd.pc = (LR ++ (K ++ S)).length := by
      simpa only [P, List.append_assoc] using hpcEnd
    obtain ⟨jLR, rLR, hjLRk, hrunLRcomp, hrunLR, hpcLR⟩ :=
      randAusEndePrefix LR (K ++ S) hLRok hlenLR hlenKS r k rEnd hpc hrun3 hpcEnd3
    obtain ⟨a, m, haEval, hmEval, hrLRa, hrLRm, hpresLRr, hlokLRr, hrueckLRr, hstoppLRr⟩ :=
      zweiEingaengeRueck L R .left .right ein (frei + 0) (frei + 1) freiL freiL freiL
        (blockLeft ein (frei + 0) freiL (by omega) (by omega) (by omega)) hLok hlenL hvR
        (blockRight ein (frei + 1) freiL (by omega) (by omega) (by omega)) hlenR
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        n r hpc hr jLR rLR hrunLR hpcLR
    have htail : (Schritt (LR ++ K ++ S))^[k - jLR] (some rLR) = some rEnd := by
      rw [show k = (k - jLR) + jLR by omega] at hrun3
      rw [Function.iterate_add_apply, hrunLRcomp] at hrun3
      simpa only [List.append_assoc] using hrun3
    let rLR0 : Rahmen := { rLR with pc := 0 }
    have hmitLR : mitPc LR.length rLR0 = rLR := by
      show { rLR with pc := LR.length + 0 } = rLR
      rw [show LR.length = rLR.pc by rw [hpcLR], Nat.add_zero]
    have htail' : (Schritt (LR ++ K ++ S))^[k - jLR] (some (mitPc LR.length rLR0)) = some rEnd := by
      rw [hmitLR]
      exact htail
    have hpcEnd' : rEnd.pc = LR.length + K.length + S.length := by
      rw [show LR.length + K.length + S.length = (LR ++ K ++ S).length by
        simp only [List.length_append]]
      exact hpcEnd
    obtain ⟨jK, rB, rMid, hjK, hrunB, hpcB, hrBMid, hrunMid, hpcMid⟩ :=
      randAusEndeMitPc LR K S hvK hKok hlenK hlenS rLR0 rfl (k - jLR) rEnd htail' hpcEnd'
    let rKRef : Rahmen := { rLR0 with pc := 3, temp := Function.update rLR0.temp (frei + 2) (some (natVal m)) }
    have hKref : (Schritt K)^[3] (some rLR0) = some rKRef := by
      exact laufKopie K rLR0 0 (frei + 2) (frei + 1) (some (natVal m)) rfl hrLRm hK0 hK1 hK2
    have hpcKref : rKRef.pc = K.length := by dsimp only [rKRef]; rw [kopieLaenge]
    have hjK3 : jK = 3 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach K rLR0 jK 3 rMid rKRef hrunMid hpcMid hKref hlt
      · exact laufStirbtNach K rLR0 3 jK rKRef rMid hKref hpcKref hrunMid hgt
    have hrMidEq : rMid = rKRef := by
      subst jK
      exact Option.some.inj (hrunMid.symm.trans hKref)
    have hrBpc : rB.pc = P.length := by
      rw [hrBMid]
      change (mitPc LR.length rMid).pc = P.length
      rw [hrMidEq]
      change LR.length + rKRef.pc = P.length
      rw [hpcKref]
      dsimp only [P, K, LR]
      rw [kopieLaenge]
      simp only [List.length_append]
    let rEntry : Rahmen := { rB with pc := 0 }
    have hmitP : mitPc P.length rEntry = rB := by
      show { rB with pc := P.length + 0 } = rB
      rw [show P.length = rB.pc by rw [hrBpc], Nat.add_zero]
    have htailB : (Schritt (P ++ S))^[k - jLR - jK] (some rB) = some rEnd := by
      rw [show k - jLR = (k - jLR - jK) + jK by omega] at htail'
      rw [Function.iterate_add_apply, hrunB] at htail'
      simpa only [P, List.append_assoc] using htail'
    have htailB' : (Schritt (P ++ S))^[k - jLR - jK] (some (mitPc P.length rEntry)) = some rEnd := by
      rw [hmitP]
      exact htailB
    have hpcEndP : rEnd.pc = P.length + S.length := by
      rw [show P.length + S.length = (LR ++ K ++ S).length by
        dsimp only [P]
        simp only [List.length_append]]
      exact hpcEnd
    obtain ⟨rS, hrunS, hpcS, hEqEnd⟩ :=
      rueckMitPc P S hvS rEntry (k - jLR - jK) rEnd htailB' hpcEndP
    have hrEntrya : rEntry.temp (frei + 0) = some (natVal a) := by
      change rB.temp (frei + 0) = some (natVal a)
      rw [hrBMid]
      change rMid.temp (frei + 0) = some (natVal a)
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [updateMiss _ (frei + 0) (frei + 2) _ (by omega)]
      exact hrLRa
    have hrEntrym1 : rEntry.temp (frei + 1) = some (natVal m) := by
      change rB.temp (frei + 1) = some (natVal m)
      rw [hrBMid]
      change rMid.temp (frei + 1) = some (natVal m)
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [updateMiss _ (frei + 1) (frei + 2) _ (by omega)]
      exact hrLRm
    have hrEntrym2 : rEntry.temp (frei + 2) = some (natVal m) := by
      change rB.temp (frei + 2) = some (natVal m)
      rw [hrBMid]
      change rMid.temp (frei + 2) = some (natVal m)
      rw [hrMidEq]
      dsimp only [rKRef]
      rw [updateHit]
    obtain ⟨z, hEval, hmz, hausS, hpresS, hlokS, hrueckS, hstoppS⟩ :=
      rfindSchleifeRueck cfBlk cf a aus frei freiCf freiP m m rEntry rS
        (k - jLR - jK) rfl hrEntrya hrEntrym1 hrEntrym2 le_rfl
        (by intro zz hmzz hzzy; omega)
        ⟨hcfEin, hcfAus, hcfUn, hcfNr⟩ hcfV hcfBl hrunS hpcS
    have haUn : (Nat.unpair n).1 = a := by
      have heq : Part.some ((Nat.unpair n).1) = Part.some a := by
        change Part.some ((Nat.unpair n).1) = Part.some a at haEval
        exact haEval
      exact Part.some_injective heq
    have hmUn : (Nat.unpair n).2 = m := by
      have heq : Part.some ((Nat.unpair n).2) = Part.some m := by
        change Part.some ((Nat.unpair n).2) = Part.some m at hmEval
        exact hmEval
      exact Part.some_injective heq
    have hnRev : Nat.pair a m = n := by
      rw [← haUn, ← hmUn]
      exact Nat.pair_unpair n
    refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hnRev]
      exact hEval
    · rw [hEqEnd]
      change rS.temp aus = some (natVal z)
      exact hausS
    · intro s hs hsa
      rw [hEqEnd]
      change rS.temp s = r.temp s
      rw [hpresS s hs hsa]
      change rEntry.temp s = r.temp s
      change rB.temp s = r.temp s
      rw [hrBMid]
      change rMid.temp s = r.temp s
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [updateMiss _ s (frei + 2) _ (by omega)]
      change rLR.temp s = r.temp s
      rw [hpresLRr s (by omega) (by omega) (by omega)]
    · rw [hEqEnd]
      change rS.lokale = r.lokale
      rw [hlokS]
      change rEntry.lokale = r.lokale
      change rB.lokale = r.lokale
      rw [hrBMid]
      change rMid.lokale = r.lokale
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [hlokLRr]
    · rw [hEqEnd]
      change rS.rueckgabe = r.rueckgabe
      rw [hrueckS]
      change rB.rueckgabe = r.rueckgabe
      rw [hrBMid]
      change rMid.rueckgabe = r.rueckgabe
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [hrueckLRr]
    · rw [hEqEnd]
      change rS.stopp = r.stopp
      rw [hstoppS]
      change rB.stopp = r.stopp
      rw [hrBMid]
      change rMid.stopp = r.stopp
      rw [hrMidEq]
      dsimp only [rKRef, rLR0]
      rw [hstoppLRr]

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
