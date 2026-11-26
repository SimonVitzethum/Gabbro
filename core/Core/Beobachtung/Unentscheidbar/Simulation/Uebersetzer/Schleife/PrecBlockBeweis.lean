module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleifeStark
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBlockHilfen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Block correctness of the primitive-recursion block, as a theorem over the
    pinned obligation. The forward half composes the two projections, the base
    block, the counter literal and the loop; the reverse half locates the loop
    boundary, reads the step value with the loop's reverse theorem and the base
    value with the base block's reverse rule. -/
theorem blockPrec (cfBlk cgBlk : List Befehl) (cf cg : Nat.Partrec.Code)
    (ein aus frei freiL freiCf freiCg : Nat) :
    blockPrecAussage cfBlk cgBlk cf cg ein aus frei freiL freiCf freiCg := by
  intro hein haus heinAus hfreiL0 hfreiL1 hfreiCf0 hausCf hfreiCf21 hfreiCg20
    hcf hcfBl hcfV hcg hcgBl hcgV hLoopBack
  let I := [(.literal (frei + 2) 0 : Befehl)]
  let S := precSchleife cgBlk aus frei
  let P := ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) ++ I
  have hL : BleibtImBlock (precBlkLinks ein frei freiL) := precBlkLinksBleibt ein frei freiL
  have hR : BleibtImBlock (precBlkRechts ein frei freiL) := precBlkRechtsBleibt ein frei freiL
  have hvR : VerschiebbaresProgramm (precBlkRechts ein frei freiL) :=
    precBlkRechtsVerschiebbar ein frei freiL
  have hI : BleibtImBlock I := by
    dsimp only [I]
    exact bleibtImBlockPrecInit frei
  have hvI : VerschiebbaresProgramm I := by
    dsimp only [I]
    exact verschiebbarPrecInit frei
  have hLR : BleibtImBlock (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) := bleibtImBlockAppend (precBlkLinks ein frei freiL) (precBlkRechts ein frei freiL) hL hvR hR
  have hLRc : BleibtImBlock ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) :=
    bleibtImBlockAppend (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) cfBlk hLR hcfV hcfBl
  have hP : BleibtImBlock P := by
    dsimp only [P]
    exact bleibtImBlockAppend ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) I hLRc hvI hI
  have hlenI : 0 < I.length := by
    dsimp only [I]
    simp only [List.length_cons, List.length_nil]
    omega
  have hlenS : 0 < S.length := by
    dsimp only [S]
    rw [precSchleifeLaenge]
    omega
  have hprecBlk : precBlk cfBlk cgBlk ein aus frei freiL freiCf = P ++ S := by
    dsimp only [P, S, I]
    rw [precBlk, precBlkLinksGleich, precBlkRechtsGleich]
  have hvS : VerschiebbaresProgramm S := by
    dsimp only [S]
    exact verschiebbarPrecSchleife cgBlk aus frei hcgV
  rcases hcf with ⟨hcfEin, hcfAus, hcfUn, hcfNr⟩
  unfold BlockKorrekt
  refine ⟨hein, haus, heinAus, ?_⟩
  intro n r hpc hr
  constructor
  · intro v hv
    let a := (Nat.unpair n).1
    let k := (Nat.unpair n).2
    have hn : Nat.pair a k = n := by
      dsimp only [a, k]
      exact Nat.pair_unpair n
    have hvPair : Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a k) = Part.some v := by
      rw [hn]
      exact hv
    have hvBind := hvPair
    rw [evalPrecAlsFolge] at hvBind
    obtain ⟨v0, hcfEval, hvFolge⟩ := Part.bind_eq_some_iff.mp hvBind
    have ha : Nat.Partrec.Code.eval .left n = Part.some a := by rfl
    have hk : Nat.Partrec.Code.eval .right n = Part.some k := by rfl
    obtain ⟨kLR, rLR, hrunLR, hpcLR, hrLRa, hrLRk, hpresLR, hlokLR, hrueckLR, hstoppLR⟩ :=
      zweiEingaengeVor (precBlkLinks ein frei freiL) (precBlkRechts ein frei freiL) .left .right ein (frei + 0) (frei + 1) freiL freiL freiL
        (precBlkLinksKorrekt ein frei freiL (by omega) (by omega) (by omega))
        hvR
        (precBlkRechtsKorrekt ein frei freiL (by omega) (by omega) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        n r hpc hr a k ha hk
    let rLR0 : Rahmen := { rLR with pc := 0 }
    have hrLR0a : rLR0.temp (frei + 0) = some (natVal a) := hrLRa
    obtain ⟨kC, rC, hrunC, hpcC, hrCaus, hpresC, hlokC, hrueckC, hstoppC⟩ :=
      (hcfNr a rLR0 rfl hrLR0a).1 v0 hcfEval
    have hbleibC := laufBleibtVorEnde cfBlk rLR0 kC rC hrunC hpcC
    have hvC := hcfV
    have hmitLR : mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rLR0 = rLR := by
      show { rLR with pc := (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + 0 } = rLR
      rw [show (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + 0 = rLR.pc by rw [hpcLR, Nat.add_zero]]
    have hshiftC : (Schritt ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk))^[kC] (some rLR) =
        some (mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rC) := by
      have hs := laufMitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) cfBlk [] hvC rLR0 kC hbleibC
      simpa only [List.append_nil, hmitLR, hrunC] using hs
    have hcompC : (Schritt (((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) ++ I))^[kC] (some rLR) =
        some (mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rC) := by
      have hp : (mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rC).pc = ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk).length := by
        simp only [mitPc, List.length_append]
        rw [hpcC]
      exact laufImAnhang ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) I rLR kC (mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rC) hshiftC hp
    let rCcomp := mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rC
    have hgetI : (((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) ++ I)[rCcomp.pc]? = some (.literal (frei + 2) 0) := by
      have hp' : rCcomp.pc = ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk).length := by
        simp only [rCcomp, mitPc, List.length_append]
        rw [hpcC]
      rw [hp']
      simpa only [I, Nat.add_zero, List.getElem?_cons_zero] using (getNachPrefix ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) I 0 (by
        dsimp only [I]
        simp only [List.length_cons, List.length_nil]
        omega))
    have eI : (Schritt (((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) ++ I))^[1] (some rCcomp) =
        some (rCcomp.schreibe (frei + 2) (some (natVal 0))) := by
      simpa only [Rahmen.schreibe, Function.iterate_one] using
        (schrittLiteral (((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) ++ I) rCcomp rCcomp.pc (frei + 2) 0 rfl hgetI)
    let rI := rCcomp.schreibe (frei + 2) (some (natVal 0))
    have hrunI : (Schritt P)^[kC + 1] (some rLR) = some rI := by
      dsimp only [P]
      rw [show kC + 1 = 1 + kC by omega, Function.iterate_add_apply, hcompC, eI]
    have hpI : rI.pc = P.length := by
      simp only [rI, rCcomp, P, I, Rahmen.schreibe, mitPc, List.length_append,
        List.length_cons, List.length_nil]
      rw [hpcC]
    have hrunFullI : (Schritt (P ++ S))^[kC + 1] (some rLR) = some rI :=
      laufImAnhang P S rLR (kC + 1) rI hrunI hpI
    let rI0 : Rahmen := { rI with pc := 0 }
    have hmitI : mitPc P.length rI0 = rI := by
      show { rI with pc := P.length + 0 } = rI
      rw [show P.length + 0 = rI.pc by rw [hpI, Nat.add_zero]]
    have hrI0a : rI0.temp (frei + 0) = some (natVal a) := by
      change rI.temp (frei + 0) = some (natVal a)
      change (Function.update rCcomp.temp (frei + 2) (some (natVal 0))) (frei + 0) = some (natVal a)
      rw [updateMiss rCcomp.temp (frei + 0) (frei + 2) (some (natVal 0)) (by omega)]
      change rC.temp (frei + 0) = some (natVal a)
      rw [hpresC (frei + 0) (by omega) (by omega)]
      exact hrLR0a
    have hrI0k : rI0.temp (frei + 1) = some (natVal k) := by
      change rI.temp (frei + 1) = some (natVal k)
      change (Function.update rCcomp.temp (frei + 2) (some (natVal 0))) (frei + 1) = some (natVal k)
      rw [updateMiss rCcomp.temp (frei + 1) (frei + 2) (some (natVal 0)) (by omega)]
      change rC.temp (frei + 1) = some (natVal k)
      rw [hpresC (frei + 1) (by omega) (by omega)]
      change rLR0.temp (frei + 1) = some (natVal k)
      exact hrLRk
    have hrI0c : rI0.temp (frei + 2) = some (natVal 0) := by
      change rI.temp (frei + 2) = some (natVal 0)
      change (Function.update rCcomp.temp (frei + 2) (some (natVal 0))) (frei + 2) = some (natVal 0)
      rw [updateHit]
    have hrI0v : rI0.temp aus = some (natVal v0) := by
      change rI.temp aus = some (natVal v0)
      change (Function.update rCcomp.temp (frei + 2) (some (natVal 0))) aus = some (natVal v0)
      rw [updateMiss rCcomp.temp aus (frei + 2) (some (natVal 0)) (by omega)]
      change rC.temp aus = some (natVal v0)
      exact hrCaus
    obtain ⟨kS, rS, hrunS, hpcS, hrSaus, hpresS, hlokS, hrueckS, hstoppS⟩ :=
      precSchleifeVorwaerts cgBlk cf cg a aus frei freiCg k v0 v rI0
        rfl hrI0a hrI0k hrI0c hrI0v
        haus hfreiCg20 hcg hcgV hcfEval hvPair
    have hbleibS := laufBleibtVorEnde S rI0 kS rS hrunS hpcS
    have hshiftS : (Schritt (P ++ S))^[kS] (some rI) = some (mitPc P.length rS) := by
      have hs := laufMitPc P S [] hvS rI0 kS hbleibS
      rw [hmitI] at hs
      rw [hrunS] at hs
      simpa only [List.append_nil] using hs
    have hbleibLR := laufBleibtVorEnde (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) r kLR rLR hrunLR hpcLR
    have hrunLR_G : (Schritt (P ++ S))^[kLR] (some r) = some rLR := by
      simpa only [P, List.append_assoc] using
        ((laufAnhang (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) (cfBlk ++ I ++ S) r kLR hbleibLR).trans hrunLR)
    have hpCcomp : rCcomp.pc = ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk).length := by
      simp only [rCcomp, mitPc, List.length_append]
      rw [hpcC]
    have hrunC_G : (Schritt (P ++ S))^[kC] (some rLR) = some rCcomp := by
      have hg := laufImAnhang ((precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk) (I ++ S) rLR kC rCcomp hshiftC hpCcomp
      simpa only [P, List.append_assoc] using hg
    have hrunI_G : (Schritt (P ++ S))^[1] (some rCcomp) = some rI := by
      simpa only [P, List.append_assoc] using (laufImAnhang P S rCcomp 1 rI eI hpI)
    rw [hprecBlk]
    refine ⟨kS + (1 + (kC + kLR)), mitPc P.length rS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, Function.iterate_add_apply,
        Function.iterate_add_apply, hrunLR_G, hrunC_G, hrunI_G, hshiftS]
    · simp only [mitPc, hpcS, List.length_append, S]
    · change rS.temp aus = some (natVal v)
      exact hrSaus
    · intro s hs hneAus
      change rS.temp s = r.temp s
      rw [hpresS s (by omega) hneAus]
      change rI.temp s = r.temp s
      change (Function.update rCcomp.temp (frei + 2) (some (natVal 0))) s = r.temp s
      rw [updateMiss rCcomp.temp s (frei + 2) (some (natVal 0)) (by omega)]
      change rC.temp s = r.temp s
      rw [hpresC s (by omega) hneAus]
      change rLR.temp s = r.temp s
      exact hpresLR s (by omega) (by omega) (by omega)
    · change rS.lokale = r.lokale
      exact hlokS.trans (hlokC.trans hlokLR)
    · change rS.rueckgabe = r.rueckgabe
      exact hrueckS.trans (hrueckC.trans hrueckLR)
    · change rS.stopp = r.stopp
      exact hstoppS.trans (hstoppC.trans hstoppLR)
  · intro k rEnd hrun hpcEnd
    rw [hprecBlk] at hrun hpcEnd
    have hlenP : 0 < P.length := by
      dsimp only [P]
      rw [List.length_append]
      simp only [I, List.length_cons, List.length_nil]
      omega
    obtain ⟨jP, rP, hjPk, hrunScomp, hrunP, hpcP⟩ :=
      randAusEndePrefix P S hP hlenP hlenS r k rEnd hpc hrun hpcEnd
    have hkdecP : (Schritt (P ++ S))^[k] (some r) =
        (Schritt (P ++ S))^[k - jP] ((Schritt (P ++ S))^[jP] (some r)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hkS : (Schritt (P ++ S))^[k - jP] (some rP) = some rEnd := by
      rw [hkdecP, hrunScomp] at hrun
      exact hrun
    let rP0 : Rahmen := { rP with pc := 0 }
    have hmitP : mitPc P.length rP0 = rP := by
      show { rP with pc := P.length + 0 } = rP
      rw [show P.length + 0 = rP.pc by rw [hpcP, Nat.add_zero]]
    have hkS' : (Schritt (P ++ S))^[k - jP] (some (mitPc P.length rP0)) = some rEnd := by
      rw [hmitP]
      exact hkS
    have hpcEndPS : rEnd.pc = P.length + S.length :=
      hpcEnd.trans (@List.length_append Befehl P S)
    obtain ⟨rS, hrunS, hpcS, hEqEnd⟩ :=
      rueckMitPc P S hvS rP0 (k - jP) rEnd hkS' hpcEndPS
    let Q := (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) ++ cfBlk
    have hlenQ : 0 < Q.length := by
      dsimp only [Q]
      rw [List.length_append, List.length_append, precBlkLinksLaenge, precBlkRechtsLaenge]
      omega
    have hpcP_Q : rP.pc = Q.length + I.length := by
      rw [hpcP]
      dsimp only [P]
      rw [List.length_append]
    have hpcP_Q' : rP.pc = (Q ++ I).length :=
      hpcP_Q.trans (@List.length_append Befehl Q I).symm
    obtain ⟨jI, rQ, hjIk, hrunIcomp, hrunQ, hpcQ⟩ :=
      randAusEndePrefix Q I hLRc hlenQ hlenI r jP rP hpc hrunP hpcP_Q'
    have hlenL : 0 < (precBlkLinks ein frei freiL).length := by
      rw [precBlkLinksLaenge ein frei freiL]
      omega
    have hlenR : 0 < (precBlkRechts ein frei freiL).length := by
      rw [precBlkRechtsLaenge ein frei freiL]
      omega
    have hpcQ_LR : rQ.pc = (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + cfBlk.length := by
      rw [hpcQ]
      dsimp only [Q]
      rw [List.length_append]
    have hpcQ_LR' : rQ.pc = (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk).length :=
      hpcQ_LR.trans (@List.length_append Befehl (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) cfBlk).symm
    have hrunQ' : (Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jI] (some r) = some rQ := by
      change (Schritt Q)^[jI] (some r) = some rQ
      exact hrunQ
    have hlenLR : 0 < (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length := by
      rw [List.length_append, precBlkLinksLaenge, precBlkRechtsLaenge]
      omega
    obtain ⟨jC, rLR, hjCk, hrunCcomp, hrunLR, hpcLR⟩ :=
      randAusEndeOder (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) cfBlk
        hLR hlenLR r jI rQ hpc hrunQ' hpcQ_LR'
    obtain ⟨a, kk, haeval, hkeval, hrLRa0, hrLRk0, hpresLRr, hlokLRr, hrueckLRr, hstoppLRr⟩ :=
      zweiEingaengeRueck (precBlkLinks ein frei freiL) (precBlkRechts ein frei freiL) .left .right ein (frei + 0) (frei + 1) freiL freiL freiL
        (precBlkLinksKorrekt ein frei freiL (by omega) (by omega) (by omega))
        hL hlenL hvR
        (precBlkRechtsKorrekt ein frei freiL (by omega) (by omega) (by omega))
        hlenR (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        n r hpc hr jC rLR hrunLR hpcLR
    let rLR0 : Rahmen := { rLR with pc := 0 }
    have hrLR0a : rLR0.temp (frei + 0) = some (natVal a) := hrLRa0
    have hkdecQ : (Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jI] (some r) =
        (Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jI - jC] ((Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jC] (some r)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hkC : (Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jI - jC] (some rLR) = some rQ := by
      rw [hkdecQ, hrunCcomp] at hrunQ
      exact hrunQ
    have hmitLR : mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rLR0 = rLR := by
      show { rLR with pc := (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + 0 } = rLR
      rw [show (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + 0 = rLR.pc by rw [hpcLR, Nat.add_zero]]
    have hkC' : (Schritt (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL ++ cfBlk))^[jI - jC]
        (some (mitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length rLR0)) = some rQ := by
      rw [hmitLR]
      exact hkC
    have hpcQend : rQ.pc = (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL).length + cfBlk.length := hpcQ_LR
    obtain ⟨rC, hrunC, hpcC, hEqQ⟩ :=
      rueckMitPc (precBlkLinks ein frei freiL ++ precBlkRechts ein frei freiL) cfBlk hcfV rLR0 (jI - jC) rQ hkC' hpcQend
    obtain ⟨v0, hcfEval0, hrCaus, hpresCr, hlokCr, hrueckCr, hstoppCr⟩ :=
      (hcfNr a rLR0 rfl hrLR0a).2 (jI - jC) rC hrunC hpcC
    let rQ0 : Rahmen := { rQ with pc := 0 }
    have hmitQ : mitPc Q.length rQ0 = rQ := by
      show { rQ with pc := Q.length + 0 } = rQ
      rw [show Q.length + 0 = rQ.pc by rw [hpcQ, Nat.add_zero]]
    have hIget : I[0]? = some (.literal (frei + 2) 0) := by
      dsimp only [I]
      simp only [List.getElem?_cons_zero]
    have eIref : (Schritt I)^[1] (some rQ0) = some (rQ0.schreibe (frei + 2) (some (natVal 0))) := by
      simpa only [Function.iterate_one, Rahmen.schreibe] using
        (schrittLiteral I rQ0 0 (frei + 2) 0 rfl hIget)
    have hpcIref : (rQ0.schreibe (frei + 2) (some (natVal 0))).pc = I.length := by
      simp only [Rahmen.schreibe, rQ0]
      dsimp only [I]
      simp only [List.length_cons, List.length_nil]
    have hbleibI := laufBleibtVorEnde I rQ0 1 (rQ0.schreibe (frei + 2) (some (natVal 0)))
      eIref hpcIref
    let rPRef := mitPc Q.length (rQ0.schreibe (frei + 2) (some (natVal 0)))
    have eQI : (Schritt (Q ++ I))^[1] (some rQ) = some rPRef := by
      have hs := laufMitPc Q I [] hvI rQ0 1 hbleibI
      rw [hmitQ] at hs
      simpa only [List.append_nil, eIref, rPRef] using hs
    have hpcPRef : rPRef.pc = (Q ++ I).length := by
      simp only [rPRef, mitPc, List.length_append]
      rw [hpcIref]
    have hrunP_QI : (Schritt (Q ++ I))^[jP] (some r) = some rP := by
      change (Schritt P)^[jP] (some r) = some rP
      exact hrunP
    have hkdecI : (Schritt (Q ++ I))^[jP] (some r) =
        (Schritt (Q ++ I))^[jP - jI] ((Schritt (Q ++ I))^[jI] (some r)) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    have hPfromQ : (Schritt (Q ++ I))^[jP - jI] (some rQ) = some rP := by
      rw [hkdecI, hrunIcomp] at hrunP_QI
      exact hrunP_QI
    have hdiff : jP - jI = 1 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach (Q ++ I) rQ (jP - jI) 1 rP rPRef hPfromQ
          (hpcP_Q.trans (@List.length_append Befehl Q I).symm) eQI hlt
      · exact laufStirbtNach (Q ++ I) rQ 1 (jP - jI) rPRef rP eQI hpcPRef hPfromQ hgt
    have hPendEq0 : rP = rPRef := by
      have hEq : (Schritt (Q ++ I))^[1] (some rQ) = some rP := by
        simpa only [hdiff] using hPfromQ
      exact Option.some.inj (hEq.symm.trans eQI)
    have hPendEq : rP = mitPc Q.length (rQ0.schreibe (frei + 2) (some (natVal 0))) := hPendEq0
    have hrP0a : rP0.temp (frei + 0) = some (natVal a) := by
      change rP.temp (frei + 0) = some (natVal a)
      rw [hPendEq]
      dsimp only [rPRef, mitPc, rQ0]
      change (Function.update rQ.temp (frei + 2) (some (natVal 0))) (frei + 0) = some (natVal a)
      rw [updateMiss rQ.temp (frei + 0) (frei + 2) (some (natVal 0)) (by omega)]
      change rQ.temp (frei + 0) = some (natVal a)
      rw [hEqQ]
      change rC.temp (frei + 0) = some (natVal a)
      rw [hpresCr (frei + 0) (by omega) (by omega)]
      exact hrLR0a
    have hrP0k : rP0.temp (frei + 1) = some (natVal kk) := by
      change rP.temp (frei + 1) = some (natVal kk)
      rw [hPendEq]
      dsimp only [rPRef, mitPc, rQ0]
      change (Function.update rQ.temp (frei + 2) (some (natVal 0))) (frei + 1) = some (natVal kk)
      rw [updateMiss rQ.temp (frei + 1) (frei + 2) (some (natVal 0)) (by omega)]
      change rQ.temp (frei + 1) = some (natVal kk)
      rw [hEqQ]
      change rC.temp (frei + 1) = some (natVal kk)
      rw [hpresCr (frei + 1) (by omega) (by omega)]
      change rLR.temp (frei + 1) = some (natVal kk)
      exact hrLRk0
    have hrP0c : rP0.temp (frei + 2) = some (natVal 0) := by
      change rP.temp (frei + 2) = some (natVal 0)
      rw [hPendEq]
      dsimp only [rPRef, mitPc, rQ0]
      change (Function.update rQ.temp (frei + 2) (some (natVal 0))) (frei + 2) = some (natVal 0)
      rw [updateHit]
    have hrP0v : rP0.temp aus = some (natVal v0) := by
      change rP.temp aus = some (natVal v0)
      rw [hPendEq]
      dsimp only [rPRef, mitPc, rQ0]
      change (Function.update rQ.temp (frei + 2) (some (natVal 0))) aus = some (natVal v0)
      rw [updateMiss rQ.temp aus (frei + 2) (some (natVal 0)) (by omega)]
      change rQ.temp aus = some (natVal v0)
      rw [hEqQ]
      change rC.temp aus = some (natVal v0)
      exact hrCaus
    obtain ⟨vFinal, hFolge, hEndTemp⟩ :=
      precSchleifeRueckStark cgBlk cf cg a aus frei freiCg 0 v0 kk rP0 rS (k - jP)
        rfl hrP0a (by simpa only [Nat.zero_add] using hrP0k) hrP0c hrP0v
        haus hfreiCg20 hcg hcgV hcgBl hrunS hpcS
    have haUn : a = (Nat.unpair n).1 := by
      have hh : Part.some ((Nat.unpair n).1) = Part.some a := by
        change Part.some ((Nat.unpair n).1) = Part.some a at haeval
        exact haeval
      exact (Part.some_injective hh).symm
    have hkUn : kk = (Nat.unpair n).2 := by
      have hh : Part.some ((Nat.unpair n).2) = Part.some kk := by
        change Part.some ((Nat.unpair n).2) = Part.some kk at hkeval
        exact hkeval
      exact (Part.some_injective hh).symm
    have hn : Nat.pair a kk = n := by
      rw [haUn, hkUn]
      exact Nat.pair_unpair n
    have hEvalPair : Nat.Partrec.Code.eval (.prec cf cg) n = Part.some vFinal := by
      rw [← hn, evalPrecAlsFolge, hcfEval0, Part.bind_some]
      exact hFolge
    have hvPair : Nat.Partrec.Code.eval (.prec cf cg) (Nat.pair a kk) = Part.some vFinal := by
      rw [hn]
      exact hEvalPair
    obtain ⟨schrRef, rSRef, hrunSRef, hpcSRef, hrSRefAus, hpresSRef, hlokSRef, hrueckSRef, hstoppSRef⟩ :=
      precSchleifeVorwaerts cgBlk cf cg a aus frei freiCg kk v0 vFinal rP0
        rfl hrP0a hrP0k hrP0c hrP0v haus hfreiCg20 hcg hcgV hcfEval0 hvPair
    have hschrEq : k - jP = schrRef := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact laufStirbtNach S rP0 (k - jP) schrRef rS rSRef hrunS hpcS hrunSRef hlt
      · exact laufStirbtNach S rP0 schrRef (k - jP) rSRef rS hrunSRef hpcSRef hrunS hgt
    have hSstate : rS = rSRef := by
      have hrunS2 : (Schritt S)^[schrRef] (some rP0) = some rS := by
        rw [← hschrEq]
        exact hrunS
      exact Option.some.inj (hrunS2.symm.trans hrunSRef)
    refine ⟨vFinal, hEvalPair, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hEqEnd]
      change rS.temp aus = some (natVal vFinal)
      exact hEndTemp
    · intro s hs hneAus
      rw [hEqEnd]
      change rS.temp s = r.temp s
      have hpresS' : rS.temp s = rP0.temp s := by
        rw [hSstate]
        exact hpresSRef s hs hneAus
      rw [hpresS']
      change rP.temp s = r.temp s
      rw [hPendEq]
      dsimp only [rPRef, mitPc, rQ0]
      change (Function.update rQ.temp (frei + 2) (some (natVal 0))) s = r.temp s
      rw [updateMiss rQ.temp s (frei + 2) (some (natVal 0)) (by omega)]
      change rQ.temp s = r.temp s
      rw [hEqQ]
      change rC.temp s = r.temp s
      rw [hpresCr s (by omega) hneAus]
      change rLR.temp s = r.temp s
      exact hpresLRr s (by omega) (by omega) (by omega)
    · rw [hEqEnd]
      change rS.lokale = r.lokale
      rw [hSstate]
      have hP0C : rP0.lokale = rC.lokale := by
        change rP.lokale = rC.lokale
        rw [hPendEq]
        change rQ.lokale = rC.lokale
        rw [hEqQ]
        rfl
      exact hlokSRef.trans (hP0C.trans (hlokCr.trans hlokLRr))
    · rw [hEqEnd]
      change rS.rueckgabe = r.rueckgabe
      rw [hSstate]
      have hP0C : rP0.rueckgabe = rC.rueckgabe := by
        change rP.rueckgabe = rC.rueckgabe
        rw [hPendEq]
        change rQ.rueckgabe = rC.rueckgabe
        rw [hEqQ]
        rfl
      exact hrueckSRef.trans (hP0C.trans (hrueckCr.trans hrueckLRr))
    · rw [hEqEnd]
      change rS.stopp = r.stopp
      rw [hSstate]
      have hP0C : rP0.stopp = rC.stopp := by
        change rP.stopp = rC.stopp
        rw [hPendEq]
        change rQ.stopp = rC.stopp
        rw [hEqQ]
        rfl
      exact hstoppSRef.trans (hP0C.trans (hstoppCr.trans hstoppLRr))
end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
