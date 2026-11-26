module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRueckSchleife

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- A standalone run that reaches the end of a prefix is also a run of the
    concatenation with any suffix. -/
theorem laufImAnhang (pre post : List Befehl) (r : Rahmen) (k : Nat) (r' : Rahmen)
    (h : (Schritt pre)^[k] (some r) = some r') (hpc : r'.pc = pre.length) :
    (Schritt (pre ++ post))^[k] (some r) = some r' := by
  have hbleib := laufBleibtVorEnde pre r k r' h hpc
  exact (laufAnhang pre post r k hbleib).trans h

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
  let L := leftBlk ein (frei + 0) freiL
  let R := rightBlk ein (frei + 1) freiL
  let I := [(.literal (frei + 2) 0 : Befehl)]
  let S := precSchleife cgBlk aus frei
  let P := ((L ++ R) ++ cfBlk) ++ I
  have hL : BleibtImBlock L := by
    dsimp only [L]
    exact bleibtImBlockLeft ein (frei + 0) freiL
  have hR : BleibtImBlock R := by
    dsimp only [R]
    exact bleibtImBlockRight ein (frei + 1) freiL
  have hvR : VerschiebbaresProgramm R := by
    dsimp only [R]
    exact verschiebbarRight ein (frei + 1) freiL
  have hI : BleibtImBlock I := by
    dsimp only [I]
    exact bleibtImBlockPrecInit frei
  have hvI : VerschiebbaresProgramm I := by
    dsimp only [I]
    exact verschiebbarPrecInit frei
  have hLR : BleibtImBlock (L ++ R) := bleibtImBlockAppend L R hL hvR hR
  have hLRc : BleibtImBlock ((L ++ R) ++ cfBlk) :=
    bleibtImBlockAppend (L ++ R) cfBlk hLR hcfV hcfBl
  have hP : BleibtImBlock P := by
    dsimp only [P]
    exact bleibtImBlockAppend ((L ++ R) ++ cfBlk) I hLRc hvI hI
  have hlenI : 0 < I.length := by
    dsimp only [I]
    simp only [List.length_cons, List.length_nil]
    omega
  have hlenS : 0 < S.length := by
    dsimp only [S]
    rw [precSchleifeLaenge]
    omega
  have hprecBlk : precBlk cfBlk cgBlk ein aus frei freiL freiCf = P ++ S := by
    dsimp only [P, S, I, L, R]
    rw [precBlk]
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
    rw [← hn] at hv
    rw [evalPrecAlsFolge] at hv
    obtain ⟨v0, hcfEval, hvFolge⟩ := Part.bind_eq_some_iff.mp hv
    have ha : Nat.Partrec.Code.eval .left n = Part.some a := by rfl
    have hk : Nat.Partrec.Code.eval .right n = Part.some k := by rfl
    obtain ⟨kLR, rLR, hrunLR, hpcLR, hrLRa, hrLRk, hpresLR, hlokLR, hrueckLR, hstoppLR⟩ :=
      zweiEingaengeVor L R .left .right ein (frei + 0) (frei + 1) freiL freiL freiL
        (by dsimp only [L]; exact blockLeft ein (frei + 0) freiL (by omega) (by omega) (by omega))
        hvR
        (by dsimp only [R]; exact blockRight ein (frei + 1) freiL (by omega) (by omega) (by omega))
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        n r hpc hr a k ha hk
    let rLR0 : Rahmen := { rLR with pc := 0 }
    have hrLR0a : rLR0.temp (frei + 0) = some (natVal a) := hrLRa
    obtain ⟨kC, rC, hrunC, hpcC, hrCaus, hpresC, hlokC, hrueckC, hstoppC⟩ :=
      (hcfNr a rLR0 rfl hrLR0a).1 v0 hcfEval
    have hbleibC := laufBleibtVorEnde cfBlk rLR0 kC rC hrunC hpcC
    have hvC := hcfV
    have hmitLR : mitPc (L ++ R).length rLR0 = rLR := by
      show { rLR with pc := (L ++ R).length + 0 } = rLR
      rw [show (L ++ R).length + 0 = rLR.pc by rw [hpcLR, Nat.add_zero]]
    have hshiftC : (Schritt ((L ++ R) ++ cfBlk))^[kC] (some rLR) =
        some (mitPc (L ++ R).length rC) := by
      have hs := laufMitPc (L ++ R) cfBlk [] hvC rLR0 kC hbleibC
      simpa only [List.append_nil, hmitLR, hrunC] using hs
    have hcompC : (Schritt (((L ++ R) ++ cfBlk) ++ I))^[kC] (some rLR) =
        some (mitPc (L ++ R).length rC) := by
      have hp : (mitPc (L ++ R).length rC).pc = ((L ++ R) ++ cfBlk).length := by
        simp only [mitPc, List.length_append]
        rw [hpcC]
      exact laufImAnhang ((L ++ R) ++ cfBlk) I rLR kC (mitPc (L ++ R).length rC) hshiftC hp
    let rCcomp := mitPc (L ++ R).length rC
    have hgetI : (((L ++ R) ++ cfBlk) ++ I)[rCcomp.pc]? = some (.literal (frei + 2) 0) := by
      have hp' : rCcomp.pc = ((L ++ R) ++ cfBlk).length := by
        simp only [rCcomp, mitPc, List.length_append]
        rw [hpcC]
      rw [hp']
      simpa only [I, Nat.add_zero] using (getNachPrefix ((L ++ R) ++ cfBlk) I 0 (by
        dsimp only [I]
        simp only [List.length_cons, List.length_nil]))
    have eI : (Schritt (((L ++ R) ++ cfBlk) ++ I))^[1] (some rCcomp) =
        some (rCcomp.schreibe (frei + 2) (some (natVal 0))) := by
      simpa only [Rahmen.schreibe, Function.iterate_one] using
        (schrittLiteral (((L ++ R) ++ cfBlk) ++ I) rCcomp rCcomp.pc (frei + 2) 0 rfl hgetI)
    let rI := rCcomp.schreibe (frei + 2) (some (natVal 0))
    have hrunI : (Schritt P)^[kC + 1] (some rLR) = some rI := by
      dsimp only [P]
      rw [show kC + 1 = 1 + kC by omega, Function.iterate_add_apply, hcompC, eI]
    have hpI : rI.pc = P.length := by
      simp only [rI, rCcomp, P, I, Rahmen.schreibe, mitPc, List.length_append,
        List.length_cons, List.length_nil]
      rw [hpcC]
      omega
    have hrunFullI : (Schritt (P ++ S))^[kC + 1] (some rLR) = some rI :=
      laufImAnhang P S rLR (kC + 1) rI hrunI hpI
    let rI0 : Rahmen := { rI with pc := 0 }
    have hmitI : mitPc P.length rI0 = rI := by
      show { rI with pc := P.length + 0 } = rI
      rw [show P.length + 0 = rI.pc by rw [hpI, Nat.add_zero]]
    have hrI0a : rI0.temp (frei + 0) = some (natVal a) := by
      change rI.temp (frei + 0) = some (natVal a)
      change (rCcomp.schreibe (frei + 2) (some (natVal 0))).temp (frei + 0) = some (natVal a)
      rw [Rahmen.schreibe]
      rw [updateMiss _ _ _ _ (by omega : frei + 0 ≠ frei + 2)]
      change rC.temp (frei + 0) = some (natVal a)
      rw [hpresC (frei + 0) (by omega) (by omega)]
      exact hrLR0a
    have hrI0k : rI0.temp (frei + 1) = some (natVal k) := by
      change rI.temp (frei + 1) = some (natVal k)
      change (rCcomp.schreibe (frei + 2) (some (natVal 0))).temp (frei + 1) = some (natVal k)
      rw [Rahmen.schreibe]
      rw [updateMiss _ _ _ _ (by omega : frei + 1 ≠ frei + 2)]
      change rC.temp (frei + 1) = some (natVal k)
      rw [hpresC (frei + 1) (by omega) (by omega)]
      change rLR0.temp (frei + 1) = some (natVal k)
      exact hrLRk
    have hrI0c : rI0.temp (frei + 2) = some (natVal 0) := by
      change rI.temp (frei + 2) = some (natVal 0)
      change (rCcomp.schreibe (frei + 2) (some (natVal 0))).temp (frei + 2) = some (natVal 0)
      rw [Rahmen.schreibe, updateHit]
    have hrI0v : rI0.temp aus = some (natVal v0) := by
      change rI.temp aus = some (natVal v0)
      change (rCcomp.schreibe (frei + 2) (some (natVal 0))).temp aus = some (natVal v0)
      rw [Rahmen.schreibe]
      rw [updateMiss _ _ _ _ (by omega : aus ≠ frei + 2)]
      change rC.temp aus = some (natVal v0)
      exact hrCaus
    obtain ⟨kS, rS, hrunS, hpcS, hrSaus, hpresS, hlokS, hrueckS, hstoppS⟩ :=
      precSchleifeVorwaerts cgBlk cf cg a aus frei freiCg 0 v0 v rI0
        rfl hrI0a (by simpa only [Nat.zero_add] using hrI0k) hrI0c hrI0v
        haus hfreiCg20 hcg hcgV hcfEval hvFolge
    have hbleibS := laufBleibtVorEnde S rI0 kS rS hrunS hpcS
    have hshiftS : (Schritt (P ++ S))^[kS] (some rI) = some (mitPc P.length rS) := by
      have hs := laufMitPc P S [] hvS rI0 kS hbleibS
      simpa only [List.append_nil, hmitI, hrunS] using hs
    refine ⟨kS + (kC + 1), mitPc P.length rS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hrunFullI, hshiftS]
    · rw [hprecBlk]
      simp only [mitPc, hpcS, List.length_append]
    · change rS.temp aus = some (natVal v)
      exact hrSaus
    · intro s hs hneAus
      change rS.temp s = r.temp s
      rw [hpresS s (by omega) hneAus]
      change rI.temp s = r.temp s
      change (rCcomp.schreibe (frei + 2) (some (natVal 0))).temp s = r.temp s
      rw [Rahmen.schreibe, updateMiss _ _ _ _ (by omega : s ≠ frei + 2)]
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
  · intro k rEnd hrun hpcEnd hvEnd
    sorry
end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
