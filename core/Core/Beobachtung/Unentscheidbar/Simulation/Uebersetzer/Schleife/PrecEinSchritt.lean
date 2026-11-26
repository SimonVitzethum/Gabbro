module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecRumpf

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The conditional at index seven leaves the loop when the counter has reached
    the limit. -/
theorem precSchleifeBei7 (cgBlk : List Befehl) (aus frei : Nat) :
    (precSchleife cgBlk aus frei)[7]? =
      some (.springeWenn (frei + 6) false (cgBlk.length + 92)) := by
  unfold precSchleife
  rw [List.append_assoc, List.append_assoc]
  rw [List.getElem?_append_right (by rw [precCheckLaenge])]
  rw [show 7 - (precCheck frei).length = 0 by rw [precCheckLaenge]]
  simp only [List.cons_append, List.getElem?_cons_zero]

/-- The first instruction of the back edge sits at offset `cgBlk.length+96`. -/
theorem precSchleifeBeiEnde0 (cgBlk : List Befehl) (aus frei : Nat) :
    (precSchleife cgBlk aus frei)[cgBlk.length + 96]? = some (.literal (frei + 3) 1) := by
  let pre := ((precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]) ++
    precRumpf cgBlk aus frei)
  have hlen : pre.length = cgBlk.length + 96 := by
    simp only [pre, List.length_append, precCheckLaenge, precRumpfLaenge,
      List.length_cons, List.length_nil]
    omega
  have hget := getNachPrefix pre (precEnde cgBlk frei) 0
    (by rw [precEndeLaenge]; omega)
  rw [hlen] at hget
  simpa only [pre, precSchleife, precEnde, Nat.add_zero, List.getElem?_cons_zero] using hget

/-- The increment of the back edge sits one instruction later. -/
theorem precSchleifeBeiEnde1 (cgBlk : List Befehl) (aus frei : Nat) :
    (precSchleife cgBlk aus frei)[cgBlk.length + 97]? = some (.binaer .add (frei + 2)) := by
  let pre := ((precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]) ++
    precRumpf cgBlk aus frei)
  have hlen : pre.length = cgBlk.length + 96 := by
    simp only [pre, List.length_append, precCheckLaenge, precRumpfLaenge,
      List.length_cons, List.length_nil]
    omega
  have hget := getNachPrefix pre (precEnde cgBlk frei) 1
    (by rw [precEndeLaenge]; omega)
  rw [hlen] at hget
  rw [show cgBlk.length + 96 + 1 = cgBlk.length + 97 by omega] at hget
  simpa only [pre, precSchleife, precEnde, List.getElem?_cons_succ,
    List.getElem?_cons_zero] using hget

/-- The back jump returns to the loop's first instruction. -/
theorem precSchleifeBeiEnde2 (cgBlk : List Befehl) (aus frei : Nat) :
    (precSchleife cgBlk aus frei)[cgBlk.length + 98]? =
      some (.zurueckSprung (cgBlk.length + 98)) := by
  let pre := ((precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]) ++
    precRumpf cgBlk aus frei)
  have hlen : pre.length = cgBlk.length + 96 := by
    simp only [pre, List.length_append, precCheckLaenge, precRumpfLaenge,
      List.length_cons, List.length_nil]
    omega
  have hget := getNachPrefix pre (precEnde cgBlk frei) 2
    (by rw [precEndeLaenge]; omega)
  rw [hlen] at hget
  rw [show cgBlk.length + 96 + 2 = cgBlk.length + 98 by omega] at hget
  simpa only [pre, precSchleife, precEnde, List.getElem?_cons_succ,
    List.getElem?_cons_zero] using hget

/-- One iteration of the primitive-recursion loop when the counter is still
    below the limit: check, fall through the conditional, run the body and take
    the back edge. The counter grows by one and the accumulator holds the step
    result; no slot below `frei` other than `aus` changes. -/
theorem precEinSchritt (cgBlk : List Befehl) (cg : Nat.Partrec.Code)
    (a aus frei freiCg y k i v : Nat) (r : Rahmen)
    (hpc : r.pc = 0)
    (ha : r.temp (frei + 0) = some (natVal a))
    (hk : r.temp (frei + 1) = some (natVal k))
    (hy : r.temp (frei + 2) = some (natVal y))
    (hi : r.temp aus = some (natVal i))
    (hyk : y < k)
    (hausFrei : aus < frei)
    (hfreiCg : frei + 20 ≤ freiCg)
    (hcg : BlockKorrekt cgBlk cg (frei + 5) aus freiCg)
    (hvCg : VerschiebbaresProgramm cgBlk)
    (hv : Nat.Partrec.Code.eval cg (Nat.pair a (Nat.pair y i)) = Part.some v) :
    ∃ kSchr rEnd, (Schritt (precSchleife cgBlk aus frei))^[kSchr] (some r) = some rEnd ∧
      rEnd.pc = 0 ∧
      rEnd.temp (frei + 2) = some (natVal (y + 1)) ∧
      rEnd.temp aus = some (natVal v) ∧
      (∀ s, s < frei → s ≠ aus → rEnd.temp s = r.temp s) ∧
      rEnd.lokale = r.lokale ∧ rEnd.rueckgabe = r.rueckgabe ∧ rEnd.stopp = r.stopp := by
  let prog := precSchleife cgBlk aus frei
  obtain ⟨rC, hrunC, hpcC, hCb, hCk, hCpres, hlokC, hrueckC, hstoppC⟩ :=
    precCheckLauf r frei y k hpc hy hk
  have hbleibC := laufBleibtVorEnde (precCheck frei) r 7 rC hrunC hpcC
  have hrunC' : (Schritt prog)^[7] (some r) = some rC := by
    change (Schritt (precSchleife cgBlk aus frei))^[7] (some r) = some rC
    rw [precSchleife, List.append_assoc, List.append_assoc]
    exact (laufAnhang (precCheck frei)
      ([.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
        (precRumpf cgBlk aus frei ++ precEnde cgBlk frei)) r 7 hbleibC).trans hrunC
  have hboolval : precBool y k = true := by
    rw [precBoolEq, decide_eq_true_eq]
    exact hyk
  have hCbool : rC.temp (frei + 6) = some ⟨.bool, true⟩ := by
    rw [hCb]
    change some (precBoolWert y k) = some ⟨.bool, true⟩
    congr 1
    simp only [precBoolWert, hboolval]
  have eJump : (Schritt prog)^[1] (some rC) =
      some { rC with pc := rC.pc + 1 } := by
    have g7 : prog[7]? = some (.springeWenn (frei + 6) false (cgBlk.length + 92)) := by
      change (precSchleife cgBlk aus frei)[7]? =
        some (.springeWenn (frei + 6) false (cgBlk.length + 92))
      exact precSchleifeBei7 cgBlk aus frei
    exact schrittSpringeWennFalsch prog rC 7 (frei + 6) false true (cgBlk.length + 92)
      hpcC hCbool (by decide) g7
  let r7 : Rahmen := { rC with pc := 8 }
  have eJump' : (Schritt prog)^[1] (some rC) = some r7 := by
    rw [eJump]
    congr 1
    rw [hpcC]
  have hrun8 : (Schritt prog)^[8] (some r) = some r7 := by
    rw [show (8 : Nat) = 1 + 7 by omega, Function.iterate_add_apply, hrunC', eJump']
  let r7_0 : Rahmen := { r7 with pc := 0 }
  have hr7_0pc : r7_0.pc = 0 := rfl
  have hr7_0y : r7_0.temp (frei + 2) = some (natVal y) := by
    change rC.temp (frei + 2) = some (natVal y)
    rw [hCpres (frei + 2) (by omega) (by omega)]
    exact hy
  have hr7_0i : r7_0.temp aus = some (natVal i) := by
    change rC.temp aus = some (natVal i)
    rw [hCpres aus (by omega) (by omega)]
    exact hi
  have hr7_0a : r7_0.temp (frei + 0) = some (natVal a) := by
    change rC.temp (frei + 0) = some (natVal a)
    rw [hCpres (frei + 0) (by omega) (by omega)]
    exact ha
  have hmitPc7 : mitPc 8 r7_0 = r7 := by
    rfl
  obtain ⟨kR, rR, hrunR, hpcR, hrRaus, hpresR, hlokR, hrueckR, hstoppR⟩ :=
    precRumpfLauf cgBlk cg aus frei freiCg y i a v r7_0 hr7_0pc hr7_0y hr7_0i hr7_0a
      hausFrei hfreiCg hcg hvCg hv
  rw [precRumpfLaenge] at hpcR
  have hbleibR := laufBleibtVorEnde (precRumpf cgBlk aus frei) r7_0 kR rR hrunR
    (by rw [hpcR, precRumpfLaenge])
  have hvR : VerschiebbaresProgramm (precRumpf cgBlk aus frei) := by
    rw [← verschiebbarVonNull]
    exact verschiebbarPrecRumpf 0 cgBlk aus frei hvCg
  have hshiftR := laufMitPc (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)])
    (precRumpf cgBlk aus frei) (precEnde cgBlk frei) hvR r7_0 kR hbleibR
  have hpreLen : (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]).length = 8 := by
    simp only [List.length_append, precCheckLaenge, List.length_cons, List.length_nil]
  rw [hpreLen] at hshiftR
  have hshiftR' : (Schritt prog)^[kR] (some r7) =
      some (mitPc 8 rR) := by
    change (Schritt (precSchleife cgBlk aus frei))^[kR] (some r7) = some (mitPc 8 rR)
    simpa only [precSchleife, hmitPc7, hrunR] using hshiftR
  have hrunMitte : (Schritt prog)^[kR + 8] (some r) = some (mitPc 8 rR) := by
    rw [Function.iterate_add_apply, hrun8, hshiftR']
  let rE : Rahmen := mitPc 8 rR
  have hrEpc : rE.pc = cgBlk.length + 96 := by
    change 8 + rR.pc = cgBlk.length + 96
    rw [hpcR]
    omega
  have hrEy : rE.temp (frei + 2) = some (natVal y) := by
    change rR.temp (frei + 2) = some (natVal y)
    rw [hpresR (frei + 2) (by omega) (by omega) (by omega) (by omega)]
    exact hr7_0y
  let rE1 : Rahmen := rE.schreibe (frei + 3) (some (natVal 1))
  have eE0 : (Schritt prog)^[1] (some rE) = some rE1 := by
    have g : prog[rE.pc]? = some (.literal (frei + 3) 1) := by
      rw [hrEpc]
      change (precSchleife cgBlk aus frei)[cgBlk.length + 96]? = some (.literal (frei + 3) 1)
      exact precSchleifeBeiEnde0 cgBlk aus frei
    change (Schritt prog)^[1] (some rE) = some (rE.schreibe (frei + 3) (some (natVal 1)))
    simpa only [Rahmen.schreibe, Function.iterate_one] using (schrittLiteral prog rE rE.pc (frei + 3) 1 rfl g)
  have hpcE1 : rE1.pc = cgBlk.length + 97 := by
    change rE.pc + 1 = cgBlk.length + 97
    rw [hrEpc]
  have hrE1s : rE1.temp (frei + 2) = some (natVal y) := by
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) (frei + 2) = some (natVal y)
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 3))]
    exact hrEy
  have hrE1e : rE1.temp (frei + 3) = some (natVal 1) := by
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) (frei + 3) = some (natVal 1)
    rw [updateHit]
  have hza : rE1.zahl (frei + 2) = some ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩ :=
    zahlOfNat _ _ _ hrE1s
  have hzb : rE1.zahl (frei + 3) = some ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ :=
    zahlOfNat _ _ _ hrE1e
  have eE1 := schrittBinaer prog rE1 (cgBlk.length + 97) (frei + 2) .add
    ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩
    ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ hpcE1 hza hzb
  let rE2 : Rahmen := rE1.schreibe (frei + 2) (some (precAddWert y))
  have eE1' : (Schritt prog)^[1] (some rE1) = some rE2 := by
    change (Schritt prog)^[1] (some rE1) =
      some (rE1.schreibe (frei + 2) (some (precAddWert y)))
    simpa only [Rahmen.schreibe, Function.iterate_one, precAddWert] using eE1
  have hpcE2 : rE2.pc = cgBlk.length + 98 := by
    change rE1.pc + 1 = cgBlk.length + 98
    rw [hpcE1]
  have g2 : prog[rE2.pc]? = some (.zurueckSprung (cgBlk.length + 98)) := by
    rw [hpcE2]
    change (precSchleife cgBlk aus frei)[cgBlk.length + 98]? =
      some (.zurueckSprung (cgBlk.length + 98))
    exact precSchleifeBeiEnde2 cgBlk aus frei
  have eE2 : (Schritt prog)^[1] (some rE2) = some { rE2 with pc := rE2.pc - (cgBlk.length + 98) } :=
    schrittZurueck prog rE2 (cgBlk.length + 98) (cgBlk.length + 98) hpcE2 g2
  let rEnd : Rahmen := { rE2 with pc := 0 }
  have eE2' : (Schritt prog)^[1] (some rE2) = some rEnd := by
    rw [eE2]
    congr 1
    rw [hpcE2]
    rfl
  have hrunEnde : (Schritt prog)^[3] (some rE) = some rEnd := by
    rw [show (3 : Nat) = 1 + 1 + 1 by omega, Function.iterate_add_apply,
      Function.iterate_add_apply, eE0, eE1', eE2']
  refine ⟨3 + kR + 8, rEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hrunMitte, hrunEnde]
  · rfl
  · change rE2.temp (frei + 2) = some (natVal (y + 1))
    change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) (frei + 2) =
      some (natVal (y + 1))
    rw [updateHit]
    congr 1
    exact packAddSucc y
  · change rE2.temp aus = some (natVal v)
    change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) aus = some (natVal v)
    rw [updateMiss _ _ _ _ (by omega)]
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) aus = some (natVal v)
    rw [updateMiss _ _ _ _ (by omega)]
    change rR.temp aus = some (natVal v)
    exact hrRaus
  · intro s hs hne
    change rE2.temp s = r.temp s
    change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) s = r.temp s
    rw [updateMiss _ _ _ _ (by omega)]
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) s = r.temp s
    rw [updateMiss _ _ _ _ (by omega)]
    change rR.temp s = r.temp s
    rw [hpresR s (by omega) hne (by omega) (by omega)]
    change rC.temp s = r.temp s
    rw [hCpres s (by omega) (by omega)]
  · change rE2.lokale = r.lokale
    exact hlokR.trans hlokC
  · change rE2.rueckgabe = r.rueckgabe
    exact hrueckR.trans hrueckC
  · change rE2.stopp = r.stopp
    exact hstoppR.trans hstoppC

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
