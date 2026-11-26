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

/-- The check and the not-taken conditional of one iteration advance the
    program counter from zero to eight without touching any slot outside the
    two comparison slots. -/
theorem precCheckSprungLauf (cgBlk : List Befehl) (aus frei y k : Nat) (r : Rahmen)
    (hpc : r.pc = 0) (hy : r.temp (frei + 2) = some (natVal y))
    (hk : r.temp (frei + 1) = some (natVal k)) (hyk : y < k) :
    ∃ r7 : Rahmen, (Schritt (precSchleife cgBlk aus frei))^[8] (some r) = some r7 ∧
      r7.pc = 8 ∧
      (∀ s, s ≠ frei + 6 → s ≠ frei + 7 → r7.temp s = r.temp s) ∧
      r7.lokale = r.lokale ∧ r7.rueckgabe = r.rueckgabe ∧ r7.stopp = r.stopp := by
  obtain ⟨rC, hrunC, hpcC, hCb, hCk, hCpres, hlokC, hrueckC, hstoppC⟩ :=
    precCheckLauf r frei y k hpc hy hk
  have hbleibC := laufBleibtVorEnde (precCheck frei) r 7 rC hrunC hpcC
  have hrunC' : (Schritt (precSchleife cgBlk aus frei))^[7] (some r) = some rC := by
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
  have eJump : (Schritt (precSchleife cgBlk aus frei))^[1] (some rC) =
      some { rC with pc := rC.pc + 1 } := by
    exact schrittSpringeWennFalsch (precSchleife cgBlk aus frei) rC 7 (frei + 6)
      false true (cgBlk.length + 92) hpcC hCbool (by decide)
      (precSchleifeBei7 cgBlk aus frei)
  let r7 : Rahmen := { rC with pc := 8 }
  have eJump' : (Schritt (precSchleife cgBlk aus frei))^[1] (some rC) = some r7 := by
    rw [eJump]
    congr 1
    rw [hpcC]
  refine ⟨r7, ?_, rfl, ?_, hlokC, hrueckC, hstoppC⟩
  · rw [show (8 : Nat) = 1 + 7 by omega, Function.iterate_add_apply, hrunC', eJump']
  · intro s hs6 hs7
    change rC.temp s = r.temp s
    exact hCpres s hs6 hs7

/-- The literal and the increment of the back edge, run inside the whole loop. -/
theorem precEndeZweiSchritte (cgBlk : List Befehl) (aus frei y : Nat) (rE : Rahmen)
    (hrEpc : rE.pc = cgBlk.length + 96)
    (hy : rE.temp (frei + 2) = some (natVal y)) :
    ∃ rE2 : Rahmen, (Schritt (precSchleife cgBlk aus frei))^[2] (some rE) = some rE2 ∧
      rE2.pc = cgBlk.length + 98 ∧
      rE2.temp (frei + 2) = some (natVal (y + 1)) ∧
      rE2.temp (frei + 3) = some (natVal 1) ∧
      (∀ s, s ≠ frei + 2 → s ≠ frei + 3 → rE2.temp s = rE.temp s) ∧
      rE2.lokale = rE.lokale ∧ rE2.rueckgabe = rE.rueckgabe ∧ rE2.stopp = rE.stopp := by
  let prog := precSchleife cgBlk aus frei
  let rE1 : Rahmen := rE.schreibe (frei + 3) (some (natVal 1))
  have eE0 : (Schritt prog)^[1] (some rE) = some rE1 := by
    have g : prog[rE.pc]? = some (.literal (frei + 3) 1) := by
      rw [hrEpc]
      change (precSchleife cgBlk aus frei)[cgBlk.length + 96]? = some (.literal (frei + 3) 1)
      exact precSchleifeBeiEnde0 cgBlk aus frei
    change (Schritt prog)^[1] (some rE) = some (rE.schreibe (frei + 3) (some (natVal 1)))
    simpa only [Rahmen.schreibe, Function.iterate_one] using
      (schrittLiteral prog rE rE.pc (frei + 3) 1 rfl g)
  have hpcE1 : rE1.pc = cgBlk.length + 97 := by
    change rE.pc + 1 = cgBlk.length + 97
    rw [hrEpc]
  have hrE1s : rE1.temp (frei + 2) = some (natVal y) := by
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) (frei + 2) = some (natVal y)
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (2 : Nat) ≠ 3))]
    exact hy
  have hrE1e : rE1.temp (frei + 3) = some (natVal 1) := by
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) (frei + 3) = some (natVal 1)
    rw [updateHit]
  have hza : rE1.zahl (frei + 2) = some ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩ :=
    zahlOfNat _ _ _ hrE1s
  have hzb : rE1.zahl (frei + 3) = some ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ :=
    zahlOfNat _ _ _ hrE1e
  have g1 : prog[cgBlk.length + 97]? = some (.binaer .add (frei + 2)) := by
    change (precSchleife cgBlk aus frei)[cgBlk.length + 97]? = some (.binaer .add (frei + 2))
    exact precSchleifeBeiEnde1 cgBlk aus frei
  have eE1 := schrittBinaer prog rE1 (cgBlk.length + 97) (frei + 2) .add
    ⟨(y : Int), (y : Int), Zahl.literal (y : Int)⟩
    ⟨(1 : Int), (1 : Int), Zahl.literal (1 : Int)⟩ hpcE1 hza hzb g1
  let rE2 : Rahmen := rE1.schreibe (frei + 2) (some (precAddWert y))
  have eE1' : (Schritt prog)^[1] (some rE1) = some rE2 := by
    change (Schritt prog)^[1] (some rE1) =
      some (rE1.schreibe (frei + 2) (some (precAddWert y)))
    simpa only [Rahmen.schreibe, Function.iterate_one, precAddWert] using eE1
  refine ⟨rE2, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · change (Schritt prog)^[2] (some rE) = some rE2
    rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply, eE0, eE1']
  · change rE1.pc + 1 = cgBlk.length + 98
    rw [hpcE1]
  · change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) (frei + 2) =
      some (natVal (y + 1))
    rw [updateHit]
    congr 1
  · change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) (frei + 3) =
      some (natVal 1)
    rw [updateMiss _ _ _ _ (addNeLinks (by decide : (3 : Nat) ≠ 2))]
    exact hrE1e
  · intro s hs2 hs3
    change (Function.update rE1.temp (frei + 2) (some (precAddWert y))) s = rE.temp s
    rw [updateMiss _ _ _ _ hs2]
    change (Function.update rE.temp (frei + 3) (some (natVal 1))) s = rE.temp s
    rw [updateMiss _ _ _ _ hs3]

/-- The back jump of the back edge returns the counter to zero. -/
theorem precEndeRueckSchritt (cgBlk : List Befehl) (aus frei : Nat) (rE2 : Rahmen)
    (hrE2pc : rE2.pc = cgBlk.length + 98) :
    (Schritt (precSchleife cgBlk aus frei))^[1] (some rE2) = some { rE2 with pc := 0 } := by
  have g : (precSchleife cgBlk aus frei)[rE2.pc]? =
      some (.zurueckSprung (cgBlk.length + 98)) := by
    rw [hrE2pc]
    exact precSchleifeBeiEnde2 cgBlk aus frei
  change Schritt (precSchleife cgBlk aus frei) (some rE2) = some { rE2 with pc := 0 }
  simp only [Schritt, g, Befehl.auswerten]
  rw [hrE2pc]
  rw [Nat.sub_self]

/-- The last three instructions of the loop increment the counter and jump back
    to its first instruction. -/
theorem precEndeGanzLauf (cgBlk : List Befehl) (aus frei y : Nat) (rE : Rahmen)
    (hrEpc : rE.pc = cgBlk.length + 96)
    (hy : rE.temp (frei + 2) = some (natVal y)) :
    ∃ rEnd : Rahmen, (Schritt (precSchleife cgBlk aus frei))^[3] (some rE) = some rEnd ∧
      rEnd.pc = 0 ∧ rEnd.temp (frei + 2) = some (natVal (y + 1)) ∧
      (∀ s, s ≠ frei + 2 → s ≠ frei + 3 → rEnd.temp s = rE.temp s) ∧
      rEnd.lokale = rE.lokale ∧ rEnd.rueckgabe = rE.rueckgabe ∧ rEnd.stopp = rE.stopp := by
  obtain ⟨rE2, hrun2, hpc2, hy2, hthree, hpres2, hlok2, hrueck2, hstopp2⟩ :=
    precEndeZweiSchritte cgBlk aus frei y rE hrEpc hy
  let rEnd : Rahmen := { rE2 with pc := 0 }
  have hrun1 : (Schritt (precSchleife cgBlk aus frei))^[1] (some rE2) = some rEnd := by
    change (Schritt (precSchleife cgBlk aus frei))^[1] (some rE2) = some { rE2 with pc := 0 }
    exact precEndeRueckSchritt cgBlk aus frei rE2 hpc2
  refine ⟨rEnd, ?_, rfl, hy2, ?_, hlok2, hrueck2, hstopp2⟩
  · rw [show (3 : Nat) = 1 + 2 by omega, Function.iterate_add_apply, hrun2, hrun1]
  · intro s hs2 hs3
    change rE2.temp s = rE.temp s
    exact hpres2 s hs2 hs3

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
  obtain ⟨r7, hrun7, hpc7, hpres7, hlok7, hrueck7, hstopp7⟩ :=
    precCheckSprungLauf cgBlk aus frei y k r hpc hy hk hyk
  let r7_0 : Rahmen := { r7 with pc := 0 }
  have hr7_0pc : r7_0.pc = 0 := rfl
  have hr7_0y : r7_0.temp (frei + 2) = some (natVal y) := by
    change r7.temp (frei + 2) = some (natVal y)
    rw [hpres7 (frei + 2) (by omega) (by omega)]
    exact hy
  have hr7_0i : r7_0.temp aus = some (natVal i) := by
    change r7.temp aus = some (natVal i)
    rw [hpres7 aus (ltNeAdd hausFrei) (ltNeAdd hausFrei)]
    exact hi
  have hr7_0a : r7_0.temp (frei + 0) = some (natVal a) := by
    change r7.temp (frei + 0) = some (natVal a)
    rw [hpres7 (frei + 0) (addNeLinks (by decide : (0 : Nat) ≠ 6))
      (addNeLinks (by decide : (0 : Nat) ≠ 7))]
    exact ha
  have hmitPc7 : mitPc 8 r7_0 = r7 := by
    change { r7 with pc := 8 + 0 } = r7
    rw [show (8 : Nat) + 0 = r7.pc by rw [hpc7]]
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
  have hshiftR' : (Schritt prog)^[kR] (some r7) = some (mitPc 8 rR) := by
    change (Schritt (precSchleife cgBlk aus frei))^[kR] (some r7) = some (mitPc 8 rR)
    simpa only [precSchleife, hmitPc7, hrunR] using hshiftR
  have hrunMitte : (Schritt prog)^[kR + 8] (some r) = some (mitPc 8 rR) := by
    rw [Function.iterate_add_apply, hrun7, hshiftR']
  let rE : Rahmen := mitPc 8 rR
  have hrEpc : rE.pc = cgBlk.length + 96 := by
    change 8 + rR.pc = cgBlk.length + 96
    rw [hpcR]
    omega
  have hrEy : rE.temp (frei + 2) = some (natVal y) := by
    change rR.temp (frei + 2) = some (natVal y)
    rw [hpresR (frei + 2) (by omega) (by omega) (by omega) (by omega)]
    exact hr7_0y
  obtain ⟨rEnd, hrunEnde, hpcEnde, hrEndY, hpresEnde, hlokEnde, hrueckEnde, hstoppEnde⟩ :=
    precEndeGanzLauf cgBlk aus frei y rE hrEpc hrEy
  refine ⟨3 + kR + 8, rEnd, ?_, hpcEnde, hrEndY, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 3 + kR + 8 = 3 + (kR + 8) by omega, Function.iterate_add_apply, hrunMitte, hrunEnde]
  · change rEnd.temp aus = some (natVal v)
    rw [hpresEnde aus (by omega) (by omega)]
    change rR.temp aus = some (natVal v)
    exact hrRaus
  · intro s hs hne
    rw [hpresEnde s (by omega) (by omega)]
    change rR.temp s = r.temp s
    rw [hpresR s (by omega) hne (by omega) (by omega)]
    change r7_0.temp s = r.temp s
    rw [hpres7 s (ltNeAdd hs) (ltNeAdd hs)]
  · change rEnd.lokale = r.lokale
    exact hlokEnde.trans (hlokR.trans hlok7)
  · change rEnd.rueckgabe = r.rueckgabe
    exact hrueckEnde.trans (hrueckR.trans hrueck7)
  · change rEnd.stopp = r.stopp
    exact hstoppEnde.trans (hstoppR.trans hstopp7)

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
