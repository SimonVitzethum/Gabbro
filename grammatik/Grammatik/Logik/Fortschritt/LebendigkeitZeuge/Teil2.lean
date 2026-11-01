module

public import Grammatik.Logik.Fortschritt.Lebendigkeit
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenLauf
public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik
set_option linter.unusedVariables false

/-- **The run, tabled.** -/
theorem lLauf : ∃ Ms : Nat → RufMaschineG mD,
    Ms 0 = RufStartG mP mSp mInit ∧
    (∀ j u, lAkt j = some u → RufSchrittG mP mO 0 (Ms j) u (Ms (j + 1))) ∧
    (∀ j, 23 ≤ j → Ms j = Ms 23) ∧
    (∀ j, BefundZ ((Ms j).faeden 0) (lO0 j) (lA0 j) (lF0 j)) ∧
    (∀ j, BefundZ ((Ms j).faeden 1) (lO1 j) (lA1 j) (lF1 j)) ∧
    (∀ j u, 2 ≤ u → (Ms j).faeden u = (RufStartG mP mSp mInit).faeden u) := by
  -- the prefix (as `mVorlauf`, every machine kept)
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP) (O := mO) (passes := 0) mStart0
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := mP) (O := mO) (passes := 0) hZ2.1 mLocksA mRestA
    .nil rfl rfl
  have h1_3 : M3.faeden 1 = (RufStartG mP mSp mInit).faeden 1 := by
    rw [rufSchrittG_fremd s3 1 (by decide), rufSchrittG_fremd s2 1 (by decide),
      rufSchrittG_fremd s1 1 (by decide)]
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := mP) (O := mO) (passes := 0) (h1_3.trans mStart1)
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M5, s5, hZ5⟩ := w_endeEntf (P := mP) (O := mO) (passes := 0) hZ4.1 mLocksB
    (.ret .empty List.Perm.nil) .nil rfl rfl
  have h0_5 : M5.faeden 0 = M3.faeden 0 := by
    rw [rufSchrittG_fremd s5 0 (by decide), rufSchrittG_fremd s4 0 (by decide)]
  have hr5 : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3)
      s4) s5
  -- the idle threads never move
  have hI5 : ∀ u, 2 ≤ u → M5.faeden u = (RufStartG mP mSp mInit).faeden u := by
    intro u hu
    have h0 : u ≠ 0 := faden_ne_klein hu (by decide)
    have h1 : u ≠ 1 := faden_ne_klein hu (by decide)
    rw [rufSchrittG_fremd s5 u h1, rufSchrittG_fremd s4 u h1, rufSchrittG_fremd s3 u h0,
      rufSchrittG_fremd s2 u h0, rufSchrittG_fremd s1 u h0]
  -- held sets of the prefix
  have o0_1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur]; refine mBlattOffen.trans ?_; exact mStart_offen 0
  have o0_2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur]; refine mBlattOffen.trans ?_; exact o0_1
  have o0_3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur]; exact o0_2
  have o1_4 : offen (M4.faeden 1).spur = [] := by
    rw [hZ4.spur]; refine mBlattOffen.trans ?_
    show offen (M3.faeden 1).spur = []
    rw [h1_3]; exact mStart_offen 1
  have o1_5 : offen (M5.faeden 1).spur = [] := by
    rw [hZ5.spur]; exact o1_4
  -- thread 0's critical section
  have hfrei5 : RufFreiG M5 0 () := mFrei fun g hg => by
    by_cases hg1 : g = 1
    · subst hg1; exact o1_5
    · rw [hI5 g (faden_ge2 hg hg1)]; exact mStart_offen g
  obtain ⟨N1, N2, N3, N4, N5, N6, N7, N8, a1, a2, a3, a4, a5, a6, a7, a8,
      b1, b2, b3, b4, b5, b6, b7, σa, loga, hza, hoffa⟩ :=
    lAbschnitt (M := M5) 0 mHauptA .nil (mSp.welt []) _ m30 mHpSetzeA (fun _ h => nomatch h)
      (.ende mRestA) (M5.speicher.welt (M2.weltVon 0).spur) ⟨h0_5.trans hZ3.1, rfl⟩ o0_2 hfrei5
  -- thread 0 finishes: call `pruefeA`, return
  obtain ⟨Mc, sc, hZc⟩ := w_rufEnde (P := mP) (O := mO) (passes := 0) hza.1 mPruefeA .nil
    mHpPruefe rfl (.ret .empty List.Perm.nil) .nil rfl (mHeld0 _)
  obtain ⟨Md, sd, hGd⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZc.1 _ [] rfl
    (PopArt.wie rfl) .empty List.Perm.nil .nil rfl (mHeld0 _)
  have o0_8 : offen (N8.faeden 0).spur = [] := by rw [hza.spur]; exact hoffa
  have o0_c : offen (Mc.faeden 0).spur = [] := by
    rw [hZc.spur, (Erw.lese _ _ _).offen]; exact o0_8
  have o0_d : offen (Md.faeden 0).spur = [] := by
    rw [hGd.1]; exact ((Erw.lese _ _ _).offen).trans o0_c
  -- thread 1 and the idle threads did not move since M5
  have hne10 : (1 : Faden) ≠ 0 := by decide
  have hU1 : ∀ X : RufMaschineG mD, X.faeden 1 = M5.faeden 1 → ∀ Y, RufSchrittG mP mO 0 X 0 Y →
      Y.faeden 1 = M5.faeden 1 := fun X hX Y hs => (rufSchrittG_fremd hs 1 hne10).trans hX
  have f1_6 := hU1 _ rfl _ a1
  have f1_7 := hU1 _ f1_6 _ a2
  have f1_8 := hU1 _ f1_7 _ a3
  have f1_9 := hU1 _ f1_8 _ a4
  have f1_10 := hU1 _ f1_9 _ a5
  have f1_11 := hU1 _ f1_10 _ a6
  have f1_12 := hU1 _ f1_11 _ a7
  have f1_13 := hU1 _ f1_12 _ a8
  have f1_14 := hU1 _ f1_13 _ sc
  have f1_15 := hU1 _ f1_14 _ sd
  have hUI : ∀ (X : RufMaschineG mD) (w : Faden), (∀ u, 2 ≤ u → X.faeden u = M5.faeden u) →
      ∀ Y, RufSchrittG mP mO 0 X w Y → w ≤ 1 → ∀ u, 2 ≤ u → Y.faeden u = M5.faeden u :=
    fun X w hX Y hs hw u hu => (rufSchrittG_fremd hs u (faden_ne_klein hu hw)).trans (hX u hu)
  have i6 := hUI _ 0 (fun _ _ => rfl) _ a1 (by decide)
  have i7 := hUI _ 0 i6 _ a2 (by decide)
  have i8 := hUI _ 0 i7 _ a3 (by decide)
  have i9 := hUI _ 0 i8 _ a4 (by decide)
  have i10 := hUI _ 0 i9 _ a5 (by decide)
  have i11 := hUI _ 0 i10 _ a6 (by decide)
  have i12 := hUI _ 0 i11 _ a7 (by decide)
  have i13 := hUI _ 0 i12 _ a8 (by decide)
  have i14 := hUI _ 0 i13 _ sc (by decide)
  have i15 := hUI _ 0 i14 _ sd (by decide)
  -- thread 1's critical section
  have hz1d : ZustandG Md 1 [] mHauptB .nil (mSp.welt []) _ .nil
      (.dann (.cons mLocksB .nil) (.ende (.ret .empty List.Perm.nil)))
      (Md.speicher.welt (M4.weltVon 1).spur) := ⟨f1_15.trans hZ5.1, rfl⟩
  have hfreid : RufFreiG Md 1 () := mFrei fun g hg => by
    by_cases hg0 : g = 0
    · subst hg0; exact o0_d
    · rw [i15 g (faden_ge2 hg0 hg), hI5 g (faden_ge2 hg0 hg)]; exact mStart_offen g
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, c1, c2, c3, c4, c5, c6, c7, c8,
      d1, d2, d3, d4, d5, d6, d7, σb, logb, hzb, hoffb⟩ :=
    lAbschnitt (M := Md) 1 mHauptB .nil (mSp.welt []) _ m70 mHpSetzeB (fun _ h => nomatch h)
      (.ende (.ret .empty List.Perm.nil)) _ hz1d o1_4 hfreid
  have hne01 : (0 : Faden) ≠ 1 := by decide
  have hU0 : ∀ X : RufMaschineG mD, X.faeden 0 = Md.faeden 0 → ∀ Y, RufSchrittG mP mO 0 X 1 Y →
      Y.faeden 0 = Md.faeden 0 := fun X hX Y hs => (rufSchrittG_fremd hs 0 hne01).trans hX
  have f0_16 := hU0 _ rfl _ c1
  have f0_17 := hU0 _ f0_16 _ c2
  have f0_18 := hU0 _ f0_17 _ c3
  have f0_19 := hU0 _ f0_18 _ c4
  have f0_20 := hU0 _ f0_19 _ c5
  have f0_21 := hU0 _ f0_20 _ c6
  have f0_22 := hU0 _ f0_21 _ c7
  have f0_23 := hU0 _ f0_22 _ c8
  have i16 := hUI _ 1 i15 _ c1 (by decide)
  have i17 := hUI _ 1 i16 _ c2 (by decide)
  have i18 := hUI _ 1 i17 _ c3 (by decide)
  have i19 := hUI _ 1 i18 _ c4 (by decide)
  have i20 := hUI _ 1 i19 _ c5 (by decide)
  have i21 := hUI _ 1 i20 _ c6 (by decide)
  have i22 := hUI _ 1 i21 _ c7 (by decide)
  have i23 := hUI _ 1 i22 _ c8 (by decide)
  -- the tables, machine by machine
  have B0_0 : BefundZ ((RufStartG mP mSp mInit).faeden 0) [] false false :=
    befund_von mStart0 (mStart_offen 0) rfl kein_fertig kein_halt_leer
  have B0_1 : BefundZ (M1.faeden 0) [] false false :=
    befund_von hZ1.1 o0_1 rfl kein_fertig kein_halt_leer
  have B0_2 : BefundZ (M2.faeden 0) [] false false :=
    befund_von hZ2.1 o0_2 rfl kein_fertig kein_halt_leer
  have B0_3 : BefundZ (M3.faeden 0) [] true false :=
    befund_von hZ3.1 o0_3 rfl kein_fertig kein_halt_leer
  have B0_13 : BefundZ (N8.faeden 0) [] false false :=
    befund_von hza.1 o0_8 rfl kein_fertig kein_halt_leer
  have B0_14 : BefundZ (Mc.faeden 0) [] false false :=
    befund_von hZc.1 o0_c rfl kein_fertig kein_halt_leer
  have B0_15 : BefundZ (Md.faeden 0) [] false true :=
    befund_von hGd.1 o0_d rfl (fun _ => ⟨rfl, rfl⟩) kein_halt_leer
  have B1_0 : BefundZ ((RufStartG mP mSp mInit).faeden 1) [] false false :=
    befund_von mStart1 (mStart_offen 1) rfl kein_fertig kein_halt_leer
  have B1_4 : BefundZ (M4.faeden 1) [] false false :=
    befund_von hZ4.1 o1_4 rfl kein_fertig kein_halt_leer
  have B1_5 : BefundZ (M5.faeden 1) [] true false :=
    befund_von hZ5.1 o1_5 rfl kein_fertig kein_halt_leer
  have B1_23 : BefundZ (P8.faeden 1) [] false true := by
    refine befund_von hzb.1 (by rw [hzb.spur]; exact hoffb) rfl (fun _ => ⟨rfl, rfl⟩)
      kein_halt_leer
  -- the run
  refine ⟨fun j => if 23 ≤ j then P8 else [RufStartG mP mSp mInit, M1, M2, M3, M4, M5,
    N1, N2, N3, N4, N5, N6, N7, N8, Mc, Md, P1, P2, P3, P4, P5, P6, P7, P8].getD j P8,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j u hj
    match j, hj with
    | 0, h => cases h; exact s1
    | 1, h => cases h; exact s2
    | 2, h => cases h; exact s3
    | 3, h => cases h; exact s4
    | 4, h => cases h; exact s5
    | 5, h => cases h; exact a1
    | 6, h => cases h; exact a2
    | 7, h => cases h; exact a3
    | 8, h => cases h; exact a4
    | 9, h => cases h; exact a5
    | 10, h => cases h; exact a6
    | 11, h => cases h; exact a7
    | 12, h => cases h; exact a8
    | 13, h => cases h; exact sc
    | 14, h => cases h; exact sd
    | 15, h => cases h; exact c1
    | 16, h => cases h; exact c2
    | 17, h => cases h; exact c3
    | 18, h => cases h; exact c4
    | 19, h => cases h; exact c5
    | 20, h => cases h; exact c6
    | 21, h => cases h; exact c7
    | 22, h => cases h; exact c8
    | j + 23, h => exact absurd (lAkt_none_von h) (by omega)
  · intro j hj
    show (if 23 ≤ j then P8 else _) = (if 23 ≤ 23 then P8 else _)
    rw [if_pos hj, if_pos (Nat.le_refl 23)]
  · intro j
    rcases Nat.lt_or_ge j 23 with h23 | h23
    · match j, h23 with
      | 0, _ => exact B0_0
      | 1, _ => exact B0_1
      | 2, _ => exact B0_2
      | 3, _ => exact B0_3
      | 4, _ => exact befund_gleich (rufSchrittG_fremd s4 0 (by decide)) B0_3
      | 5, _ => exact befund_gleich h0_5 B0_3
      | 6, _ => exact b1
      | 7, _ => exact b2
      | 8, _ => exact b3
      | 9, _ => exact b4
      | 10, _ => exact b5
      | 11, _ => exact b6
      | 12, _ => exact b7
      | 13, _ => exact B0_13
      | 14, _ => exact B0_14
      | 15, _ => exact B0_15
      | 16, _ => exact befund_gleich f0_16 B0_15
      | 17, _ => exact befund_gleich f0_17 B0_15
      | 18, _ => exact befund_gleich f0_18 B0_15
      | 19, _ => exact befund_gleich f0_19 B0_15
      | 20, _ => exact befund_gleich f0_20 B0_15
      | 21, _ => exact befund_gleich f0_21 B0_15
      | 22, _ => exact befund_gleich f0_22 B0_15
      | j + 23, h => exact absurd h (by omega)
    · show BefundZ ((if 23 ≤ j then P8 else _).faeden 0) _ _ _
      rw [if_pos h23]
      have t1 : lO0 j = [] := by simp only [lO0]; rw [if_neg (show ¬ (6 ≤ j ∧ j ≤ 11) by omega)]
      have t2 : lA0 j = false := by simp only [lA0]; exact decide_eq_false (by omega)
      have t3 : lF0 j = true := by simp only [lF0]; exact decide_eq_true (by omega)
      rw [t1, t2, t3]
      exact befund_gleich f0_23 B0_15
  · intro j
    rcases Nat.lt_or_ge j 23 with h23 | h23
    · match j, h23 with
      | 0, _ => exact B1_0
      | 1, _ => exact befund_gleich (rufSchrittG_fremd s1 1 (by decide)) B1_0
      | 2, _ => exact befund_gleich ((rufSchrittG_fremd s2 1 (by decide)).trans
          (rufSchrittG_fremd s1 1 (by decide))) B1_0
      | 3, _ => exact befund_gleich h1_3 B1_0
      | 4, _ => exact B1_4
      | 5, _ => exact B1_5
      | 6, _ => exact befund_gleich f1_6 B1_5
      | 7, _ => exact befund_gleich f1_7 B1_5
      | 8, _ => exact befund_gleich f1_8 B1_5
      | 9, _ => exact befund_gleich f1_9 B1_5
      | 10, _ => exact befund_gleich f1_10 B1_5
      | 11, _ => exact befund_gleich f1_11 B1_5
      | 12, _ => exact befund_gleich f1_12 B1_5
      | 13, _ => exact befund_gleich f1_13 B1_5
      | 14, _ => exact befund_gleich f1_14 B1_5
      | 15, _ => exact befund_gleich f1_15 B1_5
      | 16, _ => exact d1
      | 17, _ => exact d2
      | 18, _ => exact d3
      | 19, _ => exact d4
      | 20, _ => exact d5
      | 21, _ => exact d6
      | 22, _ => exact d7
      | j + 23, h => exact absurd h (by omega)
    · show BefundZ ((if 23 ≤ j then P8 else _).faeden 1) _ _ _
      rw [if_pos h23]
      have t1 : lO1 j = [] := by simp only [lO1]; rw [if_neg (show ¬ (16 ≤ j ∧ j ≤ 21) by omega)]
      have t2 : lA1 j = false := by simp only [lA1]; exact decide_eq_false (by omega)
      have t3 : lF1 j = true := by simp only [lF1]; exact decide_eq_true (by omega)
      rw [t1, t2, t3]
      exact B1_23
  · intro j u hu
    have hu0 : u ≠ 0 := faden_ne_klein hu (by decide)
    have hu1 : u ≠ 1 := faden_ne_klein hu (by decide)
    have hI3 : ∀ w, 2 ≤ w → M3.faeden w = (RufStartG mP mSp mInit).faeden w := by
      intro w hw
      rw [rufSchrittG_fremd s3 w (faden_ne_klein hw (by decide)),
        rufSchrittG_fremd s2 w (faden_ne_klein hw (by decide)),
        rufSchrittG_fremd s1 w (faden_ne_klein hw (by decide))]
    rcases Nat.lt_or_ge j 23 with h23 | h23
    · match j, h23 with
      | 0, _ => rfl
      | 1, _ => exact rufSchrittG_fremd s1 u hu0
      | 2, _ => exact (rufSchrittG_fremd s2 u hu0).trans (rufSchrittG_fremd s1 u hu0)
      | 3, _ => exact hI3 u hu
      | 4, _ => exact (rufSchrittG_fremd s4 u hu1).trans (hI3 u hu)
      | 5, _ => exact hI5 u hu
      | 6, _ => exact (i6 u hu).trans (hI5 u hu)
      | 7, _ => exact (i7 u hu).trans (hI5 u hu)
      | 8, _ => exact (i8 u hu).trans (hI5 u hu)
      | 9, _ => exact (i9 u hu).trans (hI5 u hu)
      | 10, _ => exact (i10 u hu).trans (hI5 u hu)
      | 11, _ => exact (i11 u hu).trans (hI5 u hu)
      | 12, _ => exact (i12 u hu).trans (hI5 u hu)
      | 13, _ => exact (i13 u hu).trans (hI5 u hu)
      | 14, _ => exact (i14 u hu).trans (hI5 u hu)
      | 15, _ => exact (i15 u hu).trans (hI5 u hu)
      | 16, _ => exact (i16 u hu).trans (hI5 u hu)
      | 17, _ => exact (i17 u hu).trans (hI5 u hu)
      | 18, _ => exact (i18 u hu).trans (hI5 u hu)
      | 19, _ => exact (i19 u hu).trans (hI5 u hu)
      | 20, _ => exact (i20 u hu).trans (hI5 u hu)
      | 21, _ => exact (i21 u hu).trans (hI5 u hu)
      | 22, _ => exact (i22 u hu).trans (hI5 u hu)
      | j + 23, h => exact absurd h (by omega)
    · show (if 23 ≤ j then P8 else _).faeden u = _
      rw [if_pos h23]
      exact (i23 u hu).trans (hI5 u hu)

/-! ## 4. The tables, read as facts about machine G -/

section Tafel

variable {Ms : Nat → RufMaschineG mD}
  (hB0 : ∀ j, BefundZ ((Ms j).faeden 0) (lO0 j) (lA0 j) (lF0 j))
  (hB1 : ∀ j, BefundZ ((Ms j).faeden 1) (lO1 j) (lA1 j) (lF1 j))
  (hI : ∀ j u, 2 ≤ u → (Ms j).faeden u = (RufStartG mP mSp mInit).faeden u)

include hI in
theorem lRuhe_j (j : Nat) (u : Faden) (hu : 2 ≤ u) :
    BefundZ ((Ms j).faeden u) [] false true :=
  befund_gleich (hI j u hu) (lRuheBefund u hu)

theorem befund_an {M : RufMaschineG mD} {u : Faden} {o : List Unit} {a f : Bool}
    (hb : BefundZ (M.faeden u) o a f) (L : Unit) : AnSperre M u L ↔ a = true := by
  cases L
  constructor
  · intro hA
    have hk := (anSperre_kopf hA).symm.trans hb.kopf
    cases a
    · cases hk
    · rfl
  · intro ha
    subst ha
    exact anSperre_of_kopf hb.kopf

theorem befund_nicht_bereit {M : RufMaschineG mD} {u : Faden} {o : List Unit} {a : Bool}
    (hb : BefundZ (M.faeden u) o a true) : ¬ Bereit mP mO 0 M u :=
  fun ⟨_, hs⟩ => ende_ret_kein_schritt (hb.fertig rfl).1 (hb.fertig rfl).2 hs

include hB0 hB1 hI in
/-- Who holds the lock when. -/
theorem lHaelt {j : Nat} {u : Faden} {L : Unit} (h : L ∈ offen ((Ms j).faeden u).spur) :
    (u = 0 ∧ 6 ≤ j ∧ j ≤ 11) ∨ (u = 1 ∧ 16 ≤ j ∧ j ≤ 21) := by
  by_cases h0 : u = 0
  · subst h0
    rw [(hB0 j).off] at h
    left
    refine ⟨rfl, ?_⟩
    unfold lO0 at h
    by_cases hc : 6 ≤ j ∧ j ≤ 11
    · exact hc
    · rw [if_neg hc] at h; exact absurd h List.not_mem_nil
  · by_cases h1 : u = 1
    · subst h1
      rw [(hB1 j).off] at h
      right
      refine ⟨rfl, ?_⟩
      unfold lO1 at h
      by_cases hc : 16 ≤ j ∧ j ≤ 21
      · exact hc
      · rw [if_neg hc] at h; exact absurd h List.not_mem_nil
    · rw [(lRuhe_j hI j u (faden_ge2 h0 h1)).off] at h
      exact absurd h List.not_mem_nil

include hB0 hB1 hI in
/-- Who stands at `locks` when. -/
theorem lAn {j : Nat} {u : Faden} {L : Unit} (h : AnSperre (Ms j) u L) :
    (u = 0 ∧ 3 ≤ j ∧ j ≤ 5) ∨ (u = 1 ∧ 5 ≤ j ∧ j ≤ 15) := by
  by_cases h0 : u = 0
  · subst h0
    have := (befund_an (hB0 j) L).1 h
    simp only [lA0, decide_eq_true_eq] at this
    exact Or.inl ⟨rfl, this⟩
  · by_cases h1 : u = 1
    · subst h1
      have := (befund_an (hB1 j) L).1 h
      simp only [lA1, decide_eq_true_eq] at this
      exact Or.inr ⟨rfl, this⟩
    · have := (befund_an (lRuhe_j hI j u (faden_ge2 h0 h1)) L).1 h
      cases this

end Tafel

/-! ## 5. The witness -/

set_option maxHeartbeats 4000000 in
end Gabbro.Grammatik
