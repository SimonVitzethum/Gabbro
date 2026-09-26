/-
  File:      Grammatik/Zielsatz/InvariantenZeuge.lean -- WITNESSES for the invariant legs of
             Opus agent D (2026-09-26): `sperrWechsel`, `sperrSicht`, `invRuhe`.

  The fixture is the two-writer program `mP` of MehrfadenZeuge.lean, whose premises of the
  multi-thread flagship are proved there (`mP_zertifiziert`):

      lock () protects konto, invariant konto[0] == konto[1]      -- the lock invariant `mSI`
      table invariant privA[0] == privA[1]                        -- `D.Inv`, owed by `hauptA`
      setze(x)  holds (), writes konto[0] := x; konto[1] := x
      hauptA()  privA[0] := 7; privA[1] := 7; locks { setze(30) }; pruefeA(); return
      hauptB()  privB[0] := 5; locks { setze(70) }; return

  The legs are applied through their generic lemmas (`sperrWechsel_aus`, `sperrSicht_aus`,
  `invRuheG_aus`, Zielsatz/Invarianten.lean) with the premises `mP_zertifiziert` supplies --
  exactly the premises `ziel_aus` feeds them.

  * `lock_gebrochen_unsichtbar` -- NON-DEGENERACY of the lock legs: at a reached machine
    inside thread 0's section the lock invariant is FALSE in shared memory (`konto = [30, 0]`),
    and BY THE LEG no step of thread 1 from there accesses `konto`.
  * `lock_erwerb_sieht_invariante` -- after thread 0's section (and thread 0 finished), thread
    1's acquire of the lock starts from, and ends in, a memory with `konto[0] == konto[1]`, BY
    THE LEG `sperrWechsel`.
  * `tabelle_gebrochen` -- the table invariant is FALSE at a reached machine (`privA = [7, 0]`)
    inside `hauptA`, which owes it: `invRuhe` claims nothing there (the invariant is open).
  * `tabelle_am_eintritt` -- the ENTRY witness: thread 1 enters `setze` after thread 0 has
    finished; the invariant is CLOSED there and `privA[0] == privA[1]` holds, BY THE LEG
    `invRuhe`, at the memory of that entry and at the entry world of `setze`'s frame.
-/
import Grammatik.Zielsatz.Invarianten
import Grammatik.MehrfadenLauf

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. The fixture's premises for the invariant legs -/

theorem mD_gruende (g : mD.Fn) : mD.gruende g = 0 := by cases g <;> rfl

/-- No function of `mD` has a reason: the reason-return leg holds vacuously. -/
theorem mP_invGrund (M : RufMaschineG mD) : InvAmGrundG mP M :=
  fun _ _ _ g _ r _ _ _ => absurd r.2 (by have := mD_gruende g; omega)

theorem mP_hIR : ∀ M, RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M →
    InvAmOrtG mP M ∧ InvAmGrundG mP M ∧ StartEndeG mP M ∧ KeinStartGrundG M :=
  fun M hr => ⟨(mP_zertifiziert 0 M hr).1.2, mP_invGrund M, (mP_zertifiziert 0 M hr).2.1,
    (mP_zertifiziert 0 M hr).2.2⟩

theorem mP_invTraeger : InvTraeger mP () := by
  intro c hc
  refine ⟨MTab.privA, List.mem_singleton_self _, ?_⟩
  revert c
  decide

theorem mP_invStart : InvHaelt mP () ((RufStartG mP mSp mInit).speicher.welt []) := rfl

/-- Only `hauptA` writes `privA`, so only `hauptA` owes the table invariant. -/
theorem mSchuldet (f : mD.Fn) (h : f ≠ mHauptA) : schuldet f () = false := by
  cases f
  · rfl
  · exact absurd rfl h
  · rfl
  · rfl
  · rfl

/-! ## 2. Broken states: the table invariant inside `hauptA`, the lock invariant inside a
    section -/

/-- **The table invariant is BROKEN at a reached machine** -- thread 0 has written
    `privA[0] := 7` and not yet `privA[1]` -- and it is OPEN there (thread 0 is inside
    `hauptA`, which owes it), so `invRuhe` claims nothing: the leg is not vacuously true of
    every machine. -/
theorem tabelle_gebrochen : ∃ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
    ¬ InvHaelt mP () (M.speicher.welt []) ∧ ¬ InvZu M () := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP) (O := mO) (passes := 0) mStart0
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  refine ⟨M1, .schritt _ _ _ .start s1, ?_, fun hZ => ?_⟩
  · rw [hZ1.2]
    exact Bool.false_ne_true
  · have hF : ¬ FertigG M1 0 := fun h => by
      have := h.2
      rw [hZ1.1] at this
      exact Bool.false_ne_true this
    have := hZ 0 hF (M1.faeden 0).kopf List.mem_cons_self
    rw [hZ1.1] at this
    exact absurd this (by decide)

/-- **The lock invariant is BROKEN at a reached machine, and no other thread can see it.**
    Thread 0 has taken the lock, entered `setze(30)` and written `konto[0] := 30`; the memory
    has `konto = [30, 0]`, so `konto[0] == konto[1]` is FALSE there. BY THE LEG `sperrSicht`
    (and exclusivity) no step of thread 1 from that machine accesses `konto`. -/
theorem lock_gebrochen_unsichtbar : ∃ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
    mSI.inv () M.speicher = false ∧ () ∈ offen (M.faeden 0).spur ∧
    ∀ M', RufSchrittG mP mO 0 M 1 M' → ¬ ZugriffG M M' 1 (.inl MTab.konto) := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP) (O := mO) (passes := 0) mStart0
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := mP) (O := mO) (passes := 0) hZ2.1 mLocksA mRestA
    .nil rfl rfl
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur]
    show offen (M2.faeden 0).spur = []
    rw [hZ2.spur]; refine mBlattOffen.trans ?_
    show offen (M1.faeden 0).spur = []
    rw [hZ1.spur]; refine mBlattOffen.trans ?_
    exact mStart_offen 0
  have hfrei3 : RufFreiG M3 0 () := mFrei fun g hg => by
    rw [rufSchrittG_fremd s3 g hg, rufSchrittG_fremd s2 g hg, rufSchrittG_fremd s1 g hg]
    exact mStart_offen g
  obtain ⟨M4, s4, hZ4⟩ := w_locks (P := mP) (O := mO) (passes := 0) hZ3.1 ()
    _ _ _ _ _ rfl (mhg0 (by rw [← hZ3.spur]; exact hoff3)) hfrei3
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact congrArg (List.cons ()) hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_rufDann (P := mP) (O := mO) (passes := 0) hZ4.1 mSetze
    (.cons m30 .nil) mHpSetzeA rfl .nil _ _ rfl (mhgL (moff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen]; exact hoff4
  obtain ⟨M6, s6, hZ6⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ5.1
    _ _ _ rfl rfl (mhgL (moff_z hZ5 hoff5)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff6 : offen (M6.faeden 0).spur = [()] := by
    rw [hZ6.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff5
  have hr6 : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6
  have hL0 : () ∈ offen (M6.faeden 0).spur := by rw [hoff6]; exact List.mem_singleton_self _
  refine ⟨M6, hr6, ?_, hL0, fun M' hs hz => ?_⟩
  · rw [hZ6.2]
    unfold RufMaschineG.weltVon
    rw [hZ5.2]
    unfold RufMaschineG.weltVon
    rw [hZ4.2]
    unfold RufMaschineG.weltVon
    rw [hZ3.2]
    unfold RufMaschineG.weltVon
    rw [hZ2.2]
    unfold RufMaschineG.weltVon
    rw [hZ1.2]
    rfl
  · have hL1 := (sperrSicht_aus mO_gut mSI_ok mSp mInit mInit_exklusiv hr6 1 M' hs ()
      (.inl MTab.konto) (List.mem_singleton_self _)).1 hz
    exact exklusivG mO_gut mSp mInit mInit_exklusiv hr6 0 1 (by decide) () hL0 hL1

/-! ## 3. The acquire after the section, and the ENTRY once the writer is finished -/

/-- **`inv_erwerb_und_eintritt` -- the lock and the table invariant seen by the OTHER thread,
    BY THE LEGS.** Thread 0 runs its section `locks { setze(30) }` (breaking `konto[0] ==
    konto[1]` inside it, `lock_gebrochen_unsichtbar`), calls `pruefeA` and finishes (`Md`). Then
    thread 1 ACQUIRES the lock (`Md -> Me`): by `sperrWechsel` the memory before and after the
    acquire has `konto[0] == konto[1]`. Then thread 1 ENTERS `setze(70)` (`Me -> Mf`): the table
    invariant `privA[0] == privA[1]`, broken inside `hauptA` (`tabelle_gebrochen`), is CLOSED
    at `Mf` (its only writer's thread is finished) and holds, by `invRuhe`, in the memory of
    that entry and at the entry world of `setze`'s frame. -/
theorem inv_erwerb_und_eintritt : ∃ Md Me Mf : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Md ∧
    RufSchrittG mP mO 0 Md 1 Me ∧ RufSchrittG mP mO 0 Me 1 Mf ∧
    FertigG Md 0 ∧ () ∉ offen (Md.faeden 1).spur ∧ () ∈ offen (Me.faeden 1).spur ∧
    (Md.speicher.slots MTab.konto 0 ()).n = (Md.speicher.slots MTab.konto 1 ()).n ∧
    (Me.speicher.slots MTab.konto 0 ()).n = (Me.speicher.slots MTab.konto 1 ()).n ∧
    (Mf.faeden 1).kopf.f = mSetze ∧ InvZu Mf () ∧
    InvHaelt mP () (Mf.speicher.welt []) ∧ InvHaelt mP () (Mf.faeden 1).kopf.s0 ∧
    (Mf.speicher.slots MTab.privA 0 ()).n = (Mf.speicher.slots MTab.privA 1 ()).n := by
  obtain ⟨M, σ0, σ1, log0, log1, hr, hz0, hoff0, hz1, hoff1, hidle⟩ := mVorlauf
  have hfrei0 : RufFreiG M 0 () := mFrei fun g hg => by
    by_cases hg1 : g = 1
    · subst hg1; rw [hz1.spur]; exact hoff1
    · rw [hidle g hg hg1]; exact mStart_offen g
  obtain ⟨Ma, hra, hfremdA, σa, loga, hza, hoffa, _, _⟩ := mAbschnitt hr 0 mHauptA .nil
    (mSp.welt []) log0 m30 mHpSetzeA (fun _ h => nomatch h) (.ende mRestA) σ0 hz0 hoff0 hfrei0
  -- thread 0: `pruefeA()` and its return; thread 0 is then finished
  obtain ⟨Mc, sc, hZc⟩ := w_rufEnde (P := mP) (O := mO) (passes := 0) hza.1 mPruefeA .nil
    mHpPruefe rfl (.ret .keine List.Perm.nil) .nil rfl (mHeld0 _)
  have hrc : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Mc := .schritt _ _ _ hra sc
  obtain ⟨Md, sd, hGd⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZc.1 _ [] rfl
    (PopArt.wie rfl) .keine List.Perm.nil .nil rfl (mHeld0 _)
  have hrd : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Md := .schritt _ _ _ hrc sd
  have hF0 : FertigG Md 0 := ⟨by rw [hGd.1], by rw [hGd.1]; rfl⟩
  have hoffd0 : offen (Md.faeden 0).spur = [] := by
    rw [hGd.1]
    show offen ((Mc.weltVon 0).lese _ _).spur = []
    rw [(Erw.lese _ _ _).offen]
    show offen (Mc.faeden 0).spur = []
    rw [hZc.spur, (Erw.lese _ _ _).offen]
    show offen (Ma.faeden 0).spur = []
    rw [hza.spur]; exact hoffa
  have h1d : Md.faeden 1 = M.faeden 1 := by
    rw [rufSchrittG_fremd sd 1 (by decide), rufSchrittG_fremd sc 1 (by decide),
      hfremdA 1 (by decide)]
  have hoffd1 : offen (Md.faeden 1).spur = [] := by rw [h1d, hz1.spur]; exact hoff1
  have hfrei1 : RufFreiG Md 1 () := mFrei fun g hg => by
    by_cases hg0 : g = 0
    · subst hg0; exact hoffd0
    · rw [rufSchrittG_fremd sd g hg0, rufSchrittG_fremd sc g hg0, hfremdA g hg0,
        hidle g hg0 hg]
      exact mStart_offen g
  -- thread 1: the ACQUIRE, then the ENTRY of `setze(70)`
  obtain ⟨Me, se, hZe⟩ := w_locks (P := mP) (O := mO) (passes := 0) (h1d.trans hz1.1) ()
    _ _ _ _ _ rfl (mhg0 hoff1) hfrei1
  have hoffe : offen (Me.faeden 1).spur = [()] := by
    rw [hZe.spur]
    exact congrArg (List.cons ()) hoffd1
  have hre : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Me := .schritt _ _ _ hrd se
  obtain ⟨Mf, sf, hZf⟩ := w_rufDann (P := mP) (O := mO) (passes := 0) hZe.1 mSetze
    (.cons m70 .nil) mHpSetzeB rfl .nil _ _ rfl (mhgL (moff_z hZe hoffe)).heldIn
  have hrf : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Mf := .schritt _ _ _ hre sf
  -- the acquire, BY THE LEG
  have hn : () ∉ offen (Md.faeden 1).spur := by rw [hoffd1]; exact List.not_mem_nil
  have hj : () ∈ offen (Me.faeden 1).spur := by rw [hoffe]; exact List.mem_singleton_self _
  have hW := (sperrWechsel_aus mO_gut mSI_ok mSp mInit mInit_exklusiv
    (fun M hr => (mP_zertifiziert 0 M hr).1.1.2.1) hrd 1 Me () se).1 hn hj
  -- the table invariant is closed at the entry
  have hZu : InvZu Mf () := by
    intro t hFt F hF
    by_cases ht0 : t = 0
    · subst ht0
      refine absurd ?_ hFt
      have e : Mf.faeden 0 = Md.faeden 0 := by
        rw [rufSchrittG_fremd sf 0 (by decide), rufSchrittG_fremd se 0 (by decide)]
      exact ⟨by rw [e]; exact hF0.1, by rw [e]; exact hF0.2⟩
    · by_cases ht1 : t = 1
      · subst ht1
        rw [hZf.1] at hF
        rcases List.mem_cons.mp hF with rfl | hF
        · exact mSchuldet _ (fun h => by cases h)
        · rcases List.mem_cons.mp hF with rfl | hF
          · exact mSchuldet _ (fun h => by cases h)
          · exact absurd hF List.not_mem_nil
      · have e : Mf.faeden t = (RufStartG mP mSp mInit).faeden t := by
          rw [rufSchrittG_fremd sf t ht1, rufSchrittG_fremd se t ht1,
            rufSchrittG_fremd sd t ht0, rufSchrittG_fremd sc t ht0, hfremdA t ht0,
            hidle t ht0 ht1]
        rw [e, start_faden] at hF
        rcases List.mem_cons.mp hF with rfl | hF
        · refine mSchuldet _ ?_
          show (mInit t).1 ≠ mHauptA
          simp only [mInit, if_neg ht0, if_neg ht1]
          decide
        · exact absurd hF List.not_mem_nil
  have hI := invRuheG_aus mO_gut mSp mInit mP_hIR hrf () (List.mem_singleton_self _)
    mP_invTraeger mP_invStart hZu
  have hs0 : (Mf.speicher.welt []).speicher = (Mf.faeden 1).kopf.s0.speicher := by
    rw [speicher_welt_speicher, hZf.2, hZf.1]
  refine ⟨Md, Me, Mf, hrd, se, sf, hF0, hn, hj, of_decide_eq_true hW.1, of_decide_eq_true hW.2,
    by rw [hZf.1], hZu, hI, (invHaelt_speicher mP () hs0).mp hI, ?_⟩
  exact of_decide_eq_true hI

#print axioms Gabbro.Grammatik.Zielsatz.tabelle_gebrochen
#print axioms Gabbro.Grammatik.Zielsatz.lock_gebrochen_unsichtbar
#print axioms Gabbro.Grammatik.Zielsatz.inv_erwerb_und_eintritt

end Gabbro.Grammatik.Zielsatz
