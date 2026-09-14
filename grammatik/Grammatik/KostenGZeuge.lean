/-
  File:      Grammatik/KostenGZeuge.lean
  Subject:   WITNESSES FOR THE STEP BOUND (`KostenG.lean`): the bounds
             computed by `decide`, reached runs whose own-step counts lie
             below them, every premise of both targets holding jointly.

  * `zP` (ZielOrtZeuge.lean): `haupt` takes the lock in a `locks` block and
    calls `wrap`, which calls `lies` and `einzahlen`. On the reached run of
    `zLauf`, the frame of `wrap` in thread 1 is entered by the third step
    and returns by the tenth: 7 own steps against the bound 11; the start
    frame of `haupt` takes 12 own steps (lock, call, release) against 18.
  * `hP` (RufMaschineG.lean §9): a `retry 1` loop whose body binds a call
    and leaves; 9 own steps of the start frame against its bound.
-/

import Grammatik.KostenG
import Grammatik.ZielOrtZeuge

namespace Gabbro.Grammatik

/-! ## 1. The bounds of `zP`, computed -/

instance zD_fn_deq : DecidableEq zD.Fn := inferInstanceAs (DecidableEq ZFn)

theorem zP_tief_wrap : rufTief zP 2 zWrap = true := by decide
theorem zP_tief_haupt : rufTief zP 3 zHaupt = true := by decide
theorem zP_kosten_wrap : kostenTief zP 0 2 zWrap = 11 := by decide
theorem zP_kosten_haupt : kostenTief zP 0 3 zHaupt = 18 := by decide
/-- The callees `lies` and `einzahlen` cost 4 each; `wrap` has no call
    deeper than one, so depth 2 is its admission depth and depth 1 is not. -/
theorem zP_tief_wrap_eins : rufTief zP 1 zWrap = false := by decide

/-- A declared cost table for `zP` (what `costs <= N ops` would say). -/
def zDecl : zD.Fn → Nat
  | .ein => 4
  | .lies => 4
  | .wrap => 12
  | .haupt => 20

/-- The `K001` check holds on the complete function list. -/
theorem zP_kostenPasst : kostenPasst zP 0 zDecl zFs = true := by decide

/-- A table that is one short at `wrap` fails the check. -/
theorem zP_kostenPasst_knapp :
    kostenPasst zP 0 (fun g => if g = zWrap then 10 else zDecl g) zFs = false := by decide

/-! ## 2. The runs of `zP` -/

/-- **The runs.** The first twelve steps of `zLauf` (thread 1: `locks`,
    call `wrap`, call `lies`, bind, return, call `einzahlen`, write,
    return, return from `wrap`, close, release), as explicit counted runs:
    `lauf` from the entry of `wrap` to its return, `lauf0` from the start
    machine; then thread 0 runs five steps (`zLauf`'s thirteenth to
    seventeenth: it takes the lock thread 1 released and enters `wrap` and
    `lies`), and the whole run of 17 steps counts 12 for thread 1. -/
theorem zP_laeufe : ∃ (M3 M10 M12 M17 : RufMaschineG zD) (rho : Env zD (zD.params zWrap))
    (s0 : World zD) (lauf : SegLauf zP zO 0 M3 M10)
    (lauf0 : SegLauf zP zO 0 (RufStartG zP zSp zInit) M12)
    (lauf17 : SegLauf zP zO 0 (RufStartG zP zSp zInit) M17),
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M3 ∧
    Eintritt zP 1 zWrap rho s0 1 M3 ∧ aktivVor 1 1 lauf ∧
    (M10.faeden 1).stapel.length = 0 ∧ segZaehle lauf 1 = 7 ∧
    Eintritt zP 1 zHaupt .nil (zSp.welt []) 0 (RufStartG zP zSp zInit) ∧
    aktivVor 1 0 lauf0 ∧ segZaehle lauf0 1 = 12 ∧
    aktivVor 1 0 lauf17 ∧ segZaehle lauf17 1 = 12 ∧ segZaehle lauf17 0 = 5 := by
  have h01 := zM0_faden (1 : Faden)
  have hoff0 : offen ((RufStartG zP zSp zInit).faeden 1).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h01 zLocks zHauptRet
    .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl (hg0 hoff0)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, zM0_faden] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ2.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ3.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .keine (by rfl)) .nil rfl
    (hgL (hoff_g hG6 hoff6)).heldIn
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff6
  obtain ⟨M8, s8, hZ8⟩ := w_blatt (P := zP) (O := zO) (passes := 0) hZ7.1
    _ _ _ rfl rfl
    (hgL (hoff_z hZ7 hoff7)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff8 : offen (M8.faeden 1).spur = [()] := by
    rw [hZ8.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff7
  obtain ⟨M9, s9, hG9⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ8.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ8 hoff8)).heldIn
  have hoff9 : offen (M9.faeden 1).spur = [()] := by
    rw [hG9.1]
    exact ((Erw.lese _ _ _).offen).trans hoff8
  obtain ⟨M10, s10, hG10⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hG9.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_g hG9 hoff9)).heldIn
  obtain ⟨M11, s11, hZ11⟩ := w_dannLeer (P := zP) (O := zO) (passes := 0) hG10.1 _ .nil rfl
  obtain ⟨M12, s12, hZ12⟩ := w_freiGib (P := zP) (O := zO) (passes := 0) hZ11.1 () _ .nil rfl
  have hoff10 : offen (M10.faeden 1).spur = [()] := by
    rw [hG10.1]
    exact ((Erw.lese _ _ _).offen).trans hoff9
  have hoff12 : offen (M12.faeden 1).spur = [] := by
    rw [hZ12.spur]
    show (offen (M11.weltVon 1).spur).erase () = []
    rw [offen_weltVon, hZ11.spur, offen_weltVon, hoff10]
    rfl
  -- thread 0: take the lock thread 1 released, enter `wrap` and `lies`
  have hfremd12 : ∀ u, u ≠ 1 → M12.faeden u = zZ0 := by
    intro u hu
    rw [rufSchrittG_fremd s12 u hu, rufSchrittG_fremd s11 u hu, rufSchrittG_fremd s10 u hu,
      rufSchrittG_fremd s9 u hu, rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu,
      rufSchrittG_fremd s6 u hu, rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu,
      rufSchrittG_fremd s3 u hu, rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu, zM0_faden]
  have h00 : M12.faeden 0 = zZ0 := hfremd12 0 (by decide)
  obtain ⟨M13, s13, hZ13⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h00 zLocks zHauptRet
    .nil rfl rfl
  have hfrei13 : RufFreiG M13 0 () := by
    intro u hu
    rw [rufSchrittG_fremd s13 u hu]
    by_cases hu1 : u = 1
    · subst hu1; rw [hoff12]; exact List.not_mem_nil
    · rw [hfremd12 u hu1]; exact List.not_mem_nil
  obtain ⟨M14, s14, hZ14⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ13.1 ()
    _ _ _ _ .nil rfl (hg0 (by show offen (M12.faeden 0).spur = []; rw [h00]; rfl)) hfrei13
  have hoff14 : offen (M14.faeden 0).spur = [()] := by
    rw [hZ14.spur]
    show offen (Ereignis.nimmt () (offen (M13.weltVon 0).spur) :: (M13.weltVon 0).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ13.spur]
    show () :: offen (M12.faeden 0).spur = [()]
    rw [h00]
    rfl
  obtain ⟨M15, s15, hZ15⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ14.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ14 hoff14)).heldIn
  have hoff15 : offen (M15.faeden 0).spur = [()] := by
    rw [hZ15.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff14
  obtain ⟨M16, s16, hZ16⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ15.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ15 hoff15)).heldIn
  have hoff16 : offen (M16.faeden 0).spur = [()] := by
    rw [hZ16.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff15
  obtain ⟨M17, s17, hZ17⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ16.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ16 hoff16)).heldIn
  have h17_1 : M17.faeden 1 = M12.faeden 1 := by
    rw [rufSchrittG_fremd s17 1 (by decide), rufSchrittG_fremd s16 1 (by decide),
      rufSchrittG_fremd s15 1 (by decide), rufSchrittG_fremd s14 1 (by decide),
      rufSchrittG_fremd s13 1 (by decide)]
  refine ⟨M3, M10, M12, M17, _, _,
    .schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1
      (.schritt _ _ 1 (.schritt _ _ 1 .start s4) s5) s6) s7) s8) s9) s10,
    .schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1
      (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1
      (.schritt _ _ 1 (.schritt _ _ 1 .start s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12,
    .schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0
      (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1
      (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1 (.schritt _ _ 1
      (.schritt _ _ 1 (.schritt _ _ 1 .start s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12)
      s13) s14) s15) s16) s17,
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3,
    ⟨by rw [hZ3.1], by rw [hZ3.1]; rfl⟩, ?_, by rw [hG10.1]; rfl, rfl,
    ⟨rfl, rfl⟩, ?_, rfl, ?_, rfl, rfl⟩
  · simp only [aktivVor, true_and]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hZ3.1]; simp only [List.length_cons]; omega
    · rw [hZ4.1]; simp only [List.length_cons]; omega
    · rw [hZ5.1]; simp only [List.length_cons]; omega
    · rw [hG6.1]; simp only [List.length_cons]; omega
    · rw [hZ7.1]; simp only [List.length_cons]; omega
    · rw [hZ8.1]; simp only [List.length_cons]; omega
    · rw [hG9.1]; simp only [List.length_cons]; omega
  · simp only [aktivVor, Nat.zero_le, and_self]
  · simp only [aktivVor, Nat.zero_le, and_self]

/-! ## 3. The witnesses -/

/-- **`frame_schritte_beschraenkt_zeuge`.** On `zP`, the depth admissions
    and the bounds are computed by `decide` (`wrap`: 11 at depth 2,
    `haupt`: 18 at depth 3); on the reached run, the frame of `wrap`
    (entered by thread 1's third step, returned by its tenth) takes 7 own
    steps and the start frame of `haupt` 12 -- and `frame_schritte_beschraenkt`
    (its premises holding jointly) and `kosten_passt_deklaration` (the
    declared table `zDecl` passing the Bool check) both bound them. On the
    run extended by thread 0's five steps, thread 1's count stays 12. The
    checker's number of `wrap`'s body is 8 (two calls at 4) and the
    remainder 3 (two pushes, one `return`), `8 + 3 = 11`. -/
theorem frame_schritte_beschraenkt_zeuge :
    rufTief zP 2 zWrap = true ∧ kostenTief zP 0 2 zWrap = 11 ∧
    rufTief zP 3 zHaupt = true ∧ kostenTief zP 0 3 zHaupt = 18 ∧
    kostenPasst zP 0 zDecl zFs = true ∧
    ∃ (M3 M10 M12 M17 : RufMaschineG zD) (lauf : SegLauf zP zO 0 M3 M10)
      (lauf0 : SegLauf zP zO 0 (RufStartG zP zSp zInit) M12)
      (lauf17 : SegLauf zP zO 0 (RufStartG zP zSp zInit) M17),
      RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M3 ∧
      (M3.faeden 1).kopf.f = zWrap ∧ (M10.faeden 1).stapel.length = 0 ∧
      segZaehle lauf 1 = 7 ∧ segZaehle lauf 1 ≤ kostenTief zP 0 2 zWrap ∧
      segZaehle lauf 1 ≤ zDecl zWrap ∧
      segZaehle lauf0 1 = 12 ∧ segZaehle lauf0 1 ≤ kostenTief zP 0 3 zHaupt ∧
      segZaehle lauf0 1 ≤ zDecl zHaupt ∧
      segZaehle lauf17 1 = 12 ∧ segZaehle lauf17 0 = 5 ∧
      segZaehle lauf17 1 ≤ kostenTief zP 0 3 zHaupt ∧
      segZaehle lauf 1 ≤ kostenKE (kostenTief zP 0 1) (zP.rumpf zWrap) + zusatzE (zP.rumpf zWrap) ∧
      kostenKE (kostenTief zP 0 1) (zP.rumpf zWrap) = 8 ∧ zusatzE (zP.rumpf zWrap) = 3 := by
  obtain ⟨M3, M10, M12, M17, rho, s0, lauf, lauf0, lauf17, hr, hE, hA, hl, hz, hE0, hA0, hz0,
    hA17, hz17, hz17'⟩ := zP_laeufe
  refine ⟨zP_tief_wrap, zP_kosten_wrap, zP_tief_haupt, zP_kosten_haupt, zP_kostenPasst,
    M3, M10, M12, M17, lauf, lauf0, lauf17, hr, by rw [hE.1], hl, hz,
    frame_schritte_beschraenkt zP zO 0 1 zWrap 1 zP_tief_wrap hE lauf hA,
    kosten_passt_deklaration zP zO 0 zDecl zFs zP_kostenPasst 1 zWrap (zFs_voll _) hE lauf hA,
    hz0,
    frame_schritte_beschraenkt zP zO 0 1 zHaupt 2 zP_tief_haupt hE0 lauf0 hA0,
    kosten_passt_deklaration zP zO 0 zDecl zFs zP_kostenPasst 1 zHaupt (zFs_voll _) hE0
      lauf0 hA0,
    hz17, hz17',
    frame_schritte_beschraenkt zP zO 0 1 zHaupt 2 zP_tief_haupt hE0 lauf17 hA17,
    frame_schritte_pruefer zP zO 0 1 zWrap 1 zP_tief_wrap (by decide) hE lauf hA,
    by decide, by decide⟩

/-! ## 4. A loop -/

instance rufDF_fn_deq : DecidableEq rufDF.Fn := inferInstanceAs (DecidableEq Bool)

theorem hP_start_fn : (initF 0).1 = rufCallerF := rfl
theorem hP_tief : rufTief hP 2 (initF 0).1 = true := by decide
theorem hP_kosten : kostenTief hP 0 2 (initF 0).1 = 20 := by decide

/-- **`frame_schritte_beschraenkt_zeuge_schleife`.** The start frame of
    `hP` (thread 0, the driver `false`) runs `retry 1 { let x = true(…);
    leave; }` and then its return: the bound by call depth is 20 (the
    loop's one try is counted once: body plus `until` plus the loop
    bookkeeping, the callee's 5 inside it, and 2 more for the check of
    `until` after the last try since the `retry` correction), and the witness run of
    RufMaschineG §10 takes 9 own steps (`endeEntf`, `dannRetry`,
    `wiederSchritt` with `until` false, the `dannBindCall` push, the
    callee's leaf, `rueckBind` into the waiting binder, `peelSchrumpfLeave`,
    `dannLeaveWieder` out of the loop, `dannLeer`) -- the callee's two steps
    included, since they are steps of thread 0 while the driver's frame is
    below them. -/
theorem frame_schritte_beschraenkt_zeuge_schleife :
    rufTief hP 2 (initF 0).1 = true ∧ kostenTief hP 0 2 (initF 0).1 = 20 ∧
    ∃ lauf : SegLauf hP rufOF 0 M0H H9H,
      aktivVor 0 0 lauf ∧ segZaehle lauf 0 = 9 ∧
      segZaehle lauf 0 ≤ kostenTief hP 0 2 (initF 0).1 := by
  let lauf : SegLauf hP rufOF 0 M0H H9H :=
    .schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0
      (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 .start schritt1H)
      schritt2H) schritt3H) schritt4H) schritt5H) schritt6H) schritt7H) schritt8H) schritt9H
  have hA : aktivVor 0 0 lauf := by
    simp only [lauf, aktivVor, Nat.zero_le, and_self]
  exact ⟨hP_tief, hP_kosten, lauf, hA, rfl,
    frame_schritte_beschraenkt hP rufOF 0 0 (initF 0).1 1 hP_tief
      (eintritt_start hP spF initF 0) lauf hA⟩

end Gabbro.Grammatik

/-! ## CUTS:

  - The runs are the witness runs of `zLauf` (ZielOrtZeuge.lean) and of
    RufMaschineG.lean §10, made explicit as `SegLauf`s; no new run is
    built. Interleaving is witnessed only AFTER thread 1's start frame has
    run out of steps (`lauf17`: thread 0's five steps follow thread 1's
    twelve); thread 0's `locks` could not have fired while thread 1 held
    the lock -- the run simply does not schedule it then, which is the
    waiting the bound does not count.
  - The loop witness has one try (`retry 1`); a `traverse` or `forever`
    run is not witnessed (the step lemma covers them: `schrittArt`).
-/

#print axioms Gabbro.Grammatik.frame_schritte_beschraenkt_zeuge
#print axioms Gabbro.Grammatik.frame_schritte_beschraenkt_zeuge_schleife
