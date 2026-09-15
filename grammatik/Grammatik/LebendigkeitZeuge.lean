/-
  File:      Grammatik/LebendigkeitZeuge.lean
  Subject:   THE WITNESS for the waiting bound (`Lebendigkeit.lean`) on the
             two-thread fixture `mP` (MehrfadenZeuge.lean): a concrete
             scheduled run on which EVERY premise of `wartezeit_schranke`
             holds, with a concrete bound, and a thread that really waits.

  The run (`lLauf`, 23 steps of machine G, then stutters):
    steps 0-2   thread 0: `privA[0] = 7`, `privA[1] = 7`, unfold `locks`
    steps 3-4   thread 1: `privB[0] = 5`, unfold `locks`
    step  5     thread 0 takes the lock; thread 1 stands at `locks` from step 5
    steps 6-11  thread 0 holds it: call `setze(30)`, two writes, return,
                close, release (6 own steps while holding)
    steps 12-14 thread 0: close, call `pruefeA`, return -- finished
    step  15    thread 1 takes the lock (waited 10 scheduler steps)
    steps 16-22 thread 1: its critical section, then finished
    from 23     every thread is finished; the machine stutters.

  The constants: `F = 4` (fairness window), `h = 6` (own steps per critical
  section), `k = 0` (no nested lock), contenders `[0, 1]`. The bound:
  `wartezeit = (2 - 1) * (6 * 4 + 0 + 4) + 4 = 32` (`lW_eq`). Thread 1,
  standing at `locks` at step 5, takes the lock at step 15 < 5 + 32
  (`wartezeit_zeuge`), and the theorem itself says so (`lSchranke`).
-/
import Grammatik.Lebendigkeit
import Grammatik.MehrfadenLauf

namespace Gabbro.Grammatik

set_option linter.unusedVariables false

/-! ## 1. What the witness records about one thread state -/

/-- `omega` does not see through `Faden`; these two facts are all it is needed for. -/
theorem faden_ne_klein {u w : Faden} (hu : 2 ≤ u) (hw : w ≤ 1) : u ≠ w := by
  simp only [Faden] at *; omega

theorem faden_ge2 {g : Faden} (h0 : g ≠ 0) (h1 : g ≠ 1) : 2 ≤ g := by
  simp only [Faden] at *; omega

/-- One thread state, tabled: its held set `o`, whether it stands at `locks`
    (`a`), whether it is finished (`f`), and -- while it holds a lock -- no
    hardware stop at its head in ANY world. -/
structure BefundZ (z : RufFadenG mD) (o : List Unit) (a : Bool) (f : Bool) : Prop where
  off : offen z.spur = o
  kopf : z.kopf.rest.2.2.2.2.kopfSperre = (if a then some () else none)
  fertig : f = true → z.stapel = [] ∧ z.kopf.rest.2.2.2.2.istEndeRet = true
  frei : o ≠ [] → ∀ (σ : World mD) (k : Zielsatz.HaltArt),
    ¬ Zielsatz.RestHalt mO 0 σ z.kopf.rest.2.2.2.1 k z.kopf.rest.2.2.2.2

theorem befund_von {M : RufMaschineG mD} {t : Faden} {z : RufFadenG mD} (hz : M.faeden t = z)
    {o : List Unit} {a f : Bool} (hoff : offen (M.faeden t).spur = o)
    (hk : z.kopf.rest.2.2.2.2.kopfSperre = (if a then some () else none))
    (hf : f = true → z.stapel = [] ∧ z.kopf.rest.2.2.2.2.istEndeRet = true)
    (hh : o ≠ [] → ∀ (σ : World mD) (k : Zielsatz.HaltArt),
      ¬ Zielsatz.RestHalt mO 0 σ z.kopf.rest.2.2.2.1 k z.kopf.rest.2.2.2.2) :
    BefundZ (M.faeden t) o a f := by
  rw [hz] at hoff ⊢
  exact ⟨hoff, hk, hf, hh⟩

theorem befund_gleich {z z' : RufFadenG mD} {o : List Unit} {a f : Bool} (h : z' = z)
    (hb : BefundZ z o a f) : BefundZ z' o a f := h ▸ hb

theorem kein_fertig {z : RufFadenG mD} :
    false = true → z.stapel = [] ∧ z.kopf.rest.2.2.2.2.istEndeRet = true := fun h => by cases h

theorem kein_halt_leer {z : RufFadenG mD} : ([] : List Unit) ≠ [] →
    ∀ (σ : World mD) (k : Zielsatz.HaltArt),
    ¬ Zielsatz.RestHalt mO 0 σ z.kopf.rest.2.2.2.1 k z.kopf.rest.2.2.2.2 :=
  fun h => absurd rfl h

/-- The idle threads: every thread from 2 on starts in `ruhe`, finished. -/
theorem lStartRuhe (u : Faden) (hu : 2 ≤ u) :
    (RufStartG mP mSp mInit).faeden u = ⟨[], ⟨mRuhe, .nil, mSp.welt [],
      ⟨false, [], [], .nil, .ende (.ret .keine List.Perm.nil)⟩⟩, startSpur mRuhe,
      [RufEreignisF.eintritt mRuhe .nil (mSp.welt [])]⟩ := by
  have e : mInit u = ⟨mRuhe, .nil⟩ := by
    unfold mInit
    rw [if_neg (faden_ne_klein hu (by decide)), if_neg (faden_ne_klein hu (by decide))]
  show (match mInit u with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, mSp.welt [], ⟨false, mD.params g,
        Signatur.anfang mD (mD.signatur g), rho, .ende (mP.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (mSp.welt [])]⟩ : RufFadenG mD)) = _
  rw [e]
  rfl

theorem lRuheBefund (u : Faden) (hu : 2 ≤ u) :
    BefundZ ((RufStartG mP mSp mInit).faeden u) [] false true :=
  befund_von (lStartRuhe u hu) (mStart_offen u) rfl (fun _ => ⟨rfl, rfl⟩) kein_halt_leer

/-! ## 2. One critical section, step by step -/

set_option maxHeartbeats 2000000 in
/-- **One critical section of a thread standing at `locks { setze(e) }`**,
    with every intermediate thread state tabled (the refinement of
    `mAbschnitt`): take, call, two writes, return, close, release, close. -/
theorem lAbschnitt {M : RufMaschineG mD} (t : Faden) (fn : mD.Fn) (rho : Env mD (mD.params fn))
    (s0 : World mD) (log : List (RufEreignisF mD)) (e : Expr mD [] mL (.int 0 100))
    (hp : RufPasst mD (vertragVon mD fn) (mD.signatur mSetze) mL)
    (h : ∀ K, Res.held K ∈ ([] : List (Res mD)) → mD.rang K < mD.rang ())
    (k : GRest mD (vertragVon mD fn) false [] []) (σ : World mD)
    (hz : ZustandG M t [] fn rho s0 log .nil
      (.dann (.cons (.locks () h (.cons (.call mSetze (.cons e .nil) hp rfl) .nil)) .nil) k) σ)
    (hoff : offen σ.spur = []) (hfrei : RufFreiG M t ()) :
    ∃ N1 N2 N3 N4 N5 N6 N7 N8 : RufMaschineG mD,
      RufSchrittG mP mO 0 M t N1 ∧ RufSchrittG mP mO 0 N1 t N2 ∧ RufSchrittG mP mO 0 N2 t N3 ∧
      RufSchrittG mP mO 0 N3 t N4 ∧ RufSchrittG mP mO 0 N4 t N5 ∧ RufSchrittG mP mO 0 N5 t N6 ∧
      RufSchrittG mP mO 0 N6 t N7 ∧ RufSchrittG mP mO 0 N7 t N8 ∧
      BefundZ (N1.faeden t) [()] false false ∧ BefundZ (N2.faeden t) [()] false false ∧
      BefundZ (N3.faeden t) [()] false false ∧ BefundZ (N4.faeden t) [()] false false ∧
      BefundZ (N5.faeden t) [()] false false ∧ BefundZ (N6.faeden t) [()] false false ∧
      BefundZ (N7.faeden t) [] false false ∧
      ∃ (σ' : World mD) (log' : List (RufEreignisF mD)),
        ZustandG N8 t [] fn rho s0 log' .nil k σ' ∧ offen σ'.spur = [] := by
  have hoff0 : offen (M.faeden t).spur = [] := by rw [hz.spur]; exact hoff
  obtain ⟨M1, s1, hZ1⟩ := w_locks (P := mP) (O := mO) (passes := 0) hz.1 ()
    _ _ _ _ _ rfl (mhg0 hoff) hfrei
  have hoff1 : offen (M1.faeden t).spur = [()] := by
    rw [hZ1.spur]
    exact congrArg (List.cons ()) hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_rufDann (P := mP) (O := mO) (passes := 0) hZ1.1 mSetze
    (.cons e .nil) hp rfl .nil _ _ rfl (mhgL (moff_z hZ1 hoff1)).heldIn
  have hoff2 : offen (M2.faeden t).spur = [()] := by
    rw [hZ2.spur, (Erw.lese _ _ _).offen]; exact hoff1
  obtain ⟨M3, s3, hZ3⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ2.1
    _ _ _ rfl rfl (mhgL (moff_z hZ2 hoff2)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff3 : offen (M3.faeden t).spur = [()] := by
    rw [hZ3.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ3.1
    _ _ _ rfl rfl (mhgL (moff_z hZ3 hoff3)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden t).spur = [()] := by
    rw [hZ4.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (mhgL (moff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden t).spur = [()] := by
    rw [hG5.1]
    exact ((Erw.lese _ _ _).offen).trans hoff4
  obtain ⟨M6, s6, hZ6⟩ := w_dannLeer (P := mP) (O := mO) (passes := 0) hG5.1 _ _ rfl
  have hoff6 : offen (M6.faeden t).spur = [()] := by
    rw [hZ6.spur]; exact hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_freiGib (P := mP) (O := mO) (passes := 0) hZ6.1 () _ _ rfl
  have hoff7 : offen (M7.faeden t).spur = [] := by
    rw [hZ7.spur]
    show (offen (M6.faeden t).spur).erase () = []
    rw [hoff6]
    rfl
  obtain ⟨M8, s8, hZ8⟩ := w_dannLeer (P := mP) (O := mO) (passes := 0) hZ7.1 _ _ rfl
  refine ⟨M1, M2, M3, M4, M5, M6, M7, M8, s1, s2, s3, s4, s5, s6, s7, s8, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, _, _, hZ8, ?_⟩
  · refine befund_von hZ1.1 hoff1 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp [Zielsatz.RestHalt, Zielsatz.KopfHalt, Stmt.istBlatt] at hR
  · refine befund_von hZ2.1 hoff2 rfl kein_fertig fun _ σ k hR => ?_
    cases k
    · obtain ⟨_, hw, he⟩ := hR
      have he' := (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _).symm.trans he
      cases he'
    all_goals simp [Zielsatz.RestHalt] at hR
  · refine befund_von hZ3.1 hoff3 rfl kein_fertig fun _ σ k hR => ?_
    cases k
    · obtain ⟨_, hw, he⟩ := hR
      have he' := (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _).symm.trans he
      cases he'
    all_goals simp [Zielsatz.RestHalt] at hR
  · refine befund_von hZ4.1 hoff4 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp [Zielsatz.RestHalt] at hR
  · refine befund_von hG5.1 hoff5 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp [Zielsatz.RestHalt, Zielsatz.KopfHalt] at hR
  · refine befund_von hZ6.1 hoff6 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp [Zielsatz.RestHalt] at hR
  · exact befund_von hZ7.1 hoff7 rfl kein_fertig kein_halt_leer
  · show offen (M7.faeden t).spur = []
    exact hoff7

/-! ## 3. The run -/

/-- The scheduler's choices: who acts at step `j`. -/
def lAkt (j : Nat) : Option Faden :=
  if j ≤ 2 then some 0 else if j ≤ 4 then some 1 else if j ≤ 14 then some 0
  else if j ≤ 22 then some 1 else none

/-- The table of thread 0: holds the lock at steps 6-11, stands at `locks` at
    3-5, finished from 15. -/
def lO0 (j : Nat) : List Unit := if 6 ≤ j ∧ j ≤ 11 then [()] else []
def lA0 (j : Nat) : Bool := decide (3 ≤ j ∧ j ≤ 5)
def lF0 (j : Nat) : Bool := decide (15 ≤ j)

/-- The table of thread 1: holds the lock at steps 16-21, stands at `locks`
    at 5-15, finished from 23. -/
def lO1 (j : Nat) : List Unit := if 16 ≤ j ∧ j ≤ 21 then [()] else []
def lA1 (j : Nat) : Bool := decide (5 ≤ j ∧ j ≤ 15)
def lF1 (j : Nat) : Bool := decide (23 ≤ j)

theorem lAkt_none_von {n : Nat} {u : Faden} (h : lAkt n = some u) : n ≤ 22 := by
  refine Classical.byContradiction fun hn => ?_
  unfold lAkt at h
  rw [if_neg (show ¬ n ≤ 2 by omega), if_neg (show ¬ n ≤ 4 by omega), if_neg (show ¬ n ≤ 14 by omega),
    if_neg (show ¬ n ≤ 22 by omega)] at h
  cases h

theorem lAkt_none {n : Nat} (h : lAkt n = none) : 23 ≤ n := by
  refine Classical.byContradiction fun hn => ?_
  unfold lAkt at h
  by_cases h1 : n ≤ 2
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : n ≤ 4
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : n ≤ 14
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3, if_pos (show n ≤ 22 by omega)] at h
  cases h

theorem lAkt_some {n : Nat} {u : Faden} (h : lAkt n = some u) :
    (u = 0 ∧ (n ≤ 2 ∨ (5 ≤ n ∧ n ≤ 14))) ∨ (u = 1 ∧ ((3 ≤ n ∧ n ≤ 4) ∨ (15 ≤ n ∧ n ≤ 22))) := by
  unfold lAkt at h
  by_cases h1 : n ≤ 2
  · rw [if_pos h1] at h; cases h; exact Or.inl ⟨rfl, Or.inl h1⟩
  rw [if_neg h1] at h
  by_cases h2 : n ≤ 4
  · rw [if_pos h2] at h; cases h; exact Or.inr ⟨rfl, Or.inl ⟨by omega, h2⟩⟩
  rw [if_neg h2] at h
  by_cases h3 : n ≤ 14
  · rw [if_pos h3] at h; cases h; exact Or.inl ⟨rfl, Or.inr ⟨by omega, h3⟩⟩
  rw [if_neg h3] at h
  by_cases h4 : n ≤ 22
  · rw [if_pos h4] at h; cases h; exact Or.inr ⟨rfl, Or.inr ⟨by omega, h4⟩⟩
  rw [if_neg h4] at h
  cases h

theorem lAkt_wert (n : Nat) :
    (n ≤ 2 → lAkt n = some 0) ∧ (3 ≤ n → n ≤ 4 → lAkt n = some 1) ∧
    (5 ≤ n → n ≤ 14 → lAkt n = some 0) ∧ (15 ≤ n → n ≤ 22 → lAkt n = some 1) := by
  unfold lAkt
  refine ⟨fun h => by rw [if_pos h], fun h1 h2 => by rw [if_neg (show ¬ n ≤ 2 by omega), if_pos h2],
    fun h1 h2 => by
      rw [if_neg (show ¬ n ≤ 2 by omega), if_neg (show ¬ n ≤ 4 by omega), if_pos h2],
    fun h1 h2 => by
      rw [if_neg (show ¬ n ≤ 2 by omega), if_neg (show ¬ n ≤ 4 by omega),
        if_neg (show ¬ n ≤ 14 by omega), if_pos h2]⟩

set_option maxHeartbeats 8000000 in
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
    (.ret .keine List.Perm.nil) .nil rfl rfl
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
    mHpPruefe rfl (.ret .keine List.Perm.nil) .nil rfl (mHeld0 _)
  obtain ⟨Md, sd, hGd⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZc.1 _ [] rfl
    (PopArt.wie rfl) .keine List.Perm.nil .nil rfl (mHeld0 _)
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
      (.dann (.cons mLocksB .nil) (.ende (.ret .keine List.Perm.nil)))
      (Md.speicher.welt (M4.weltVon 1).spur) := ⟨f1_15.trans hZ5.1, rfl⟩
  have hfreid : RufFreiG Md 1 () := mFrei fun g hg => by
    by_cases hg0 : g = 0
    · subst hg0; exact o0_d
    · rw [i15 g (faden_ge2 hg0 hg), hI5 g (faden_ge2 hg0 hg)]; exact mStart_offen g
  obtain ⟨P1, P2, P3, P4, P5, P6, P7, P8, c1, c2, c3, c4, c5, c6, c7, c8,
      d1, d2, d3, d4, d5, d6, d7, σb, logb, hzb, hoffb⟩ :=
    lAbschnitt (M := Md) 1 mHauptB .nil (mSp.welt []) _ m70 mHpSetzeB (fun _ h => nomatch h)
      (.ende (.ret .keine List.Perm.nil)) _ hz1d o1_4 hfreid
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
/-- **The witness run with every premise of `wartezeit_schranke`**: the
    runtime assumption at `F = 4`, the hold time `h = 6`, `k = 0`, no
    hardware stop in a critical section, the contenders `[0, 1]`, and
    `KeinLogikHaltG` at every machine (from `mP_zertifiziert`). And the run
    is not degenerate: thread 1 stands at `locks` from step 5 to step 15
    while thread 0 holds the lock at steps 6-11, and takes it at step 15. -/
theorem lZeuge : ∃ R : PlanLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧ R.akt = lAkt ∧
    LaufzeitAnnahme R 4 ∧ Haltezeit R (fun _ => 6) (fun _ => 0) ∧ HardwareImAbschnitt R ∧
    Anwaerter R (fun _ => [0, 1]) ∧ (∀ n, KeinLogikHaltG mO 0 (R.M n)) ∧
    (∀ j, 5 ≤ j → j ≤ 15 → AnSperre (R.M j) 1 ()) ∧
    (∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((R.M j).faeden 0).spur) ∧
    () ∈ offen ((R.M 16).faeden 1).spur := by
  obtain ⟨Ms, h0, hS, hT, hB0, hB1, hI⟩ := lLauf
  have nb0 : ∀ j, 15 ≤ j → ¬ Bereit mP mO 0 (Ms j) 0 := fun j hj => by
    have hb := hB0 j
    have e : lF0 j = true := by simp only [lF0]; exact decide_eq_true hj
    rw [e] at hb
    exact befund_nicht_bereit hb
  have nb1 : ∀ j, 23 ≤ j → ¬ Bereit mP mO 0 (Ms j) 1 := fun j hj => by
    have hb := hB1 j
    have e : lF1 j = true := by simp only [lF1]; exact decide_eq_true hj
    rw [e] at hb
    exact befund_nicht_bereit hb
  have nbI : ∀ j u, 2 ≤ u → ¬ Bereit mP mO 0 (Ms j) u := fun j u hu =>
    befund_nicht_bereit (lRuhe_j hI j u hu)
  have an1 : ∀ j, 5 ≤ j → j ≤ 15 → AnSperre (Ms j) 1 () := fun j h1 h2 =>
    (befund_an (hB1 j) ()).2 (by simp only [lA1]; exact decide_eq_true ⟨h1, h2⟩)
  have halt0 : ∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((Ms j).faeden 0).spur := fun j h1 h2 => by
    rw [(hB0 j).off]
    unfold lO0
    rw [if_pos ⟨h1, h2⟩]
    exact List.mem_singleton_self _
  -- thread 1 cannot step while thread 0 holds the lock
  have nb1h : ∀ j, 6 ≤ j → j ≤ 11 → ¬ Bereit mP mO 0 (Ms j) 1 := fun j h1 h2 =>
    nicht_bereit_an_sperre (an1 j (by omega) (by omega)) (by decide) (halt0 j h1 h2)
  let R : PlanLauf mP mO 0 :=
    { M := Ms, akt := lAkt, schritt := hS,
      stotter := fun n hn => by
        have h23 := lAkt_none hn
        refine ⟨(hT (n + 1) (by omega)).trans (hT n h23).symm, fun u => ?_⟩
        by_cases hu0 : u = 0
        · subst hu0; exact nb0 n (by omega)
        · by_cases hu1 : u = 1
          · subst hu1; exact nb1 n h23
          · exact nbI n u (faden_ge2 hu0 hu1) }
  refine ⟨R, h0, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, an1, halt0, ?_⟩
  · -- FIFO
    intro t u L a n htu hW hakt hAu
    rcases lAkt_some hakt with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
    · -- thread 0 takes the lock: only at step 5
      rcases lAn hB0 hB1 hI hAu with ⟨_, h3, h5⟩ | ⟨h, _⟩
      · have hn5 : n = 5 := by omega
        subst hn5
        intro j hj1 hj2
        have ha : 5 ≤ a := by
          refine Classical.byContradiction fun ha => ?_
          rcases lAn hB0 hB1 hI (hW 4 (by omega) (by omega)) with ⟨ht, _, _⟩ | ⟨_, h5', _⟩
          · exact htu ht
          · omega
        have hj : j = 5 := by omega
        subst hj
        exact hAu
      · cases h
    · -- thread 1 takes the lock: only at step 15, when nobody else waits
      rcases lAn hB0 hB1 hI hAu with ⟨h, _⟩ | ⟨_, h5, h15⟩
      · cases h
      · have hn15 : n = 15 := by omega
        subst hn15
        intro j hj1 hj2
        exfalso
        rcases lAn hB0 hB1 hI (hW 15 (by omega) (Nat.le_refl 15)) with ⟨_, _, h⟩ | ⟨ht, _, _⟩
        · omega
        · exact htu ht
  · -- fairness, window 4
    intro t n hb
    have w := lAkt_wert
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hn : n ≤ 14
      · by_cases hn2 : n ≤ 2
        · exact ⟨n, Nat.le_refl n, by omega, (w n).1 hn2⟩
        · by_cases hn4 : n ≤ 4
          · exact ⟨5, by omega, by omega, (w 5).2.2.1 (by omega) (by omega)⟩
          · exact ⟨n, Nat.le_refl n, by omega, (w n).2.2.1 (by omega) hn⟩
      · exact absurd (hb n (Nat.le_refl n) (by omega)) (nb0 n (by omega))
    · by_cases ht1 : t = 1
      · subst ht1
        by_cases hn3 : n ≤ 3
        · exact ⟨3, by omega, by omega, (w 3).2.1 (by omega) (by omega)⟩
        · by_cases hn4 : n ≤ 4
          · exact ⟨4, by omega, by omega, (w 4).2.1 (by omega) (by omega)⟩
          · by_cases hn11 : n ≤ 11
            · have hm : 6 ≤ max n 6 ∧ max n 6 ≤ 11 := by omega
              exact absurd (hb (max n 6) (by omega) (by omega)) (nb1h _ hm.1 hm.2)
            · by_cases hn14 : n ≤ 14
              · exact ⟨15, by omega, by omega, (w 15).2.2.2 (by omega) (by omega)⟩
              · by_cases hn22 : n ≤ 22
                · exact ⟨n, Nat.le_refl n, by omega, (w n).2.2.2 (by omega) hn22⟩
                · exact absurd (hb n (Nat.le_refl n) (by omega)) (nb1 n (by omega))
      · exact absurd (hb n (Nat.le_refl n) (by omega)) (nbI n t (faden_ge2 ht0 ht1))
  · -- the hold time: 6 own steps, no nested acquisition
    intro u L a n hhold
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact ⟨Nat.zero_le _, Nat.le_refl _⟩
    · have hw : ∀ i, i < n → (u = 0 ∧ 6 ≤ a + i ∧ a + i ≤ 11) ∨
          (u = 1 ∧ 16 ≤ a + i ∧ a + i ≤ 21) :=
        fun i hi => lHaelt hB0 hB1 hI (hhold i hi)
      have hn6 : n ≤ 6 := by
        rcases hw 0 hn with ⟨hu, h1, _⟩ | ⟨hu, h1, _⟩
        · rcases hw (n - 1) (by omega) with ⟨_, _, h2⟩ | ⟨hu', _, _⟩
          · omega
          · rw [hu] at hu'; exact absurd hu' (by decide)
        · rcases hw (n - 1) (by omega) with ⟨hu', _, _⟩ | ⟨_, _, h2⟩
          · rw [hu] at hu'; exact absurd hu' (by decide)
          · omega
      refine ⟨Nat.le_trans (zaehl_le _ a n) hn6, Nat.le_of_eq (zaehl_null _ a n fun i hi hp => ?_)⟩
      obtain ⟨_, L', hA⟩ := hp
      rcases lAn hB0 hB1 hI hA with ⟨hu, _, h5⟩ | ⟨hu, _, h15⟩ <;>
        rcases hw i hi with ⟨hu', h6, _⟩ | ⟨hu', h16, _⟩
      · omega
      · rw [hu] at hu'; exact absurd hu' (by decide)
      · rw [hu] at hu'; exact absurd hu' (by decide)
      · omega
  · -- no hardware stop in a critical section
    intro n u L hL k hH
    have hk := halt_kopf hH
    rcases lHaelt hB0 hB1 hI hL with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have hne : lO0 n ≠ [] := by
        intro e; rw [(hB0 n).off, e] at hL; exact List.not_mem_nil hL
      exact (hB0 n).frei hne _ _ hk
    · have hne : lO1 n ≠ [] := by
        intro e; rw [(hB1 n).off, e] at hL; exact List.not_mem_nil hL
      exact (hB1 n).frei hne _ _ hk
  · -- the contenders
    intro n u L h
    rcases h with h | h
    · rcases lHaelt hB0 hB1 hI h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases lAn hB0 hB1 hI h with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
  · -- no `logik` stop, from the flagship
    intro n
    have hr : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) (R.M n) :=
      R.erreichbar (by show RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) (Ms 0); rw [h0]
                       exact .start) n
    exact (mP_zertifiziert 0 (R.M n) hr).1.1.2.2.1
  · show () ∈ offen ((Ms 16).faeden 1).spur
    rw [(hB1 16).off]
    exact List.mem_singleton_self _

/-- The bound on the witness: `(2 - 1) * (6 * 4 + 0 * 0 + 4) + 4 = 32`. -/
theorem lW_eq : wartezeit (D := mD) [()] (fun _ => [0, 1]) (fun _ => 6) (fun _ => 0) 4 () = 32 := by
  decide

/-- **THE WAITING BOUND ON THE WITNESS** (`wartezeit_schranke`, every premise
    discharged): thread 1, standing at `locks` at step 5 (while thread 0 is
    about to hold the lock for steps 6-11), takes the lock at a step
    `j < 5 + 32` and holds it after -- BY THE THEOREM. On the concrete run it
    takes it at step 15 (`lZeuge`: `akt 15 = some 1`, held at step 16). -/
theorem wartezeit_zeuge : ∃ R : PlanLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧ LaufzeitAnnahme R 4 ∧
    Haltezeit R (fun _ => 6) (fun _ => 0) ∧ HardwareImAbschnitt R ∧
    Anwaerter R (fun _ => [0, 1]) ∧
    AnSperre (R.M 5) 1 () ∧
    (∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((R.M j).faeden 0).spur) ∧
    R.akt 15 = some 1 ∧ () ∈ offen ((R.M 16).faeden 1).spur ∧
    wartezeit (D := mD) [()] (fun _ => [0, 1]) (fun _ => 6) (fun _ => 0) 4 () = 32 ∧
    ∃ j, 5 ≤ j ∧ j < 5 + 32 ∧ R.akt j = some 1 ∧ () ∈ offen ((R.M (j + 1)).faeden 1).spur := by
  obtain ⟨R, h0, hakt, hLZ, hH, hHw, hAnw, hL, an1, halt0, h16⟩ := lZeuge
  have hA5 : AnSperre (R.M 5) 1 () := an1 5 (Nat.le_refl 5) (by decide)
  have hB : ∀ n t, BereichG (R.M n) t := fun n =>
    bereichG_mehrfaden mP mO 0 (axWahr mD) mSI mFs mSp mInit mK mO_gut mO_lokal
      (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
      (mP_koerper_alle 0) mP_start mSI_start mInit_exklusiv (R.M n)
      (R.erreichbar (by rw [h0]; exact .start) n)
  have hW := wartezeit_schranke R mO_gut mP_stufen mSp mInit mInit_leer
    (ls := [()]) (fun L => by cases L; exact List.mem_singleton_self _)
    (by rw [h0]; exact .start) hL hB
    (fun g x hx => absurd hx (by cases g <;> exact List.not_mem_nil)) hLZ hH hHw hAnw () 1 5 hA5
  rw [lW_eq] at hW
  exact ⟨R, h0, hLZ, hH, hHw, hAnw, hA5, halt0, by rw [hakt]; rfl, h16, lW_eq, hW⟩

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lLauf
#print axioms Gabbro.Grammatik.lZeuge
#print axioms Gabbro.Grammatik.wartezeit_zeuge
