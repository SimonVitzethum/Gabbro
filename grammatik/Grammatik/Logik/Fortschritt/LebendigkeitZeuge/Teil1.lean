module

public import Grammatik.Logik.Fortschritt.Lebendigkeit
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenLauf

@[expose] public section



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
      ⟨false, [], [], .nil, .ende (.ret .empty List.Perm.nil)⟩⟩, startSpur mRuhe,
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
    cases k <;> (try rw [show mP.rumpf mSetze = mRumpfSetze from rfl] at hR) <;>
      simp only [Zielsatz.RestHalt, Zielsatz.KopfHalt, Stmt.istBlatt, Bool.false_eq_true, false_and] at hR
  · refine befund_von hZ2.1 hoff2 rfl kein_fertig fun _ σ k hR => ?_
    cases k
    · obtain ⟨_, hw, he⟩ := hR
      have he' := (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _).symm.trans he
      cases he'
    all_goals (try rw [show mP.rumpf mSetze = mRumpfSetze from rfl] at hR)
    all_goals simp only [Zielsatz.RestHalt, mRumpfSetze] at hR
  · refine befund_von hZ3.1 hoff3 rfl kein_fertig fun _ σ k hR => ?_
    cases k
    · obtain ⟨_, hw, he⟩ := hR
      have he' := (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _).symm.trans he
      cases he'
    all_goals (try rw [show mP.rumpf mSetze = mRumpfSetze from rfl] at hR)
    all_goals simp only [Zielsatz.RestHalt] at hR
  · refine befund_von hZ4.1 hoff4 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp only [Zielsatz.RestHalt] at hR
  · refine befund_von hG5.1 hoff5 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp only [Zielsatz.RestHalt, Zielsatz.KopfHalt] at hR
  · refine befund_von hZ6.1 hoff6 rfl kein_fertig fun _ σ k hR => ?_
    cases k <;> simp only [Zielsatz.RestHalt] at hR
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
end Gabbro.Grammatik
