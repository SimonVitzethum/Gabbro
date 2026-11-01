module

public import Grammatik.Logik.Fortschritt.KostenGZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
public import Grammatik.Korpus.Referenz.Referenz104.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- **The run of `104-referenz.gab` on G** (7 steps of thread 0): the driver
    calls `einzahlen(&Konto, 0, 7)` (1), which writes `Konto[0].stand = 100`
    through its pointer (2: memory `0 -> 100`), calls `lies(k, 0)` (3), which
    returns the slot (4, logged); `einzahlen` returns (5, logged); the
    driver calls `lies(&Konto, 0)` (6), which returns (7, logged). -/
theorem r4Lauf : ∃ M : RufMaschineG r4D,
    RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
    (M.speicher.slots () 0 ()).n = 100 ∧
    (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
      RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log) ∧
    VertragAmOrtG r4P M := by
  have h00 : (RufStartG r4P r4Sp r4Init).faeden 0 = ⟨[], ⟨r4Treiber, .nil, r4Sp.welt [],
      ⟨false, [], r4M, .nil, .ende r4RumpfTreiber⟩⟩, startSpur r4Treiber,
      [RufEreignisF.eintritt r4Treiber .nil (r4Sp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG r4P r4Sp r4Init).faeden 0).spur = [()] := rfl
  -- 1: call `einzahlen`
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) h00 r4Ein _ r4HpEinT rfl
    r4RestT .nil rfl (r4HgM hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: the write through the pointer
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := r4P) (O := r4O) (passes := 0) e1 r4Schreib r4RestEin _
    rfl rfl (r4HgM (r4Hoff e1 hoff1)).heldIn _ _ rfl ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff1)
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: call `lies`
  obtain ⟨M3, s3, hZ3⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) e2 r4Lies _ r4HpLies rfl
    r4RetEin _ rfl (r4HgM (r4Hoff e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  -- 4: `lies` returns
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e3 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hG4.1]; exact ((Erw.lese _ _ _).offen).trans hoff3
  have e4 := hG4.1
  try dsimp only at e4
  -- 5: `einzahlen` returns
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e4 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hG5.1]; exact ((Erw.lese _ _ _).offen).trans hoff4
  have e5 := hG5.1
  try dsimp only at e5
  -- 6: the driver calls `lies`
  obtain ⟨M6, s6, hZ6⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) e5 r4Lies _ r4HpLiesT rfl
    r4RetT .nil rfl (r4HgM (r4Hoff e5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 0).spur = [()] := by
    rw [hZ6.spur, (Erw.lese _ _ _).offen]; exact hoff5
  have e6 := hZ6.1
  try dsimp only at e6
  -- 7: `lies` returns
  obtain ⟨M7, s7, hG7⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e6 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e6 hoff6)).heldIn
  have hr7 : RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M7 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7
  have hsp4 : (M4.speicher.slots () 0 ()).n = 100 := by
    rw [hG4.2]
    show (M3.speicher.slots () 0 ()).n = 100
    rw [hZ3.2]
    show (M2.speicher.slots () 0 ()).n = 100
    rw [hZ2.2]
    rfl
  have hsp7 : (M7.speicher.slots () 0 ()).n = 100 := by
    rw [hG7.2]
    show (M6.speicher.slots () 0 ()).n = 100
    rw [hZ6.2]
    show (M5.speicher.slots () 0 ()).n = 100
    rw [hG5.2]
    exact hsp4
  have hfremd : ∀ t : Faden, t ≠ 0 → M7.faeden t = (RufStartG r4P r4Sp r4Init).faeden t := by
    intro t ht
    rw [rufSchrittG_fremd s7 t ht, rufSchrittG_fremd s6 t ht, rufSchrittG_fremd s5 t ht,
      rufSchrittG_fremd s4 t ht, rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht,
      rufSchrittG_fremd s1 t ht]
  have hlog7 := congrArg RufFadenG.log hG7.1
  have hlog6 := congrArg RufFadenG.log e6
  have hlog5 := congrArg RufFadenG.log e5
  have hlog4 := congrArg RufFadenG.log e4
  refine ⟨M7, hr7, hsp7, ?_, ?_⟩
  · rw [hlog7]
    dsimp only
    exact ⟨_, _, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · intro t ev hev
    refine ⟨fun g rho s0 _ => rfl, ?_⟩
    intro g rho v s0 s1' he
    subst he
    by_cases ht : t = 0
    · subst ht
      rw [hlog7] at hev
      dsimp only at hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with h | h | h | h | h | h | h
      · cases h
        exact decide_eq_true rfl
      · cases h
      · cases h
        show decide ((r4Sp.slots () 0 ()).n ≤ (M4.speicher.slots () 0 ()).n) = true
        rw [hsp4]
        rfl
      · cases h
        exact decide_eq_true rfl
      · cases h
      · cases h
      · cases h
    · rw [hfremd t ht, r4_start_log] at hev
      have hi : r4Init t = ⟨r4Ruhe, .nil⟩ := if_neg ht
      rw [hi] at hev
      simp only [List.mem_singleton] at hev
      cases hev

/-! ## 7. The premises, jointly -/

/-- **`referenz104_zeuge`.** On the hand translation of
    `104-referenz.gab` (plus the flagged driver and idle function), every
    premise of `ziel_ort_voll` holds EXCEPT the user obligation of
    `einzahlen`, which is refuted; the declared costs pass `kostenPasst`;
    on the reached run (memory `0 -> 100`, the return of `einzahlen`
    logged) the contracts hold at every logged event, checked directly. -/
theorem referenz104_zeuge :
    GutO r4O ∧ (∀ g : r4D.Fn, g ∈ r4Fs) ∧ programmImFragmentV r4P r4Fs = true ∧
    fussOrtB r4P r4Fs = true ∧ StartGut r4P r4Sp r4Init ∧ StartExklusiv (D := r4D) r4Init ∧
    KoerperGutV r4P 0 r4Lies ∧ KoerperGutV r4P 0 r4Treiber ∧ KoerperGutV r4P 0 r4Ruhe ∧
    ¬ KoerperGutV r4P 0 r4Ein ∧ kostenPasst r4P 0 r4Decl r4Fs = true ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log) ∧
      VertragAmOrtG r4P M := by
  obtain ⟨M, hr, hsp, hlog, hV⟩ := r4Lauf
  exact ⟨r4O_gut, r4Fs_voll, r4P_fragment, r4P_fuss, r4P_start, r4Init_exklusiv,
    r4P_koerper_lies, r4P_koerper_treiber, r4P_koerper_ruhe, r4_einzahlen_nicht_V,
    r4P_kostenPasst, M, hr, rfl, hsp, hlog, hV⟩

/-! ## CUTS:

  What is proved: the hand translation `r4D`/`r4P` of `104-referenz.gab`
  (the construct table in the header); the decidable premises
  (`r4P_fragment`, `r4P_fuss`), the declared costs (`r4P_kostenPasst`),
  `GutO`, the start facts, the user obligations of `lies`, the driver and
  the idle function; the refutation of `einzahlen`'s obligation
  (`r4_einzahlen_nicht_V`); a reached run of G and the contracts on it
  (`r4Lauf`, `referenz104_zeuge`).

  What is NOT proved: `ziel_ort_voll` (or `ziel_ort_geraet`) for `r4P` --
  its premise `∀ f, KoerperGutV r4P 0 f` is false. The repair (handlers
  that respect the callee's declared frame, the call analogue of
  `RahmenO`) is proposed, not built. Constructs without a Lean form: the
  module, named constants, carrier widths, address spaces, the lock hold
  budget `held <= N ops`, the `reads` effect, the implicit fall-off
  return, the `rw`-to-`r` pointer coercion (written as `ptrOf` of the same
  table), `old(p->f)` through a pointer (written as `old` of the table).
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.r4_einzahlen_nicht_V
#print axioms Gabbro.Grammatik.r4Lauf
#print axioms Gabbro.Grammatik.referenz104_zeuge
