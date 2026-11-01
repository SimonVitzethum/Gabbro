module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem geHgLt {s : List (Ereignis geD)} (h : offen s = [GeLock.lt]) :
    HeldGenau geLt (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm geHeld_ne),
      fun h => absurd (List.mem_singleton.mp h) (Ne.symm geLock_ne)⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem geOffen_weltVon (M : RufMaschineG geD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := by rfl

theorem geOffen_fragt (M : RufMaschineG geD) (t : Faden) (q : geD.Ax ⊕ geD.Reg ⊕ geD.Glob) :
    offen ((M.weltVon t).fragt q).spur = offen (M.faeden t).spur := by rfl

theorem geHoff_e {M : RufMaschineG geD} {f : Faden} {z : RufFadenG geD} {x : List geD.Lock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

def geNull : Wert geD (.int 0 1) := ⟨0, by decide, by decide⟩

/-- **The run.** Thread 0 calls `leser`, unfolds its `if`, reads the
    register (`0`), writes `notiz`; thread 1 writes `tafel`; thread 0 reads
    the register again (`0`) and returns `0 == 0`. The log of thread 0 ends
    in the return of `leser`; between the two reads memory changed twice
    (`notiz` and `tafel` from `0` to `1`), the device carrier did not. -/
theorem geLauf : ∃ M : RufMaschineG geD,
    RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M ∧
    (M.speicher.slots GeTab.tafel 0 ()).n = 1 ∧ (M.speicher.slots GeTab.notiz 0 ()).n = 1 ∧
    (M.speicher.slots GeTab.geraet 0 ()).n = 0 ∧
    ∃ (rho : Env geD (geD.params geLeser)) (s0 s1 : World geD),
      RufEreignisF.rueck geLeser rho true s0 s1 ∈ (M.faeden 0).log := by
  have h0 := geM0_faden0
  have hoff0 : offen ((RufStartG geP geSp geInit).faeden 0).spur = [GeLock.lg] := rfl
  -- `haupt` calls `leser`
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := geP) (O := geO) (passes := 0) h0 geLeser .nil geHpLeser
    rfl (.ret .empty (List.Perm.refl _)) .nil rfl (geHgLg hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [GeLock.lg] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen, geOffen_weltVon]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- `leser`: unfold the `if`, take its true branch
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := geP) (O := geO) (passes := 0) e1
    (.ite .tru geLesBlock .nil) (.ret (.val .tru) (List.Perm.refl _)) .nil rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [GeLock.lg] := by
    rw [hZ2.spur, geOffen_weltVon]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := geP) (O := geO) (passes := 0) e2 .tru geLesBlock .nil
    .nil (.ende (.ret (.val .tru) (List.Perm.refl _))) .nil rfl rfl
    (geHgLg (geHoff_e e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [GeLock.lg] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, geOffen_weltVon]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  have hsp3 : M3.speicher = geSp := by
    rw [hZ3.2]
    show M2.speicher = geSp
    rw [hZ2.2]
    show M1.speicher = geSp
    rw [hZ1.2]
    rfl
  -- first read: 0
  obtain ⟨M4, s4, hZ4⟩ := w_regLies (P := geP) (O := geO) (passes := 0) e3 () rfl _ _ .nil rfl
    geNull
    (by show einpassen geO.zeiger (.int 0 1) ((M3.speicher.slots GeTab.geraet 0 ()).n) = some geNull
        rw [hsp3]; rfl)
    rfl (geHgLg (geHoff_e e3 hoff3)).heldIn
  have e4 := hZ4.1
  try dsimp only at e4
  have hoff4 : offen (M4.faeden 0).spur = [GeLock.lg] := by
    rw [hZ4.spur, geOffen_fragt]; exact hoff3
  -- the reader writes `notiz`
  obtain ⟨M5, s5, hZ5⟩ := w_dannBlatt (P := geP) (O := geO) (passes := 0) e4 geNotiz _ _ _
    rfl rfl (geHgLg (geHoff_e e4 hoff4)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have e5 := hZ5.1
  try dsimp only at e5
  have hoff5 : offen (M5.faeden 0).spur = [GeLock.lg] := by
    rw [hZ5.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans
      (((Erw.lese _ _ _).offen).trans ((geOffen_weltVon _ _).trans hoff4))
  -- thread 1 writes `tafel`
  have h51 : M5.faeden 1 = geZ1 := by
    rw [rufSchrittG_fremd s5 1 (by decide), rufSchrittG_fremd s4 1 (by decide),
      rufSchrittG_fremd s3 1 (by decide), rufSchrittG_fremd s2 1 (by decide),
      rufSchrittG_fremd s1 1 (by decide), geM0_faden1]
  obtain ⟨M6, s6, hZ6⟩ := w_blatt (P := geP) (O := geO) (passes := 0) h51
    (.assignSlot GeTab.tafel () (geIdx GeTab.tafel) geEins rfl geDarfTafel)
    (.ret .empty (List.Perm.refl _)) .nil rfl rfl (geHgLt rfl).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have h60 : M6.faeden 0 = M5.faeden 0 := rufSchrittG_fremd s6 0 (by decide)
  have e5' : M6.faeden 0 = _ := h60.trans e5
  have hsp6g : (M6.speicher.slots GeTab.geraet 0 ()).n = 0 := by
    rw [hZ6.2]
    show (M5.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ5.2]
    show (M4.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ4.2]
    show (M3.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hsp3]
    rfl
  -- second read: 0
  obtain ⟨M7, s7, hZ7⟩ := w_regLies (P := geP) (O := geO) (passes := 0) e5' () rfl _ _ _ rfl geNull
    (by show einpassen geO.zeiger (.int 0 1) ((M6.speicher.slots GeTab.geraet 0 ()).n) = some geNull
        rw [hsp6g]; rfl)
    rfl (geHgLg (geHoff_e e5' (by rw [h60]; exact hoff5))).heldIn
  have e7 := hZ7.1
  try dsimp only at e7
  have hoff7 : offen (M7.faeden 0).spur = [GeLock.lg] := by
    rw [hZ7.spur, geOffen_fragt, h60]; exact hoff5
  -- return `x == y`, which is `true`
  obtain ⟨M8, s8, hG8⟩ := w_dannRetP (P := geP) (O := geO) (passes := 0) e7 _ _ rfl
    (PopArt.wie rfl) _ (List.Perm.refl _) .nil _ _ rfl (geHgLg (geHoff_e e7 hoff7)).heldIn
  have hr8 : RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8
  refine ⟨M8, hr8, ?_, ?_, ?_, _, _, _, by rw [hG8.1]; exact List.mem_cons_self⟩
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.tafel 0 ()).n = 1
    rw [hZ7.2]
    show (M6.speicher.slots GeTab.tafel 0 ()).n = 1
    rw [hZ6.2]
    rfl
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ7.2]
    show (M6.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ6.2]
    show (M5.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ5.2]
    rfl
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ7.2]
    exact hsp6g

/-! ## 4. The witness -/

/-- **`ziel_ort_geraet_zeuge`.** On the two-thread program `geP` -- thread
    0 reads the device register `R` twice inside `leser`, which holds the
    device's lock `lg` by signature, with its own write to `notiz` between
    the reads; thread 1 writes the unrelated table `tafel` -- every premise
    of `ziel_ort_geraet` holds jointly: the hardware assumptions `GutO` and
    `RegLokal` for an oracle that answers the register from the device
    carrier (and so depends on memory), the complete member list, the
    widened fragment (outside the fragment of `ziel_ort_voll`), the widened
    footprint check, the user obligation `KoerperGutG` for all four
    functions (the reader's through register locality), the start
    obligation and the exclusive start. On a machine reached by eight steps
    -- with `tafel` and `notiz` changed between the two reads, `geraet`
    unchanged -- the return of `leser` with result `true` is logged, and
    the contracts hold at every logged entry and return. -/
theorem ziel_ort_geraet_zeuge :
    GutO geO ∧ RegLokal geO ∧ (∃ σ σ' : World geD, geO.regLies () σ ≠ geO.regLies () σ') ∧
    (∀ g : geD.Fn, g ∈ geFs) ∧ programmImFragmentG geP geFs = true ∧
    programmImFragmentV geP geFs = false ∧ fussOrtGB geP geFs = true ∧
    (∀ f : geD.Fn, KoerperGutG geP 0 f) ∧ StartGut geP geSp geInit ∧
    StartExklusiv (D := geD) geInit ∧
    ∃ M : RufMaschineG geD, RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M ∧
      (geSp.slots GeTab.tafel 0 ()).n = 0 ∧ (M.speicher.slots GeTab.tafel 0 ()).n = 1 ∧
      (geSp.slots GeTab.notiz 0 ()).n = 0 ∧ (M.speicher.slots GeTab.notiz 0 ()).n = 1 ∧
      (M.speicher.slots GeTab.geraet 0 ()).n = 0 ∧
      (∃ (rho : Env geD (geD.params geLeser)) (s0 s1 : World geD),
        RufEreignisF.rueck geLeser rho true s0 s1 ∈ (M.faeden 0).log) ∧
      VertragAmOrtG geP M := by
  obtain ⟨M, hr, ht, hn, hg, hlog⟩ := geLauf
  exact ⟨geO_gut, geO_lokal, geO_liest_speicher, geFs_voll, geP_fragment, geP_nicht_fragmentV,
    geP_fuss, geP_koerper, geP_start, geInit_exklusiv, M, hr, rfl, ht, rfl, hn, hg, hlog,
    geP_vertragAmOrt M hr⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_geraet` hold jointly on `geP`
  (`geP_vertragAmOrt` is the instance); the oracle is register-local and
  reads memory (`geO_lokal`, `geO_liest_speicher`); the reader's user
  obligation needs locality, since its own write lies between the two reads
  (`geLeser_lauf`); `geP` is outside the fragment of `ziel_ort_voll`
  (`geP_nicht_fragmentV`); a reached run of eight steps with both memory
  changes between the two reads and the logged return `true`
  (`geLauf`, `ziel_ort_geraet_zeuge`).

  What is NOT covered: no device-driven change of `geraet` in the run (the
  device carrier changes only through a declared write, and the witness has
  none); no `awaits` in the witness (the declaration has no global).
-/

#print axioms Gabbro.Grammatik.geO_lokal
#print axioms Gabbro.Grammatik.geP_koerper
#print axioms Gabbro.Grammatik.geP_vertragAmOrt
#print axioms Gabbro.Grammatik.geLauf
#print axioms Gabbro.Grammatik.ziel_ort_geraet_zeuge

end Gabbro.Grammatik
