module

public import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsZeuge.Teil2

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. Start states and small facts -/

def taI0 : Wert taD (.index (taD.count ())) := ⟨0, by decide, by decide⟩
def taI1 : Wert taD (.index (taD.count ())) := ⟨1, by decide, by decide⟩

theorem taAlle : alleIndizes (taD.count ()) = [taI0, taI1] := by rfl

def taM0 : RufMaschineG taD := RufStartG taP taSp taInit

def taZ0 : RufFadenG taD :=
  ⟨[], ⟨taHaupt0, .nil, taSp.welt [], ⟨false, [], taLL, .nil, .ende taRumpfHaupt0⟩⟩,
    startSpur taHaupt0, [RufEreignisF.eintritt taHaupt0 .nil (taSp.welt [])]⟩

def taZ1 : RufFadenG taD :=
  ⟨[], ⟨taHaupt1, .nil, taSp.welt [], ⟨false, [], [], .nil, .ende taRumpfHaupt1⟩⟩,
    startSpur taHaupt1, [RufEreignisF.eintritt taHaupt1 .nil (taSp.welt [])]⟩

theorem taM0_faden0 : taM0.faeden 0 = taZ0 := by rfl

theorem taM0_faden1 : taM0.faeden 1 = taZ1 := by rfl

/-- Threads other than 0 and 1 hold nothing at the start. -/
theorem taM0_offen (g : Faden) (h0 : g ≠ 0) (L : TaLock) : L ∉ offen (taM0.faeden g).spur := by
  intro h
  have h' := (offen_start (P := taP) taSp taInit g L).mp h
  rw [taInit_haelt, if_neg h0] at h'
  exact List.not_mem_nil h'

theorem taHgL {s : List (Ereignis taD)} (h : offen s = [TaLock.l]) :
    HeldGenau taLL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) taHeld_ne,
      fun h => absurd (List.mem_singleton.mp h) taLock_ne⟩

theorem taHgK {s : List (Ereignis taD)} (h : offen s = [TaLock.k]) :
    HeldGenau taKL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm taHeld_ne),
      fun h => absurd (List.mem_singleton.mp h) (Ne.symm taLock_ne)⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem taHgKL {s : List (Ereignis taD)} (h : offen s = [TaLock.k, TaLock.l]) :
    HeldGenau taKLL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_of_mem _ List.mem_cons_self,
      fun _ => List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem taHg0 {s : List (Ereignis taD)} (h : offen s = []) :
    HeldGenau ([] : List (Res taD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- The release marker after `haupt0`'s publish block. -/
def taKFrei : GRest taD (vertragVon taD taHaupt0) false [] taKLL :=
  .frei TaLock.k (.dann .nil (.ende taRetH0))

theorem taHoff {M : RufMaschineG taD} {f : Faden} {z : RufFadenG taD} {x : List TaLock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

/-! ## 2. Thread 0: 19 steps -/

/-- **Thread 0's part of the run.** From the start machine, 19 steps of
    thread 0: `haupt0` calls `fuelle` (1); `fuelle` unfolds its body (2) and
    the `traverse` (3, `dannTrav`); iteration `i = 0` (4 `travNext`, 5 the
    write `tab[0] := 1`, 6, 7 `travFort`); iteration `i = 1` (8, 9 the write
    `tab[1] := 1`, 10, 11); the loop exit (12 `travDone`, 13); the return of
    `fuelle`, logged (14); `haupt0` unfolds `locks k` (15, 16 takes `k`),
    publishes `flag := 1` (17), and releases `k` (18, 19). -/
theorem taLauf0 : ∃ L : List (RufMaschineG taD),
    L.getD 0 taM0 = taM0 ∧
    (∀ k, k < 19 → RufSchrittG taP taO 0 (L.getD k taM0) 0 (L.getD (k + 1) taM0)) ∧
    (∃ st rho s0 sp lg, (L.getD 2 taM0).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨false, [], taLL, .nil, .dann (.cons taTrav .nil) (.ende taRetF)⟩⟩, sp, lg⟩) ∧
    (∃ st rho s0 sp lg, (L.getD 3 taM0).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨false, [], taLL, .nil,
        .trav () .tru taTravBody (alleIndizes (taD.count ())) (.dann .nil (.ende taRetF))⟩⟩,
      sp, lg⟩) ∧
    (∃ st rho s0 sp lg, (L.getD 4 taM0).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨true, [.index (taD.count ())], taLL, .cons taI0 .nil,
        .dann taTravBody (.travRest () .tru taTravBody [taI1] (.dann .nil (.ende taRetF)))⟩⟩,
      sp, lg⟩) ∧
    ((L.getD 4 taM0).speicher.slots () 0 ()).n = 0 ∧
    ((L.getD 5 taM0).speicher.slots () 0 ()).n = 1 ∧
    ((L.getD 8 taM0).speicher.slots () 1 ()).n = 0 ∧
    ((L.getD 9 taM0).speicher.slots () 1 ()).n = 1 ∧
    ((L.getD 16 taM0).speicher.globs ()).n = 0 ∧
    ((L.getD 17 taM0).speicher.globs ()).n = 1 ∧
    (∃ (rho : Env taD (taD.params taFuelle)) (s0 s1 : World taD),
      RufEreignisF.rueck taFuelle rho () s0 s1 ∈ ((L.getD 19 taM0).faeden 0).log) ∧
    (L.getD 19 taM0).faeden 1 = taZ1 ∧
    offen ((L.getD 19 taM0).faeden 0).spur = [TaLock.l] ∧
    ((L.getD 19 taM0).speicher.globs ()).n = 1 ∧
    (∀ g, g ≠ 0 → (L.getD 19 taM0).faeden g = taM0.faeden g) := by
  have h00 : taM0.faeden 0 = ⟨[], ⟨taHaupt0, .nil, taSp.welt [], ⟨false, [], taLL, .nil, .ende taRumpfHaupt0⟩⟩, startSpur taHaupt0, [RufEreignisF.eintritt taHaupt0 .nil (taSp.welt [])]⟩ := rfl
  have hoff0 : offen (taM0.faeden 0).spur = [TaLock.l] := rfl
  -- 1: `haupt0` calls `fuelle`
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := taP) (O := taO) (passes := 0) h00 taFuelle .nil
    taHpFuelle rfl taRestH0 .nil rfl (taHgL hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [TaLock.l] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: unfold the body of `fuelle`
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := taP) (O := taO) (passes := 0) e1 taTrav taRetF .nil
    rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [TaLock.l] := by rw [hZ2.spur]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: `dannTrav`
  obtain ⟨M3, s3, hZ3⟩ := w_dannTrav (P := taP) (O := taO) (passes := 0) e2 () .tru taTravBody
    .nil (.ende taRetF) .nil rfl
  have hoff3 : offen (M3.faeden 0).spur = [TaLock.l] := by rw [hZ3.spur]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  -- 4: `travNext`, index 0
  obtain ⟨M4, s4, hZ4⟩ := w_travNext (P := taP) (O := taO) (passes := 0) e3 () .tru taTravBody
    taI0 [taI1] (.dann .nil (.ende taRetF)) .nil rfl rfl (taHgL (taHoff e3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [TaLock.l] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen]; exact hoff3
  have e4 := hZ4.1
  try dsimp only at e4
  -- 5: `tab[0] := 1`
  obtain ⟨M5, s5, hZ5⟩ := w_dannBlatt (P := taP) (O := taO) (passes := 0) e4 taSchreibI .nil
    (.travRest () .tru taTravBody [taI1] (.dann .nil (.ende taRetF))) (.cons taI0 .nil) rfl rfl
    (taHgL (taHoff e4 hoff4)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden 0).spur = [TaLock.l] := by
    rw [hZ5.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff4)
  have e5 := hZ5.1
  try dsimp only at e5
  -- 6: `dannLeer`
  obtain ⟨M6, s6, hZ6⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e5
    (.travRest () .tru taTravBody [taI1] (.dann .nil (.ende taRetF))) (.cons taI0 .nil) rfl
  have hoff6 : offen (M6.faeden 0).spur = [TaLock.l] := by rw [hZ6.spur]; exact hoff5
  have e6 := hZ6.1
  try dsimp only at e6
  -- 7: `travFort`
  obtain ⟨M7, s7, hZ7⟩ := w_travFort (P := taP) (O := taO) (passes := 0) e6 () .tru taTravBody
    [taI1] (.dann .nil (.ende taRetF)) taI0 .nil rfl
  have hoff7 : offen (M7.faeden 0).spur = [TaLock.l] := by rw [hZ7.spur]; exact hoff6
  have e7 := hZ7.1
  try dsimp only at e7
  -- 8: `travNext`, index 1
  obtain ⟨M8, s8, hZ8⟩ := w_travNext (P := taP) (O := taO) (passes := 0) e7 () .tru taTravBody
    taI1 [] (.dann .nil (.ende taRetF)) .nil rfl rfl (taHgL (taHoff e7 hoff7)).heldIn
  have hoff8 : offen (M8.faeden 0).spur = [TaLock.l] := by
    rw [hZ8.spur, (Erw.lese _ _ _).offen]; exact hoff7
  have e8 := hZ8.1
  try dsimp only at e8
  -- 9: `tab[1] := 1`
  obtain ⟨M9, s9, hZ9⟩ := w_dannBlatt (P := taP) (O := taO) (passes := 0) e8 taSchreibI .nil
    (.travRest () .tru taTravBody [] (.dann .nil (.ende taRetF))) (.cons taI1 .nil) rfl rfl
    (taHgL (taHoff e8 hoff8)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff9 : offen (M9.faeden 0).spur = [TaLock.l] := by
    rw [hZ9.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff8)
  have e9 := hZ9.1
  try dsimp only at e9
  -- 10: `dannLeer`
  obtain ⟨M10, s10, hZ10⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e9
    (.travRest () .tru taTravBody [] (.dann .nil (.ende taRetF))) (.cons taI1 .nil) rfl
  have hoff10 : offen (M10.faeden 0).spur = [TaLock.l] := by rw [hZ10.spur]; exact hoff9
  have e10 := hZ10.1
  try dsimp only at e10
  -- 11: `travFort`
  obtain ⟨M11, s11, hZ11⟩ := w_travFort (P := taP) (O := taO) (passes := 0) e10 () .tru
    taTravBody [] (.dann .nil (.ende taRetF)) taI1 .nil rfl
  have hoff11 : offen (M11.faeden 0).spur = [TaLock.l] := by rw [hZ11.spur]; exact hoff10
  have e11 := hZ11.1
  try dsimp only at e11
  -- 12: `travDone`
  obtain ⟨M12, s12, hZ12⟩ := w_travDone (P := taP) (O := taO) (passes := 0) e11 () .tru
    taTravBody (.dann .nil (.ende taRetF)) .nil rfl rfl (taHgL (taHoff e11 hoff11)).heldIn
  have hoff12 : offen (M12.faeden 0).spur = [TaLock.l] := by
    rw [hZ12.spur, (Erw.lese _ _ _).offen]; exact hoff11
  have e12 := hZ12.1
  try dsimp only at e12
  -- 13: `dannLeer`
  obtain ⟨M13, s13, hZ13⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e12
    (.ende taRetF) .nil rfl
  have hoff13 : offen (M13.faeden 0).spur = [TaLock.l] := by rw [hZ13.spur]; exact hoff12
  have e13 := hZ13.1
  try dsimp only at e13
  -- 14: `fuelle` returns into `haupt0`
  obtain ⟨M14, s14, hG14⟩ := w_rueckP (P := taP) (O := taO) (passes := 0) e13 _ _ rfl
    (PopArt.wie rfl) .empty (List.Perm.refl _) .nil rfl (taHgL (taHoff e13 hoff13)).heldIn
  have hoff14 : offen (M14.faeden 0).spur = [TaLock.l] := by
    rw [hG14.1]; exact ((Erw.lese _ _ _).offen).trans hoff13
  have e14 := hG14.1
  try dsimp only at e14
  -- 15: unfold `locks k`
  obtain ⟨M15, s15, hZ15⟩ := w_endeEntf (P := taP) (O := taO) (passes := 0) e14 taLocksK taRetH0
    .nil rfl rfl
  have hoff15 : offen (M15.faeden 0).spur = [TaLock.l] := by rw [hZ15.spur]; exact hoff14
  have e15 := hZ15.1
  try dsimp only at e15
  -- the other threads are untouched by thread 0
  have hfremd15 : ∀ g, g ≠ 0 → M15.faeden g = taM0.faeden g := by
    intro g hg
    rw [rufSchrittG_fremd s15 g hg, rufSchrittG_fremd s14 g hg, rufSchrittG_fremd s13 g hg,
      rufSchrittG_fremd s12 g hg, rufSchrittG_fremd s11 g hg, rufSchrittG_fremd s10 g hg,
      rufSchrittG_fremd s9 g hg, rufSchrittG_fremd s8 g hg, rufSchrittG_fremd s7 g hg,
      rufSchrittG_fremd s6 g hg, rufSchrittG_fremd s5 g hg, rufSchrittG_fremd s4 g hg,
      rufSchrittG_fremd s3 g hg, rufSchrittG_fremd s2 g hg, rufSchrittG_fremd s1 g hg]
  -- 16: take `k`
  obtain ⟨M16, s16, hZ16⟩ := w_locks (P := taP) (O := taO) (passes := 0) e15 TaLock.k taRangK
    taPubBody .nil (.ende taRetH0) .nil rfl (taHgL (taHoff e15 hoff15))
    (fun g hg => by rw [hfremd15 g hg]; exact taM0_offen g hg TaLock.k)
  have hoff16 : offen (M16.faeden 0).spur = [TaLock.k, TaLock.l] := by
    rw [hZ16.spur]
    show offen (Ereignis.nimmt TaLock.k (offen (M15.weltVon 0).spur) :: (M15.weltVon 0).spur) =
      [TaLock.k, TaLock.l]
    simp only [offen]
    show TaLock.k :: offen (M15.faeden 0).spur = [TaLock.k, TaLock.l]
    rw [hoff15]
  have e16 := hZ16.1
  try dsimp only at e16
  -- 17: publish `flag := 1`
  obtain ⟨M17, s17, hZ17⟩ := w_dannBlatt (P := taP) (O := taO) (passes := 0) e16 taPub .nil
    taKFrei .nil rfl rfl (taHgKL (taHoff e16 hoff16)).heldIn
    _ _ rfl ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _))
  have hoff17 : offen (M17.faeden 0).spur = [TaLock.k, TaLock.l] := by
    rw [hZ17.spur]
    exact ((Erw.schreibGlob _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff16)
  have e17 := hZ17.1
  try dsimp only at e17
  -- 18: `dannLeer`
  obtain ⟨M18, s18, hZ18⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e17
    taKFrei .nil rfl
  have hoff18 : offen (M18.faeden 0).spur = [TaLock.k, TaLock.l] := by
    rw [hZ18.spur]; exact hoff17
  have e18 := hZ18.1
  try dsimp only at e18
  -- 19: release `k`
  obtain ⟨M19, s19, hZ19⟩ := w_freiGib (P := taP) (O := taO) (passes := 0) e18 TaLock.k
    (.dann .nil (.ende taRetH0)) .nil rfl
  have hoff19 : offen (M19.faeden 0).spur = [TaLock.l] := by
    rw [hZ19.spur]
    show (offen (M18.faeden 0).spur).erase TaLock.k = [TaLock.l]
    rw [hoff18]
    rfl
  -- memory
  have hsp4 : M4.speicher = taSp := hZ4.2.trans (hZ3.2.trans (hZ2.2.trans hZ1.2))
  have hsp8 : M8.speicher = M5.speicher := hZ8.2.trans (hZ7.2.trans (hZ6.2))
  have hsp16 : M16.speicher = M9.speicher :=
    hZ16.2.trans (hZ15.2.trans (hG14.2.trans (hZ13.2.trans (hZ12.2.trans (hZ11.2.trans
      hZ10.2)))))
  have hsp19 : M19.speicher = M17.speicher := hZ19.2.trans hZ18.2
  refine ⟨[taM0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, M16, M17,
    M18, M19], rfl, ?_, ⟨_, _, _, _, _, e2⟩, ⟨_, _, _, _, _, e3⟩, ⟨_, _, _, _, _, e4⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | 2, _ => exact s3
    | 3, _ => exact s4
    | 4, _ => exact s5
    | 5, _ => exact s6
    | 6, _ => exact s7
    | 7, _ => exact s8
    | 8, _ => exact s9
    | 9, _ => exact s10
    | 10, _ => exact s11
    | 11, _ => exact s12
    | 12, _ => exact s13
    | 13, _ => exact s14
    | 14, _ => exact s15
    | 15, _ => exact s16
    | 16, _ => exact s17
    | 17, _ => exact s18
    | 18, _ => exact s19
    | n + 19, h => exact absurd h (by omega)
  · show (M4.speicher.slots () 0 ()).n = 0
    rw [hsp4]; rfl
  · show (M5.speicher.slots () 0 ()).n = 1
    rw [hZ5.2]; rfl
  · show (M8.speicher.slots () 1 ()).n = 0
    rw [hsp8, hZ5.2]
    show ((M4.speicher.slots () 1 ())).n = 0
    rw [hsp4]; rfl
  · show (M9.speicher.slots () 1 ()).n = 1
    rw [hZ9.2]; rfl
  · show (M16.speicher.globs ()).n = 0
    rw [hsp16, hZ9.2]
    show (M8.speicher.globs ()).n = 0
    rw [hsp8, hZ5.2]
    show (M4.speicher.globs ()).n = 0
    rw [hsp4]; rfl
  · show (M17.speicher.globs ()).n = 1
    rw [hZ17.2]; rfl
  · show ∃ (rho : Env taD (taD.params taFuelle)) (s0 s1 : World taD),
      RufEreignisF.rueck taFuelle rho () s0 s1 ∈ (M19.faeden 0).log
    have hlog : (M19.faeden 0).log = (M14.faeden 0).log :=
      (congrArg RufFadenG.log hZ19.1).trans ((congrArg RufFadenG.log e18).symm.trans
        ((congrArg RufFadenG.log hZ18.1).trans ((congrArg RufFadenG.log e17).symm.trans
          ((congrArg RufFadenG.log hZ17.1).trans ((congrArg RufFadenG.log e16).symm.trans
            ((congrArg RufFadenG.log hZ16.1).trans ((congrArg RufFadenG.log e15).symm.trans
              ((congrArg RufFadenG.log hZ15.1).trans (congrArg RufFadenG.log e14).symm))))))))
    rw [hlog, hG14.1]
    exact ⟨_, _, _, List.mem_cons_self⟩
  · show M19.faeden 1 = taZ1
    rw [rufSchrittG_fremd s19 1 (by decide), rufSchrittG_fremd s18 1 (by decide),
      rufSchrittG_fremd s17 1 (by decide), rufSchrittG_fremd s16 1 (by decide),
      hfremd15 1 (by decide)]
    rfl
  · exact hoff19
  · show (M19.speicher.globs ()).n = 1
    rw [hsp19, hZ17.2]; rfl
  · intro g hg
    show M19.faeden g = taM0.faeden g
    rw [rufSchrittG_fremd s19 g hg, rufSchrittG_fremd s18 g hg,
      rufSchrittG_fremd s17 g hg, rufSchrittG_fremd s16 g hg, hfremd15 g hg]

/-! ## 3. Thread 1: 10 steps -/

theorem taRang0 : ∀ M, Res.held M ∈ ([] : List (Res taD)) → taD.rang M < taD.rang TaLock.k :=
  fun _ h => nomatch h

/-- The release marker after `haupt1`'s `locks k` block. -/
def taKFrei1 : GRest taD (vertragVon taD taHaupt1) false [] taKL :=
  .frei TaLock.k (.dann .nil (.ende taRetH1))

/-- **Thread 1's part of the run.** From any machine where thread 1 is at
    its start, `flag` is `1`, and no other thread holds `k`: 10 steps of
    thread 1 -- unfold `locks k` (1), take `k` (2), call `warte` (3), unfold
    its `if` (4, 5), fire `awaits` reading `flag` (6), close the blocks
    (7, 8, 9), return to `haupt1`, logged (10). -/
end Gabbro.Grammatik
