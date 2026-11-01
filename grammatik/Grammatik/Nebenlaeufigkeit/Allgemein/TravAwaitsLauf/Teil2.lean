module

public import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsZeuge.Teil2
public import Grammatik.Nebenlaeufigkeit.Allgemein.TravAwaitsLauf.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem taLauf1 (M : RufMaschineG taD) (h1 : M.faeden 1 = taZ1)
    (hflag : (M.speicher.globs ()).n = 1)
    (hfrei : ∀ g, g ≠ 1 → TaLock.k ∉ offen (M.faeden g).spur) :
    ∃ L : List (RufMaschineG taD),
    L.getD 0 M = M ∧
    (∀ k, k < 10 → RufSchrittG taP taO 0 (L.getD k M) 1 (L.getD (k + 1) M)) ∧
    (∃ st rho s0 sp lg, (L.getD 5 M).faeden 1 = ⟨st, ⟨taWarte, rho, s0,
      ⟨false, [], taKL, .nil, .dann taAwaitsBlock (.dann .nil (.ende taRetW))⟩⟩, sp, lg⟩) ∧
    (∃ v : Wert taD (.int 0 1), ∃ st rho s0 sp lg, v.n = 1 ∧ (L.getD 6 M).faeden 1 =
      ⟨st, ⟨taWarte, rho, s0, ⟨false, [.int 0 1], taKL, .cons v .nil,
        .dann .nil (.schrumpf (.dann .nil (.ende taRetW)))⟩⟩, sp, lg⟩) ∧
    (Sum.inr (), false) ∈ zugriffe (L.getD 5 M) (L.getD 6 M) 1 ∧
    (∃ (rho : Env taD (taD.params taWarte)) (s0 s1 : World taD),
      RufEreignisF.rueck taWarte rho () s0 s1 ∈ ((L.getD 10 M).faeden 1).log) := by
  have h10 : M.faeden 1 = ⟨[], ⟨taHaupt1, .nil, taSp.welt [], ⟨false, [], [], .nil,
      .ende taRumpfHaupt1⟩⟩, startSpur taHaupt1,
      [RufEreignisF.eintritt taHaupt1 .nil (taSp.welt [])]⟩ := h1
  have hoff0 : offen (M.faeden 1).spur = [] := by rw [h1]; rfl
  -- 1: unfold `locks k`
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := taP) (O := taO) (passes := 0) h10 taLocksH taRetH1
    .nil rfl rfl
  have hoff1 : offen (M1.faeden 1).spur = [] := by rw [hZ1.spur]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: take `k`
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := taP) (O := taO) (passes := 0) e1 TaLock.k
    taRang0 taWarteBody .nil (.ende taRetH1) .nil rfl (taHg0 (taHoff e1 hoff1))
    (fun g hg => by rw [rufSchrittG_fremd s1 g hg]; exact hfrei g hg)
  have hoff2 : offen (M2.faeden 1).spur = [TaLock.k] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt TaLock.k (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) =
      [TaLock.k]
    simp only [offen]
    show TaLock.k :: offen (M1.faeden 1).spur = [TaLock.k]
    rw [hoff1]
    rfl
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: call `warte`
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := taP) (O := taO) (passes := 0) e2 taWarte .nil
    taHpWarte rfl .nil taKFrei1 .nil rfl (taHgK (taHoff e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [TaLock.k] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  -- 4: unfold the `if`
  obtain ⟨M4, s4, hZ4⟩ := w_endeEntf (P := taP) (O := taO) (passes := 0) e3 taIteW taRetW .nil
    rfl rfl
  have hoff4 : offen (M4.faeden 1).spur = [TaLock.k] := by rw [hZ4.spur]; exact hoff3
  have e4 := hZ4.1
  try dsimp only at e4
  -- 5: its `true` branch
  obtain ⟨M5, s5, hZ5⟩ := w_iteWahr (P := taP) (O := taO) (passes := 0) e4 .tru taAwaitsBlock
    .nil .nil (.ende taRetW) .nil rfl rfl (taHgK (taHoff e4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [TaLock.k] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen]; exact hoff4
  have e5 := hZ5.1
  try dsimp only at e5
  have hsp5 : M5.speicher = M.speicher :=
    hZ5.2.trans (hZ4.2.trans (hZ3.2.trans (hZ2.2.trans hZ1.2)))
  -- 6: `awaits` fires: the publication is visible
  obtain ⟨M6, s6, hZ6⟩ := w_awaits (P := taP) (O := taO) (passes := 0) e5 () [] rfl taGdarfK rfl
    .nil (.dann .nil (.ende taRetW)) .nil rfl
    (by show decide ((M5.speicher.globs ()).n = 1) = true
        rw [hsp5, hflag]; rfl)
    (taHgK (taHoff e5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [TaLock.k] := by
    rw [hZ6.spur, (Erw.lese _ _ _).offen]; exact hoff5
  have e6 := hZ6.1
  try dsimp only at e6
  -- 7, 8, 9: close the blocks
  obtain ⟨M7, s7, hZ7⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e6
    (.schrumpf (.dann .nil (.ende taRetW))) _ rfl
  have hoff7 : offen (M7.faeden 1).spur = [TaLock.k] := by rw [hZ7.spur]; exact hoff6
  have e7 := hZ7.1
  try dsimp only at e7
  obtain ⟨M8, s8, hZ8⟩ := w_schrumpf (P := taP) (O := taO) (passes := 0) e7
    (.dann .nil (.ende taRetW)) _ .nil rfl
  have hoff8 : offen (M8.faeden 1).spur = [TaLock.k] := by rw [hZ8.spur]; exact hoff7
  have e8 := hZ8.1
  try dsimp only at e8
  obtain ⟨M9, s9, hZ9⟩ := w_dannLeer (P := taP) (O := taO) (passes := 0) e8 (.ende taRetW) .nil rfl
  have hoff9 : offen (M9.faeden 1).spur = [TaLock.k] := by rw [hZ9.spur]; exact hoff8
  have e9 := hZ9.1
  try dsimp only at e9
  -- 10: `warte` returns into `haupt1`
  obtain ⟨M10, s10, hG10⟩ := w_rueckP (P := taP) (O := taO) (passes := 0) e9 _ _ rfl
    (PopArt.wie rfl) .empty (List.Perm.refl _) .nil rfl (taHgK (taHoff e9 hoff9)).heldIn
  refine ⟨[M, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10], rfl, ?_, ⟨_, _, _, _, _, e5⟩,
    ⟨_, _, _, _, _, _, ?_, e6⟩, ?_, ?_⟩
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
    | n + 10, h => exact absurd h (by omega)
  · show (M5.speicher.globs ()).n = 1
    rw [hsp5, hflag]
  · show (Sum.inr (), false) ∈ zugriffe M5 M6 1
    have hX : (M6.faeden 1).spur =
        (leseEv ((M5.weltVon 1).fragt (Sum.inr (Sum.inr ()))) taKL [Sum.inr ()] ++
          [Ereignis.fremd (Sum.inr (Sum.inr ()))]) ++ (M5.faeden 1).spur := by
      rw [hZ6.spur, List.append_assoc]; rfl
    rw [zugriffe_ereignisse, ereignisse_eq hX]
    exact List.mem_cons_self
  · show ∃ (rho : Env taD (taD.params taWarte)) (s0 s1 : World taD),
      RufEreignisF.rueck taWarte rho () s0 s1 ∈ (M10.faeden 1).log
    rw [hG10.1]
    exact ⟨_, _, _, List.mem_cons_self⟩

/-! ## 4. The whole run by index -/

/-- **The run of `taP`, by index** (29 steps from the start machine): steps
    0-18 by thread 0, steps 19-28 by thread 1. Step 2 fires `dannTrav`
    (the head residue goes from the unfolded `traverse` to the loop state),
    step 3 fires `travNext` (index 0 bound, the body scheduled); steps 4 and
    8 write `tab[0]` and `tab[1]` (`0 -> 1`); step 16 publishes `flag := 1`
    (`0 -> 1`); step 24 fires `dannAwaits` (thread 1 reads `flag`, the
    bound value is `1`); the returns of `fuelle` and `warte` are logged. -/
theorem taLauf : ∃ (ms : Nat → RufMaschineG taD) (fs : Nat → Faden),
    LaufG taP taO 0 (RufStartG taP taSp taInit) ms fs 29 ∧
    fs 2 = 0 ∧ fs 3 = 0 ∧ fs 16 = 0 ∧ fs 24 = 1 ∧
    (∃ st rho s0 sp lg, (ms 2).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨false, [], taLL, .nil, .dann (.cons taTrav .nil) (.ende taRetF)⟩⟩, sp, lg⟩) ∧
    (∃ st rho s0 sp lg, (ms 3).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨false, [], taLL, .nil,
        .trav () .tru taTravBody (alleIndizes (taD.count ())) (.dann .nil (.ende taRetF))⟩⟩,
      sp, lg⟩) ∧
    (∃ st rho s0 sp lg, (ms 4).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
      ⟨true, [.index (taD.count ())], taLL, .cons taI0 .nil,
        .dann taTravBody (.travRest () .tru taTravBody [taI1] (.dann .nil (.ende taRetF)))⟩⟩,
      sp, lg⟩) ∧
    ((ms 4).speicher.slots () 0 ()).n = 0 ∧ ((ms 5).speicher.slots () 0 ()).n = 1 ∧
    ((ms 8).speicher.slots () 1 ()).n = 0 ∧ ((ms 9).speicher.slots () 1 ()).n = 1 ∧
    ((ms 16).speicher.globs ()).n = 0 ∧ ((ms 17).speicher.globs ()).n = 1 ∧
    (∃ st rho s0 sp lg, (ms 24).faeden 1 = ⟨st, ⟨taWarte, rho, s0,
      ⟨false, [], taKL, .nil, .dann taAwaitsBlock (.dann .nil (.ende taRetW))⟩⟩, sp, lg⟩) ∧
    (∃ v : Wert taD (.int 0 1), ∃ st rho s0 sp lg, v.n = 1 ∧ (ms 25).faeden 1 =
      ⟨st, ⟨taWarte, rho, s0, ⟨false, [.int 0 1], taKL, .cons v .nil,
        .dann .nil (.schrumpf (.dann .nil (.ende taRetW)))⟩⟩, sp, lg⟩) ∧
    LiestG (ms 24) (ms 25) 1 (Sum.inr ()) ∧
    (∃ (rho : Env taD (taD.params taFuelle)) (s0 s1 : World taD),
      RufEreignisF.rueck taFuelle rho () s0 s1 ∈ ((ms 29).faeden 0).log) ∧
    (∃ (rho : Env taD (taD.params taWarte)) (s0 s1 : World taD),
      RufEreignisF.rueck taWarte rho () s0 s1 ∈ ((ms 29).faeden 1).log) := by
  obtain ⟨L0, h0a, h0s, hk2, hk3, hk4, hm4, hm5, hm8, hm9, hm16, hm17, hlog0, h19_1, hoff19,
    hflag19, hfremd19⟩ := taLauf0
  have hfrei : ∀ g, g ≠ 1 → TaLock.k ∉ offen ((L0.getD 19 taM0).faeden g).spur := by
    intro g hg
    by_cases h0 : g = 0
    · subst h0
      rw [hoff19]
      intro h
      exact taLock_ne (List.mem_singleton.mp h)
    · rw [hfremd19 g h0]
      exact taM0_offen g h0 TaLock.k
  obtain ⟨L1, h1a, h1s, ha5, ha6, hread, hlog1⟩ := taLauf1 (L0.getD 19 taM0) h19_1 hflag19 hfrei
  have hl0 : LaufG taP taO 0 taM0 (fun k => L0.getD k taM0) (fun _ => 0) 19 := ⟨h0a, h0s⟩
  have hl1 : LaufG taP taO 0 ((fun k => L0.getD k taM0) 19)
      (fun k => L1.getD k (L0.getD 19 taM0)) (fun _ => 1) 10 := ⟨h1a, h1s⟩
  have hl := laufG_verketten hl0 hl1
  have h29 : (L1.getD 10 (L0.getD 19 taM0)).faeden 0 = (L0.getD 19 taM0).faeden 0 :=
    laufG_fremd hl1 0 (fun _ _ => by decide) 10 (Nat.le_refl _)
  refine ⟨_, _, hl, rfl, rfl, rfl, rfl, hk2, hk3, hk4, hm4, hm5, hm8, hm9, hm16, hm17, ha5, ha6,
    hread, ?_, hlog1⟩
  show ∃ (rho : Env taD (taD.params taFuelle)) (s0 s1 : World taD),
    RufEreignisF.rueck taFuelle rho () s0 s1 ∈ ((L1.getD 10 (L0.getD 19 taM0)).faeden 0).log
  rw [h29]
  exact hlog0

/-! ## 5. The witnesses -/

/-- **`trav_awaits_zeuge`: reached runs that fire `traverse` and `awaits`,
    jointly with every premise of `ziel_ort_geraet`.** On the two-thread
    program `taP` -- `fuelle` (non-trivial `ensures`: every slot of `tab`
    is `1`) writes each slot in a `traverse`, `haupt0` publishes `flag`
    under `k`, thread 1 `awaits` it under `k` -- every premise holds
    (good, register-local oracle whose visibility answer reads memory; the
    complete member list; the widened fragment; the widened footprint
    check; `KoerperGutG` for all five functions; the start obligation; the
    exclusive start); the 29-step run fires `dannTrav` (step 2), `travNext`
    (step 3), writes both slots (steps 4, 8), publishes (step 16) and fires
    `dannAwaits` (step 24); every machine of the run satisfies the contracts
    at their place, in particular the logged return of `fuelle`, whose
    `ensures` is the non-trivial one. -/
theorem trav_awaits_zeuge :
    GutO taO ∧ RegLokal taO ∧ (∃ σ σ' : World taD, taO.sichtbar () σ ≠ taO.sichtbar () σ') ∧
    (∀ g : taD.Fn, g ∈ taFs) ∧ programmImFragmentG taP taFs = true ∧
    fussOrtGB taP taFs = true ∧ (∀ f : taD.Fn, KoerperGutG taP 0 f) ∧
    StartGut taP taSp taInit ∧ StartExklusiv (D := taD) taInit ∧
    taP.ensures taFuelle = taEnsFuelle ∧
    ∃ (ms : Nat → RufMaschineG taD) (fs : Nat → Faden),
      LaufG taP taO 0 (RufStartG taP taSp taInit) ms fs 29 ∧
      fs 2 = 0 ∧ fs 3 = 0 ∧ fs 24 = 1 ∧
      (∃ st rho s0 sp lg, (ms 2).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
        ⟨false, [], taLL, .nil, .dann (.cons taTrav .nil) (.ende taRetF)⟩⟩, sp, lg⟩) ∧
      (∃ st rho s0 sp lg, (ms 3).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
        ⟨false, [], taLL, .nil,
          .trav () .tru taTravBody (alleIndizes (taD.count ())) (.dann .nil (.ende taRetF))⟩⟩,
        sp, lg⟩) ∧
      (∃ st rho s0 sp lg, (ms 4).faeden 0 = ⟨st, ⟨taFuelle, rho, s0,
        ⟨true, [.index (taD.count ())], taLL, .cons taI0 .nil,
          .dann taTravBody (.travRest () .tru taTravBody [taI1] (.dann .nil (.ende taRetF)))⟩⟩,
        sp, lg⟩) ∧
      ((ms 4).speicher.slots () 0 ()).n = 0 ∧ ((ms 5).speicher.slots () 0 ()).n = 1 ∧
      ((ms 8).speicher.slots () 1 ()).n = 0 ∧ ((ms 9).speicher.slots () 1 ()).n = 1 ∧
      ((ms 16).speicher.globs ()).n = 0 ∧ ((ms 17).speicher.globs ()).n = 1 ∧
      (∃ st rho s0 sp lg, (ms 24).faeden 1 = ⟨st, ⟨taWarte, rho, s0,
        ⟨false, [], taKL, .nil, .dann taAwaitsBlock (.dann .nil (.ende taRetW))⟩⟩, sp, lg⟩) ∧
      (∃ v : Wert taD (.int 0 1), ∃ st rho s0 sp lg, v.n = 1 ∧ (ms 25).faeden 1 =
        ⟨st, ⟨taWarte, rho, s0, ⟨false, [.int 0 1], taKL, .cons v .nil,
          .dann .nil (.schrumpf (.dann .nil (.ende taRetW)))⟩⟩, sp, lg⟩) ∧
      (∃ (rho : Env taD (taD.params taFuelle)) (s0 s1 : World taD),
        RufEreignisF.rueck taFuelle rho () s0 s1 ∈ ((ms 29).faeden 0).log ∧
        EnsAmRueck taP taFuelle s0 s1 rho ()) ∧
      ∀ k, k ≤ 29 → VertragAmOrtG taP (ms k) := by
  obtain ⟨ms, fs, hl, hf2, hf3, _, hf24, hk2, hk3, hk4, hm4, hm5, hm8, hm9, hm16, hm17, ha24,
    ha25, _, ⟨rho, s0, s1, hlog⟩, _⟩ := taLauf
  have hV : ∀ k, k ≤ 29 → VertragAmOrtG taP (ms k) :=
    fun k hk => taP_vertragAmOrt (ms k) (laufG_erreichbar hl k hk)
  have hens : EnsAmRueck taP taFuelle s0 s1 rho () :=
    ((hV 29 (Nat.le_refl _)) 0 _ hlog).2 taFuelle rho () s0 s1 rfl
  exact ⟨taO_gut, taO_lokal, taO_liest_speicher, taFs_voll, taP_fragment, taP_fuss, taP_koerper,
    taP_start, taInit_exklusiv, rfl, ms, fs, hl, hf2, hf3, hf24, hk2, hk3, hk4, hm4, hm5, hm8,
    hm9, hm16, hm17, ha24, ha25, ⟨rho, s0, s1, hlog, hens⟩, hV⟩

/-! ## CUTS:

  What is proved: the run of `taP` by index (`taLauf`, 29 steps: thread 0's
  19 steps `taLauf0`, thread 1's 10 steps `taLauf1`, glued by
  `laufG_verketten`), firing `dannTrav`, `travNext` (twice), `travFort`,
  `travDone`, the slot writes, `dannLocks`, the publish, `freiGib`,
  `rufDann`, `dannIteWahr`, `dannAwaits`, `schrumpfVergiss` and two returns;
  every premise of `ziel_ort_geraet` jointly with the run and the
  conclusion on every machine of it (`trav_awaits_zeuge`), including the
  logged return of `fuelle` with its non-trivial `ensures`. The witness of
  `rennfrei_g_voll` (a read/write pair at distance 8 through a
  release/acquire of `k`) needs a non-atomic carrier and lives on the copy
  of this run with a plain read (`TravLese.lean`).

  What is NOT covered: `forever` (no reached run fires `dannForever`); the
  `leave`/`next` exits of a `traverse` (`dannLeaveTrav`, `dannNextTrav`);
  a `traverse` whose `invariant` is not `true`. The "fires" facts are
  stated as the head residue before and after the step (the rule itself is
  not named by the step relation); the step from a `.dann (.cons
  (.traverse …) …)` head to a `.trav` head is `dannTrav` by the shape of
  the rules. The publish/awaits pair runs under the lock `k` (the
  footprint check `fussOrtGB` puts the awaited global into `warte`'s
  footprint, so its guard must be held by signature); `flag` is atomic (an
  `awaits` needs an atomic static) and guarded by `k` as well, so the run
  does not exercise the lock-free discipline of an unguarded atomic.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.taLauf0
#print axioms Gabbro.Grammatik.taLauf1
#print axioms Gabbro.Grammatik.taLauf
#print axioms Gabbro.Grammatik.trav_awaits_zeuge
