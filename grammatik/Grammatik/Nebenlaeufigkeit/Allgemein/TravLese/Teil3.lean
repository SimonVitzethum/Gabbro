module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge
public import Grammatik.Nebenlaeufigkeit.Allgemein.TravLese.Teil2

@[expose] public section

namespace Gabbro.Grammatik.TravLese

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

/-- **`rennfrei_g_voll_zeuge`.** Every premise of `rennfrei_g_voll` jointly,
    on the run of `taP`, for a READ/WRITE pair at distance: thread 0 writes
    the lock-guarded global `flag` at step 16 (the publish, a memory change
    `0 -> 1`), thread 1 reads it at step 24 (the plain read, a recorded read
    event); `flag` is guarded by `k`, neither atomic nor a published payload;
    the conclusion orders the two through a release of `k` by thread 0 and
    an acquire by thread 1 in between. -/
theorem _root_.Gabbro.Grammatik.rennfrei_g_voll_zeuge : GutO taO ∧ StartExklusiv (D := taD) taInit ∧
    ∃ (ms : Nat → RufMaschineG taD) (fs : Nat → Faden),
      LaufG taP taO 0 (RufStartG taP taSp taInit) ms fs 29 ∧ fs 16 ≠ fs 24 ∧
      SchreibG (ms 16) (ms 17) (fs 16) (Sum.inr ()) ∧
      LiestG (ms 24) (ms 25) (fs 24) (Sum.inr ()) ∧
      Bewacht (D := taD) (Sum.inr ()) TaLock.k ∧ ¬ AtomarAusgenommen (D := taD) (Sum.inr ()) ∧
      ¬ PaarungAusgenommen (D := taD) (Sum.inr ()) ∧ GeordnetG ms fs TaLock.k 16 24 := by
  obtain ⟨ms, fs, hl, _, _, hf16, hf24, _, _, _, _, _, _, _, hm16, hm17, _, _, hread, _, _⟩ :=
    taLauf
  have hw : ¬ TraegerGleich (ms 17).speicher (ms 16).speicher (Sum.inr ()) := by
    intro h
    have h' : (ms 17).speicher.globs () = (ms 16).speicher.globs () := h
    have := congrArg Zahl.n h'
    rw [hm16, hm17] at this
    exact absurd this (by decide)
  have hfg : fs 16 ≠ fs 24 := by rw [hf16, hf24]; decide
  have hB : Bewacht (D := taD) (Sum.inr ()) TaLock.k := List.mem_singleton.mpr rfl
  have hr' : LiestG (ms 24) (ms 25) (fs 24) (Sum.inr ()) := by rw [hf24]; exact hread
  refine ⟨taO_gut, taInit_exklusiv, ms, fs, hl, hfg, Or.inr hw, hr', hB, ?_, ?_, ?_⟩
  · rintro ⟨g, _, h⟩
    cases h
  · rintro ⟨a, p, _, h, _⟩
    cases h
  · exact rennfrei_g_voll taP taO 0 taSp taInit taO_gut taInit_exklusiv ms fs 29 hl 16 24
      (by decide) (by decide) hfg (Sum.inr ()) TaLock.k hB (Or.inr hw) (Or.inl ⟨false, hr'⟩)

end Gabbro.Grammatik.TravLese

#print axioms Gabbro.Grammatik.TravLese.taLauf
#print axioms Gabbro.Grammatik.rennfrei_g_voll_zeuge
