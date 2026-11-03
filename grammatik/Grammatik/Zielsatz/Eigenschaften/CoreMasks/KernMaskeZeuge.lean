/-
  File:      Grammatik/Zielsatz/Eigenschaften/KernMaskeZeuge.lean
  Subject:   The witnesses of the per-core mask state (`KernMaske.lean`): ONE program, two
             declarations that differ in nothing but whether its lock is declared `masks irqs`.

  The fixture is the smallest one that has the shape of `beispiele/gift/460`: one lock `()`,
  two functions with the same body `locks () { }; return`, `h` an interrupt handler
  (`Programm.unterbricht`) and `t` an ordinary function. The declaration `wD m` has
  `maskiert := fun _ => m`; the start has thread 0 running `h` and thread 1 running `t`, both on
  core 0 (`wk`).

  * `ohne_maske_verklemmt` (`m = false`): thread 1 takes the lock, the entry guard admits the
    handler (the core is unmasked), the handler stands at a lock its core's thread holds and
    waits for it (`WartetG`), every other thread is held back by run to completion, and
    `KernHaltM` is FALSE at the machine reached. The checker side agrees: `w_masken_falsch`.
  * `mit_maske_verweigert` (`m = true`): the same two steps of thread 1 set the core's mask
    (`maske_nichtleer_iff`), and the model REFUSES the handler's entry step. PLANTED DEFECT: the
    step the guard refuses is a step of plain machine G (`RufSchrittG`) and ends with the
    handler standing at the held lock, so the safety below rests on the guard and on nothing else.
  * `mit_maske_nach_freigabe`: after thread 1 leaves its section and releases the lock the mask
    is empty and the handler's entry is a guarded step: the guard delays, it does not block.
  * `mit_maske_sicher` (`m = true`): `KernHaltM` holds on EVERY guarded run -- `kernHaltM_aus`
    from the closure (`w_abg_wahr`) and the discipline (`w_masken_wahr`), the schedule derived
    from the guards, not assumed.
-/
module
public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaskeZeugeBasis
public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaske
public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaskeGleich
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz.KernMaskeFix
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

instance (m : Bool) : DecidableEq (wD m).Ax := inferInstanceAs (DecidableEq Empty)

/-- A step of thread 1 (not a handler) is a guarded step, and the handler stays unbegun. -/
theorem w_schritt1 (m : Bool) {Z : KernZ (wD m)} {M' : RufMaschineG (wD m)}
    (hnb : ¬ Z.begonnen 0) (hs : RufSchrittG (wP m) (wO m) 0 Z.m 1 M') :
    KernSchritt (wP m) (wO m) 0 wk (HandlerVon (wP m) (wM0 m)) Z 1 (Z.weiter wk 1 M') ∧
      ¬ (Z.weiter wk 1 M').begonnen 0 := by
  refine ⟨kernSchritt_weiter hs (fun h _ => ?_) (fun g hg hb _ _ => ?_), ?_⟩
  · exact absurd (w_handler m 1 h) (by decide)
  · have e := w_handler m g hg
    subst e
    exact absurd hb hnb
  · rintro (h | h)
    · exact absurd h (by decide)
    · exact hnb h

/-- The handler's first step: guarded as soon as its core is unmasked. -/
theorem w_schritt0 (m : Bool) {Z : KernZ (wD m)} {M' : RufMaschineG (wD m)}
    (hmask : Z.mask 0 = []) (hs : RufSchrittG (wP m) (wO m) 0 Z.m 0 M') :
    KernSchritt (wP m) (wO m) 0 wk (HandlerVon (wP m) (wM0 m)) Z 0 (Z.weiter wk 0 M') :=
  kernSchritt_weiter hs (fun _ _ => hmask) (fun g hg _ _ _ => w_handler m g hg)

/-- **THE SAME PROGRAM DEADLOCKS WHEN THE LOCK DOES NOT MASK.** The lock is not declared
    `masks irqs` (`wD false`), thread 1 (an ordinary thread) takes it, and the handler (thread 0)
    enters on the same core: the entry guard admits it (the core is unmasked). The handler stands
    at a lock its core's thread holds, waits for it, and the only thread that could release it is
    held back by run to completion: nothing can step. `KernHaltM` is false at the machine
    reached; `maskenB` refuses the program (`w_masken_falsch`). -/
theorem ohne_maske_verklemmt : ∃ (zs : Nat → KernZ (wD false)) (fs : Nat → Faden),
    KernLauf (wP false) (wO false) 0 wk (HandlerVon (wP false) (wM0 false)) (wZ0 false) zs fs 3 ∧
    AnSperre (zs 3).m 0 () ∧ () ∈ offen ((zs 3).m.faeden 1).spur ∧ WartetG (zs 3).m 0 ∧
    (∀ f, f ≠ 0 → ¬ ∃ Z', KernSchritt (wP false) (wO false) 0 wk
      (HandlerVon (wP false) (wM0 false)) (zs 3) f Z') ∧
    ¬ KernHaltM (wP false) (wO false) 0 (wM0 false) (zs 3).m := by
  obtain ⟨M1, M2, -, -, s1, s2, -, -, hh2, -, hf2, -⟩ := w_prefix false
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := wP false) (O := wO false) (passes := 0) (M := M2)
    (f := 0) (hf2 0 (by decide)) (wLocksS false WFn.h) (wRet false WFn.h) .nil rfl rfl
  have hn0 : ¬ (wZ0 false).begonnen 0 := fun h => h
  obtain ⟨st1, hn1⟩ := w_schritt1 false hn0 s1
  obtain ⟨st2, hn2⟩ := w_schritt1 false hn1 s2
  have hok2 : MaskeOk wk M2 (((wZ0 false).weiter wk 1 M1).weiter wk 1 M2).mask :=
    maskeOk_schritt s2 (maskeOk_schritt s1 (wStart false).2.1)
  have hm2 : (((wZ0 false).weiter wk 1 M1).weiter wk 1 M2).mask 0 = [] :=
    mask_leer_ohne (fun _ => rfl) hok2 0
  have st3 := w_schritt0 false (Z := ((wZ0 false).weiter wk 1 M1).weiter wk 1 M2) hm2 s3
  have hAn : AnSperre M3 0 () := by
    unfold AnSperre
    rw [hZ3.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil), .nil, .nil,
      .ende (wRet false WFn.h), rfl⟩
  have hRing : () ∈ offen (M3.faeden 1).spur := by
    rw [rufSchrittG_fremd s3 1 (by decide)]
    exact hh2
  let zs : Nat → KernZ (wD false) := fun k => match k with
    | 0 => wZ0 false
    | 1 => (wZ0 false).weiter wk 1 M1
    | 2 => ((wZ0 false).weiter wk 1 M1).weiter wk 1 M2
    | _ => (((wZ0 false).weiter wk 1 M1).weiter wk 1 M2).weiter wk 0 M3
  let fs : Nat → Faden := fun k => match k with
    | 0 => 1
    | 1 => 1
    | _ => 0
  have hlauf : KernLauf (wP false) (wO false) 0 wk (HandlerVon (wP false) (wM0 false))
      (wZ0 false) zs fs 3 := by
    refine ⟨rfl, fun k hk => ?_⟩
    match k, hk with
    | 0, _ => exact st1
    | 1, _ => exact st2
    | 2, _ => exact st3
  refine ⟨zs, fs, hlauf, hAn, hRing, ⟨⟨(), hAn⟩, fun L _ => ⟨1, by decide, ?_⟩⟩, ?_, ?_⟩
  · cases L
    exact hRing
  · rintro f hf ⟨Z', hs⟩
    have := hs.vollendung 0 (wH0 false) (Or.inl rfl) (anSperre_nicht_fertig hAn) rfl
    exact hf this.symm
  · intro hK
    exact hK wk (wZ0 false) zs fs 3 (wStart false) hlauf rfl 0 1 () (wH0 false) (by decide) rfl
      hAn hRing

/-- **WITH THE MASK THE HANDLER IS HELD BACK.** The lock is declared `masks irqs` (`wD true`).
    After thread 1 takes it the core's mask is set, and the handler's entry step is REFUSED by the
    model (`eintritt`). The planted defect is the step the guard refuses: plain machine G takes
    it (`RufSchrittG` holds) and the handler stands at the held lock, the deadlock above. -/
theorem mit_maske_verweigert : ∃ (zs : Nat → KernZ (wD true)) (fs : Nat → Faden),
    KernLauf (wP true) (wO true) 0 wk (HandlerVon (wP true) (wM0 true)) (wZ0 true) zs fs 2 ∧
    () ∈ offen ((zs 2).m.faeden 1).spur ∧ (zs 2).mask 0 ≠ [] ∧
    (¬ ∃ Z', KernSchritt (wP true) (wO true) 0 wk (HandlerVon (wP true) (wM0 true)) (zs 2) 0 Z') ∧
    (∃ M3, RufSchrittG (wP true) (wO true) 0 (zs 2).m 0 M3 ∧ AnSperre M3 0 ()) := by
  obtain ⟨M1, M2, -, -, s1, s2, -, -, hh2, -, hf2, -⟩ := w_prefix true
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := wP true) (O := wO true) (passes := 0) (M := M2)
    (f := 0) (hf2 0 (by decide)) (wLocksS true WFn.h) (wRet true WFn.h) .nil rfl rfl
  have hn0 : ¬ (wZ0 true).begonnen 0 := fun h => h
  obtain ⟨st1, hn1⟩ := w_schritt1 true hn0 s1
  obtain ⟨st2, hn2⟩ := w_schritt1 true hn1 s2
  have hok2 : MaskeOk wk M2 (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).mask :=
    maskeOk_schritt s2 (maskeOk_schritt s1 (wStart true).2.1)
  have hne : (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).mask 0 ≠ [] :=
    (maske_nichtleer_iff hok2 0).2 ⟨1, (), rfl, rfl, hh2⟩
  let zs : Nat → KernZ (wD true) := fun k => match k with
    | 0 => wZ0 true
    | 1 => (wZ0 true).weiter wk 1 M1
    | _ => ((wZ0 true).weiter wk 1 M1).weiter wk 1 M2
  let fs : Nat → Faden := fun _ => 1
  refine ⟨zs, fs, ⟨rfl, fun k hk => ?_⟩, hh2, hne, ?_, ⟨M3, s3, ?_⟩⟩
  · match k, hk with
    | 0, _ => exact st1
    | 1, _ => exact st2
  · rintro ⟨Z', hs⟩
    exact hne (hs.eintritt (wH0 true) hn2)
  · unfold AnSperre
    rw [hZ3.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil), .nil, .nil,
      .ende (wRet true WFn.h), rfl⟩

/-- **After the release the handler is admitted**: thread 1 leaves its section and releases the
    masking lock, the core's mask empties (the last release unmasks), and the handler's entry
    step is a guarded step. -/
theorem mit_maske_nach_freigabe : ∃ (zs : Nat → KernZ (wD true)) (fs : Nat → Faden),
    KernLauf (wP true) (wO true) 0 wk (HandlerVon (wP true) (wM0 true)) (wZ0 true) zs fs 4 ∧
    (zs 4).mask 0 = [] ∧
    ∃ Z5, KernSchritt (wP true) (wO true) 0 wk (HandlerVon (wP true) (wM0 true)) (zs 4) 0 Z5 := by
  obtain ⟨M1, M2, M3, M4, s1, s2, s3, s4, hh2, h4, hf2, hf4⟩ := w_prefix true
  obtain ⟨M5, s5, -⟩ := w_endeEntf (P := wP true) (O := wO true) (passes := 0) (M := M4)
    (f := 0) (hf4 0 (by decide)) (wLocksS true WFn.h) (wRet true WFn.h) .nil rfl rfl
  have hn0 : ¬ (wZ0 true).begonnen 0 := fun h => h
  obtain ⟨st1, hn1⟩ := w_schritt1 true hn0 s1
  obtain ⟨st2, hn2⟩ := w_schritt1 true hn1 s2
  obtain ⟨st3, hn3⟩ := w_schritt1 true hn2 s3
  obtain ⟨st4, hn4⟩ := w_schritt1 true hn3 s4
  have hok4 : MaskeOk wk M4
      (((((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).weiter wk 1 M3).weiter wk 1 M4).mask :=
    maskeOk_schritt s4 (maskeOk_schritt s3 (maskeOk_schritt s2
      (maskeOk_schritt s1 (wStart true).2.1)))
  have hm4 : (((((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).weiter wk 1 M3).weiter wk 1 M4).mask 0
      = [] := by
    by_cases hnil : (((((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).weiter wk 1 M3).weiter wk 1
      M4).mask 0 = []
    · exact hnil
    · obtain ⟨f, L, _, _, hL⟩ := (maske_nichtleer_iff hok4 0).1 hnil
      by_cases hf : f = 1
      · subst hf
        rw [h4] at hL
        exact absurd hL List.not_mem_nil
      · rw [hf4 f hf, wM0_offen] at hL
        exact absurd hL List.not_mem_nil
  let zs : Nat → KernZ (wD true) := fun k => match k with
    | 0 => wZ0 true
    | 1 => (wZ0 true).weiter wk 1 M1
    | 2 => ((wZ0 true).weiter wk 1 M1).weiter wk 1 M2
    | 3 => (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).weiter wk 1 M3
    | _ => ((((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).weiter wk 1 M3).weiter wk 1 M4
  let fs : Nat → Faden := fun _ => 1
  refine ⟨zs, fs, ⟨rfl, fun k hk => ?_⟩, hm4, _, w_schritt0 true hm4 s5⟩
  match k, hk with
  | 0, _ => exact st1
  | 1, _ => exact st2
  | 2, _ => exact st3
  | 3, _ => exact st4

/-- **THE SAFE VARIANT, FROM THE MODEL**: with the lock declared `masks irqs`, the handler never
    stands at a lock a thread of its core holds, on every guarded run. -/
theorem mit_maske_sicher (M : RufMaschineG (wD true)) :
    KernHaltM (wP true) (wO true) 0 (wM0 true) M :=
  kernHaltM_aus (wFs_voll true) ((abgAlleB_iff (wFs_voll true)).1 w_abg_wahr)
    ((maskenB_iff (wFs_voll true)).1 w_masken_wahr) (wSp true) (wInit true) M

/-- **Witness of the embedding** (`laufG_kernLauf`): a G run of the fixture with the handler set
    taken EMPTY (a unit with no `entry … via idt`) lifts to a guarded run that ends at the same
    machine, with the lock held. -/
theorem einbettung_zeuge : ∃ zs : Nat → KernZ (wD true),
    KernLauf (wP true) (wO true) 0 wk (fun _ => False) ⟨wM0 true, fun _ => [], fun _ => False⟩
      zs (fun _ => 1) 2 ∧ () ∈ offen ((zs 2).m.faeden 1).spur := by
  obtain ⟨M1, M2, -, -, s1, s2, -, -, hh2, -, -, -⟩ := w_prefix true
  let ms : Nat → RufMaschineG (wD true) := fun k => match k with
    | 0 => wM0 true
    | 1 => M1
    | _ => M2
  have hl : LaufG (wP true) (wO true) 0 (wM0 true) ms (fun _ => 1) 2 := by
    refine ⟨rfl, fun k hk => ?_⟩
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
  obtain ⟨zs, hz, hm⟩ := laufG_kernLauf (kern := wk) (H := fun _ => False)
    (fun _ h => h) hl (fun _ => [])
  refine ⟨zs, hz, ?_⟩
  rw [hm 2 (Nat.le_refl 2)]
  exact hh2

/-- **`KernHaltE` itself on the safe variant** (through `kernHaltE_iff_M`: the start holds no
    lock): the leg of `Ziel`, with `KernPlan` as the premise it still is in `Spec.lean`. -/
theorem mit_maske_sicher_E (M : RufMaschineG (wD true)) :
    KernHaltE (wP true) (wO true) 0 (wM0 true) M :=
  (kernHaltE_iff_M (fun t L hL => by
    rw [wM0_offen] at hL
    exact absurd hL List.not_mem_nil)).2 (mit_maske_sicher M)


end Gabbro.Grammatik.Zielsatz.KernMaskeFix

#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.w_prefix
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.ohne_maske_verklemmt
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.mit_maske_verweigert
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.mit_maske_nach_freigabe
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.mit_maske_sicher
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.w_masken_falsch
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.mit_maske_sicher_E
#print axioms Gabbro.Grammatik.Zielsatz.KernMaskeFix.einbettung_zeuge
