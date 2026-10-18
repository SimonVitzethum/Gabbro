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
import Grammatik.Zielsatz.Eigenschaften.KernMaske
import Grammatik.Zielsatz.Eigenschaften.KernMaskeGleich
import Grammatik.Zielsatz.Kern.Akzeptiert
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2
namespace Gabbro.Grammatik.Zielsatz.KernMaskeFix
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

inductive WFn where
  | h
  | t
  deriving DecidableEq

def wSig : Signatur Empty Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def wD (m : Bool) : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun t _ => nomatch t
  erlaubt := fun t _ _ _ => nomatch t
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun t => nomatch t
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => m
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun t => nomatch t
  gbraucht := fun e => nomatch e
  eigner := fun t => nomatch t
  Fn := WFn
  sig := fun _ => 0
  sigNr := fun _ => wSig
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance (m : Bool) : DecidableEq (wD m).Fn := inferInstanceAs (DecidableEq WFn)

def wRumpf (m : Bool) (f : WFn) : Endblock (wD m) (vertragVon (wD m) f) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) .nil) (.ret .empty List.Perm.nil)

def wP (m : Bool) : Programm (wD m) where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => wRumpf m f
  unterbricht
    | .h => true
    | .t => false

def wFs (m : Bool) : List (wD m).Fn := [WFn.h, WFn.t]

theorem wFs_voll (m : Bool) : ∀ g : (wD m).Fn, g ∈ wFs m := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem w_masken_wahr : maskenB (wP true) (wFs true) = true := by decide
theorem w_masken_falsch : maskenB (wP false) (wFs false) = false := by decide
theorem w_abg_wahr : abgAlleB (wP true) (wFs true) = true := by decide


def wLocksS (m : Bool) (f : WFn) : Stmt (wD m) (vertragVon (wD m) f) false [] [] [] :=
  .locks () (fun _ h => nomatch h) .nil

def wRet (m : Bool) (f : WFn) : Endblock (wD m) (vertragVon (wD m) f) false [] [] :=
  .ret .empty List.Perm.nil

def wO (m : Bool) : Orakel (wD m) where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

def wInit (m : Bool) : Faden → Σ f : (wD m).Fn, Env (wD m) ((wD m).params f)
  | 0 => ⟨WFn.h, .nil⟩
  | _ + 1 => ⟨WFn.t, .nil⟩

def wSp (m : Bool) : Speicher (wD m) := ⟨fun t _ _ => (nomatch t), fun g => nomatch g⟩

abbrev wM0 (m : Bool) : RufMaschineG (wD m) := RufStartG (wP m) (wSp m) (wInit m)

theorem wM0_offen (m : Bool) (f : Faden) : offen ((wM0 m).faeden f).spur = [] := by
  match f with
  | 0 => rfl
  | _ + 1 => rfl

theorem wH0 (m : Bool) : HandlerVon (wP m) (wM0 m) 0 := rfl

theorem w_handler (m : Bool) (t : Faden) (h : HandlerVon (wP m) (wM0 m) t) : t = 0 := by
  match t, h with
  | 0, _ => rfl
  | _ + 1, h => exact Bool.noConfusion h

def wZ0 (m : Bool) : KernZ (wD m) := ⟨wM0 m, fun _ => [], fun _ => False⟩

theorem wStart (m : Bool) : KernStart (fun _ => 0) (wM0 m) (wZ0 m) :=
  ⟨rfl, fun c f L => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, _, hL⟩ => by
    rw [wM0_offen] at hL
    exact absurd hL List.not_mem_nil⟩, fun _ h => h⟩


abbrev wk : Faden → Nat := fun _ => 0

/-- **The runs of the fixture, common prefix**: thread 1 (`t`) unfolds its body, takes the lock,
    leaves the empty section (`dannLeer`) and releases it (`freiGib`); no other thread moves. -/
theorem w_prefix (m : Bool) : ∃ M1 M2 M3 M4 : RufMaschineG (wD m),
    RufSchrittG (wP m) (wO m) 0 (wM0 m) 1 M1 ∧ RufSchrittG (wP m) (wO m) 0 M1 1 M2 ∧
    RufSchrittG (wP m) (wO m) 0 M2 1 M3 ∧ RufSchrittG (wP m) (wO m) 0 M3 1 M4 ∧
    () ∈ offen (M2.faeden 1).spur ∧ offen (M4.faeden 1).spur = [] ∧
    (∀ f, f ≠ 1 → M2.faeden f = (wM0 m).faeden f) ∧
    (∀ f, f ≠ 1 → M4.faeden f = (wM0 m).faeden f) := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := wP m) (O := wO m) (passes := 0) (M := wM0 m)
    (f := 1) rfl (wLocksS m WFn.t) (wRet m WFn.t) .nil rfl rfl
  have e1 : offen (M1.faeden 1).spur = [] := by
    rw [hZ1.1]
    exact wM0_offen m 1
  have hfrei : RufFreiG M1 1 () := by
    intro g hg
    rw [rufSchrittG_fremd s1 g hg, wM0_offen]
    exact List.not_mem_nil
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := wP m) (O := wO m) (passes := 0) (M := M1) (f := 1)
    hZ1.1 () (fun _ h => absurd h List.not_mem_nil) .nil .nil (.ende (wRet m WFn.t)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res (wD m))) ↔ L ∈ offen ((wM0 m).faeden 1).spur
      rw [wM0_offen]
      simp) hfrei
  obtain ⟨M3, s3, hZ3⟩ := w_dannLeer (P := wP m) (O := wO m) (passes := 0) (M := M2) (f := 1)
    hZ2.1 (.frei () (.dann .nil (.ende (wRet m WFn.t)))) .nil rfl
  obtain ⟨M4, s4, hZ4⟩ := w_freiGib (P := wP m) (O := wO m) (passes := 0) (M := M3) (f := 1)
    hZ3.1 () (.dann .nil (.ende (wRet m WFn.t))) .nil rfl
  have hn2 : (M2.faeden 1).spur = Ereignis.nimmt () (offen (M1.weltVon 1).spur) ::
      (M1.weltVon 1).spur := by
    rw [hZ2.1]
    rfl
  have hn3 : (M3.faeden 1).spur = (M2.faeden 1).spur := by
    rw [hZ3.1]
    rfl
  have hn4 : (M4.faeden 1).spur = Ereignis.gibt () :: (M3.faeden 1).spur := by
    rw [hZ4.1]
    rfl
  refine ⟨M1, M2, M3, M4, s1, s2, s3, s4, ?_, ?_, ?_, ?_⟩
  · rw [hn2]
    exact List.mem_cons_self
  · rw [hn4, hn3, hn2]
    have e1' : offen (M1.weltVon 1).spur = [] := e1
    simp [offen, e1']
    first | rfl | decide
  · intro f hf
    rw [rufSchrittG_fremd s2 f hf, rufSchrittG_fremd s1 f hf]
  · intro f hf
    rw [rufSchrittG_fremd s4 f hf, rufSchrittG_fremd s3 f hf, rufSchrittG_fremd s2 f hf,
      rufSchrittG_fremd s1 f hf]


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
