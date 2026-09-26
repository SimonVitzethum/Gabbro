/-
  File:      Grammatik/Zielsatz/MaskenZeuge.lean
  Subject:   The witnesses of the leg `keinKernHalt` of `Ziel` (fix lane F11, 2026-09-22; made
             contentful by Opus agent H, 2026-09-26, OFFEN O19): `beispiele/59`, and the
             refused `gift/460` shape on which the leg FAILS.

  The fixture is `Korpus59.lean`, the G program of
  `beispiele/59-eintritt-nimmt-maskierte-sperre.gab`: the `via idt` dispatch root
  `takt_verteiler` (the program's one handler, `kP.unterbricht`) takes `TAKT`, which is declared
  `masks irqs` (`kMaskiert .takt = true`), and the system-call root `ruf_verteiler` takes `RING`,
  which is not.

  * `masken_zeuge` -- ONE CORE, a real preemption. On the runtime's start (thread 0 runs
    `takt_verteiler`, thread 1 `ruf_verteiler`), both bound to core 0: thread 1 unfolds its
    body, TAKES `RING`, and then the handler (thread 0) steps -- it stands at `locks TAKT`
    while the thread it interrupted holds `RING`. The core schedule holds (`KernPlan` with the
    handler set the PROGRAM declares), and `korpus59_ziel`'s `keinKernHalt` -- discharged from
    (a) since Opus agent H -- gives: the lock the handler stands at is NOT held by the thread
    of its core. Nothing of the leg is supplied here but the run and its schedule.
  * `masken_disziplin_59` / `masken_disziplin_460` / `masken_59` -- the discipline Bool on the
    two roots, and the handler component of `Akzeptiert` on example 59.
  * `kernHaltE_verletzt` -- THE LEG IS CONTENTFUL. `kPv` is example 59 with the handler's body
    replaced by `locks RING { }`: a handler that takes a lock WITHOUT `masks irqs`, which an
    ordinary thread takes too (the shape of `beispiele/gift/460`, refused by the Rust `H102`).
    The checker Bool accepts the same bodies with no handler declared (`kPv_ohne_handler`), the
    handler component refuses the program (`handler_abgelehnt`), and on a run of the runtime's
    start that the core hardware admits -- thread 1 takes `RING`, the handler enters (admitted:
    `RING` masks nothing) and stands at `locks RING` -- `KernHaltE` is FALSE. So the leg is no
    theorem about every program: what carries it is (a).
-/
import Grammatik.Korpus59

namespace Gabbro.Grammatik

namespace K59

open Gabbro.Grammatik.Zielsatz

/-! ## 1. The discipline Bool on the two roots (`H102` and `gift/460`) -/

/-- **The masked root passes**: every lock of `takt_verteiler`'s call graph masks
    interrupts. -/
theorem masken_disziplin_59 : maskenDisziplinB kP kFs kTaktVert = true := by decide

/-- **The `gift/460` shape is refused**: `ruf_verteiler` takes `RING`, which is not declared
    `masks irqs`; as a handler root its graph would fail the discipline. -/
theorem masken_disziplin_460 : maskenDisziplinB kP kFs kRufVert = false := by decide

/-- **The handler component accepts example 59**: its one handler `takt_verteiler` meets the
    discipline (Opus agent H; before, the unit did not say which root is a handler). -/
theorem masken_59 : maskenB kP kFs = true := by decide

/-! ## 2. The run: a handler stands at its masked lock while its core's thread holds one -/

/-- The runtime's start of `beispiele/59`. -/
abbrev kM0 : RufMaschineG kD.mitRuhe :=
  RufStartG kP.mitRuhe (speicherR kSp) (initRuhe kE.starts)

/-- No thread of the start machine holds a lock (both roots hold none by signature). -/
theorem kM0_offen (g : Faden) : offen (kM0.faeden g).spur = [] := by
  match g with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The two entry dispatch roots on threads 0 and 1. -/
theorem kM0_wurzeln :
    (initRuhe kE.starts 0).1 = some kTaktVert ∧ (initRuhe kE.starts 1).1 = some kRufVert :=
  ⟨rfl, rfl⟩

abbrev kLocksTR := ruS (V := vertragVon kD kTaktVert) (l := false) kLocksT
abbrev kRetTR :=
  ruEnd (V := vertragVon kD kTaktVert) (l := false) (Γ := []) (Λ := [])
    (Endblock.ret (D := kD) .keine List.Perm.nil)
abbrev kLocksRR := ruS (V := vertragVon kD kRufVert) (l := false) kLocksR
abbrev kRetRR :=
  ruEnd (V := vertragVon kD kRufVert) (l := false) (Γ := []) (Λ := [])
    (Endblock.ret (D := kD) .keine List.Perm.nil)

/-! ## 3. The handler set the program declares -/

/-- Thread 0 (`takt_verteiler`) is a handler of the program. -/
theorem kM0_handler0 : HandlerVon kP.mitRuhe kM0 0 := rfl

/-- ... and no other thread is: thread 1 runs the system-call root, every other thread the
    idle root. -/
theorem kM0_handler (t : Faden) (h : HandlerVon kP.mitRuhe kM0 t) : t = 0 := by
  match t, h with
  | 0, _ => rfl
  | 1, h => exact Bool.noConfusion h
  | _ + 2, h => exact Bool.noConfusion h

/-! ## 4. The witness -/

/-- **THE WITNESS.** Threads 0 (`takt_verteiler`, the handler) and 1 (`ruf_verteiler`) run
    on ONE core. Thread 1 unfolds its body and takes `RING`; then the handler steps and
    stands at `locks TAKT`, the lock declared `masks irqs`. The schedule is a real
    preemption: the handler entered while the thread of its core was inside its critical
    section, and it is the only thread of that core that steps from then on. The leg
    `keinKernHalt` of `Ziel` -- from `gabbro_ziel` through `korpus59_ziel`, discharged from (a)
    -- says the lock the handler stands at is not one the interrupted thread holds. -/
theorem masken_zeuge : ∃ M1 M2 M3 : RufMaschineG kD.mitRuhe,
    Zielsatz.Laufzeit kE (speicherR kSp) (initRuhe kE.starts) ∧
    RufSchrittG kP.mitRuhe kO.mitRuhe 0 kM0 1 M1 ∧
    RufSchrittG kP.mitRuhe kO.mitRuhe 0 M1 1 M2 ∧
    RufSchrittG kP.mitRuhe kO.mitRuhe 0 M2 0 M3 ∧
    -- the interrupted thread is inside its critical section
    KLock.ring ∈ offen (M3.faeden 1).spur ∧
    -- the handler stands at its masked lock
    AnSperre M3 0 KLock.takt ∧ kD.mitRuhe.maskiert KLock.takt = true ∧
    -- and that lock is not one the thread of its core holds: no same-core deadlock
    KLock.takt ∉ offen (M3.faeden 1).spur := by
  -- thread 1 unfolds `locks RING { bearbeite(0); } return;`
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := kP.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := kM0) (f := 1) rfl kLocksRR kRetRR .nil rfl rfl
  have hfrei1 : RufFreiG M1 1 KLock.ring := by
    intro g hg
    rw [rufSchrittG_fremd s1 g hg, kM0_offen]
    exact List.not_mem_nil
  -- thread 1 takes RING: it is inside its critical section
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := kP.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := M1) (f := 1) hZ1.1 KLock.ring (fun _ h => absurd h List.not_mem_nil)
    (ruB (.cons kRufB .nil)) .nil (.ende kRetRR) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res kD.mitRuhe)) ↔ L ∈ offen (kM0.faeden 1).spur
      rw [kM0_offen]
      simp) hfrei1
  -- the handler preempts: thread 0 steps and stands at `locks TAKT`
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := kP.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := M2) (f := 0)
    ((rufSchrittG_fremd s2 0 (by decide)).trans (rufSchrittG_fremd s1 0 (by decide)))
    kLocksTR kRetTR .nil rfl rfl
  refine ⟨M1, M2, M3, laufzeit_initRuhe kE, s1, s2, s3, ?_, ?_, rfl, ?_⟩
  · -- RING is held by thread 1 at M3
    rw [rufSchrittG_fremd s3 1 (by decide), hZ2.1]
    show KLock.ring ∈ offen (Ereignis.nimmt KLock.ring _ :: (M1.weltVon 1).spur)
    exact List.mem_cons_self
  · -- the handler stands at its masked lock
    unfold AnSperre
    rw [hZ3.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil),
      ruB (.cons kRufZ .nil), .nil, .ende kRetTR, rfl⟩
  · -- and that lock is not held by the thread of its core
    have hAn : AnSperre M3 0 KLock.takt := by
      unfold AnSperre
      rw [hZ3.1]
      exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil),
        ruB (.cons kRufZ .nil), .nil, .ende kRetTR, rfl⟩
    have hr3 : RufErreichbarG kE.P.mitRuhe kO.mitRuhe 0 kM0 M3 :=
      .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3
    have hZiel := korpus59_ziel kO kO_hw 0 (speicherR kSp) (initRuhe kE.starts)
      (laufzeit_initRuhe kE) M3 hr3
    -- the run, by index
    let ms : Nat → RufMaschineG kD.mitRuhe :=
      fun k => if k = 0 then kM0 else if k = 1 then M1 else if k = 2 then M2 else M3
    let fs : Nat → Faden := fun k => if k < 2 then 1 else 0
    have hlauf : LaufG kE.P.mitRuhe kO.mitRuhe 0 kM0 ms fs 3 := by
      refine ⟨rfl, fun k hk => ?_⟩
      match k, hk with
      | 0, _ => exact s1
      | 1, _ => exact s2
      | 2, _ => exact s3
    -- what the other threads hold at the handler's entry
    have hoffen1 : ∀ L, L ∈ offen (M2.faeden 1).spur → L = KLock.ring := by
      intro L hL
      rw [hZ2.1] at hL
      have e1 : offen (M1.weltVon 1).spur = [] := by
        show offen (M1.faeden 1).spur = []
        rw [hZ1.1]
        show offen (kM0.weltVon 1).spur = []
        exact kM0_offen 1
      have hL' : L ∈ KLock.ring :: offen (M1.weltVon 1).spur := hL
      rw [e1] at hL'
      exact List.mem_singleton.mp hL'
    have hoffen2 : ∀ f, f ≠ 0 → f ≠ 1 → offen (M2.faeden f).spur = [] := by
      intro f h0 h1
      rw [rufSchrittG_fremd s2 f h1, rufSchrittG_fremd s1 f h1]
      exact kM0_offen f
    have hplan : Zielsatz.KernPlan (fun _ => 0) (HandlerVon kP.mitRuhe kM0) ms fs 3 := by
      constructor
      · intro i hi hH _ f L hne _ hL
        have hi2 : i = 2 := by
          by_cases h0 : i < 2
          · have e1 : fs i = 1 := by simp only [fs]; rw [if_pos h0]
            rw [e1] at hH
            exact absurd (kM0_handler 1 hH) (by decide)
          · omega
        subst hi2
        have hms : ms 2 = M2 := rfl
        rw [hms] at hL
        have hf0 : f ≠ 0 := by
          intro h
          exact hne (by rw [h]; rfl)
        by_cases hf1 : f = 1
        · subst hf1
          rw [hoffen1 L hL]
          rfl
        · rw [hoffen2 f hf0 hf1] at hL
          exact absurd hL List.not_mem_nil
      · intro g i j k hg hfi _ hik hkj hj3 _ _
        have hg0 := kM0_handler g hg
        subst hg0
        have hi2 : i = 2 := by
          by_cases h0 : i < 2
          · exact absurd hfi (by simp only [fs]; rw [if_pos h0]; exact fun h => by cases h)
          · omega
        subst hi2
        have hk2 : k = 2 := by omega
        subst hk2
        rfl
    exact hZiel.keinKernHalt (fun _ => 0) ms fs 3 hlauf rfl hplan 0 1 KLock.takt kM0_handler0
      (by decide) rfl hAn

/-! ## 5. The refused shape: the leg FAILS on it -/

/-- The handler's body of the variant: `locks RING { }` -- a lock that does NOT mask. -/
def kLocksTRing : Stmt kD (vertragVon kD kTaktVert) false [] [] [] :=
  .locks KLock.ring (fun _ h => nomatch h) .nil

def kRumpfTaktRing : Endblock kD (vertragVon kD kTaktVert) false [] [] :=
  .cons kLocksTRing (.ret .keine List.Perm.nil)

/-- **The `gift/460` shape**: example 59 whose handler `takt_verteiler` takes `RING` -- which
    `ruf_verteiler`, an ordinary thread, takes too, and which does not mask interrupts. -/
def kPv : Programm kD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .zaehle => kRumpfZaehle
    | .taktVert => kRumpfTaktRing
    | .bearbeite => kRumpfBearbeite
    | .rufVert => kRumpfRufVert
  unterbricht
    | .taktVert => true
    | _ => false

/-- The same bodies with no handler declared. -/
def kPv0 : Programm kD := { kPv with unterbricht := fun _ => false }

/-- **Without a declared handler the checker accepts these bodies**: every component but the
    handler one is the same Bool on `kPv0` and `kPv`, and all of them pass. -/
theorem kPv_ohne_handler :
    Akzeptiert kPv0 kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] = true := by decide

/-- **The handler component refuses it**: the handler's graph takes `RING`. -/
theorem handler_abgelehnt :
    maskenB kPv kFs = false ∧
      Akzeptiert kPv kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] = false := by
  decide

/-- The variant as a unit, and its runtime start. -/
def kEv : Zielsatz.Einheit kD :=
  ⟨kPv, kSI, axWahr kD, [⟨kTaktVert, .nil⟩, ⟨kRufVert, .nil⟩], kSp, []⟩

abbrev kMv0 : RufMaschineG kD.mitRuhe :=
  RufStartG kPv.mitRuhe (speicherR kSp) (initRuhe kEv.starts)

theorem kMv0_offen (g : Faden) : offen (kMv0.faeden g).spur = [] := by
  match g with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem kMv0_handler (t : Faden) (h : HandlerVon kPv.mitRuhe kMv0 t) : t = 0 := by
  match t, h with
  | 0, _ => rfl
  | 1, h => exact Bool.noConfusion h
  | _ + 2, h => exact Bool.noConfusion h

abbrev kLocksTRv := ruS (V := vertragVon kD kTaktVert) (l := false) kLocksTRing

/-- **THE LEG FAILS ON THE REFUSED SHAPE.** On the runtime's start of `kEv` (thread 0 the
    handler, thread 1 `ruf_verteiler`), one core: thread 1 unfolds its body and takes `RING`;
    the handler enters -- admitted by the core hardware, `RING` masks nothing -- and stands at
    `locks RING`, which the interrupted thread holds. That is the same-core deadlock, and
    `KernHaltE` is false at the machine reached. -/
theorem kernHaltE_verletzt : ∃ M3 : RufMaschineG kD.mitRuhe,
    Zielsatz.Laufzeit kEv (speicherR kSp) (initRuhe kEv.starts) ∧
    RufErreichbarG kPv.mitRuhe kO.mitRuhe 0 kMv0 M3 ∧
    ¬ KernHaltE kPv.mitRuhe kO.mitRuhe 0 kMv0 M3 := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := kPv.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := kMv0) (f := 1) rfl kLocksRR kRetRR .nil rfl rfl
  have hfrei1 : RufFreiG M1 1 KLock.ring := by
    intro g hg
    rw [rufSchrittG_fremd s1 g hg, kMv0_offen]
    exact List.not_mem_nil
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := kPv.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := M1) (f := 1) hZ1.1 KLock.ring (fun _ h => absurd h List.not_mem_nil)
    (ruB (.cons kRufB .nil)) .nil (.ende kRetRR) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res kD.mitRuhe)) ↔ L ∈ offen (kMv0.faeden 1).spur
      rw [kMv0_offen]
      simp) hfrei1
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := kPv.mitRuhe) (O := kO.mitRuhe) (passes := 0)
    (M := M2) (f := 0)
    ((rufSchrittG_fremd s2 0 (by decide)).trans (rufSchrittG_fremd s1 0 (by decide)))
    kLocksTRv kRetTR .nil rfl rfl
  refine ⟨M3, laufzeit_initRuhe kEv,
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3, fun hK => ?_⟩
  have hRing : KLock.ring ∈ offen (M3.faeden 1).spur := by
    rw [rufSchrittG_fremd s3 1 (by decide), hZ2.1]
    show KLock.ring ∈ offen (Ereignis.nimmt KLock.ring _ :: (M1.weltVon 1).spur)
    exact List.mem_cons_self
  have hAn : AnSperre M3 0 KLock.ring := by
    unfold AnSperre
    rw [hZ3.1]
    exact ⟨false, [], [], [], .nil, _, _, .nil, .ende kRetTR, rfl⟩
  let ms : Nat → RufMaschineG kD.mitRuhe :=
    fun k => if k = 0 then kMv0 else if k = 1 then M1 else if k = 2 then M2 else M3
  let fs : Nat → Faden := fun k => if k < 2 then 1 else 0
  have hlauf : LaufG kPv.mitRuhe kO.mitRuhe 0 kMv0 ms fs 3 := by
    refine ⟨rfl, fun k hk => ?_⟩
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | 2, _ => exact s3
  have hoffen1 : ∀ L, L ∈ offen (M2.faeden 1).spur → L = KLock.ring := by
    intro L hL
    rw [hZ2.1] at hL
    have e1 : offen (M1.weltVon 1).spur = [] := by
      show offen (M1.faeden 1).spur = []
      rw [hZ1.1]
      show offen (kMv0.weltVon 1).spur = []
      exact kMv0_offen 1
    have hL' : L ∈ KLock.ring :: offen (M1.weltVon 1).spur := hL
    rw [e1] at hL'
    exact List.mem_singleton.mp hL'
  have hoffen2 : ∀ f, f ≠ 0 → f ≠ 1 → offen (M2.faeden f).spur = [] := by
    intro f h0 h1
    rw [rufSchrittG_fremd s2 f h1, rufSchrittG_fremd s1 f h1]
    exact kMv0_offen f
  have hplan : Zielsatz.KernPlan (fun _ => 0) (HandlerVon kPv.mitRuhe kMv0) ms fs 3 := by
    constructor
    · intro i hi hH _ f L hne _ hL
      have hi2 : i = 2 := by
        by_cases h0 : i < 2
        · have e1 : fs i = 1 := by simp only [fs]; rw [if_pos h0]
          rw [e1] at hH
          exact absurd (kMv0_handler 1 hH) (by decide)
        · omega
      subst hi2
      have hms : ms 2 = M2 := rfl
      rw [hms] at hL
      have hf0 : f ≠ 0 := by
        intro h
        exact hne (by rw [h]; rfl)
      by_cases hf1 : f = 1
      · subst hf1
        rw [hoffen1 L hL]
        rfl
      · rw [hoffen2 f hf0 hf1] at hL
        exact absurd hL List.not_mem_nil
    · intro g i j k hg hfi _ hik hkj hj3 _ _
      have hg0 := kMv0_handler g hg
      subst hg0
      have hi2 : i = 2 := by
        by_cases h0 : i < 2
        · exact absurd hfi (by simp only [fs]; rw [if_pos h0]; exact fun h => by cases h)
        · omega
      subst hi2
      have hk2 : k = 2 := by omega
      subst hk2
      rfl
  exact hK (fun _ => 0) ms fs 3 hlauf rfl hplan 0 1 KLock.ring rfl (by decide) rfl hAn hRing

#print axioms K59.masken_disziplin_59
#print axioms K59.masken_disziplin_460
#print axioms K59.masken_59
#print axioms K59.kM0_handler
#print axioms K59.masken_zeuge
#print axioms K59.kPv_ohne_handler
#print axioms K59.handler_abgelehnt
#print axioms K59.kernHaltE_verletzt

end K59

end Gabbro.Grammatik
