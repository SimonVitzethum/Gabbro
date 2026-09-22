/-
  File:      Grammatik/Zielsatz/MaskenZeuge.lean
  Subject:   The witnesses of fix lane F11 (2026-09-22, OFFEN O19): the leg `keinKernHalt`
             of `Ziel` on `beispiele/59`, and the refusal of the `gift/460` shape.

  The fixture is `Korpus59.lean`, the G program of
  `beispiele/59-eintritt-nimmt-maskierte-sperre.gab`: the entry dispatch root
  `takt_verteiler` takes `TAKT`, which is declared `masks irqs` (`kMaskiert .takt = true`),
  and the second root `ruf_verteiler` takes `RING`, which is not.

  * `masken_zeuge` -- ONE CORE, a real preemption. On the runtime's start (thread 0 runs
    `takt_verteiler`, thread 1 `ruf_verteiler`), both bound to core 0: thread 1 unfolds its
    body, thread 1 TAKES `RING`, and then the handler (thread 0) steps -- it stands at
    `locks TAKT` while the thread it interrupted holds `RING`. Every hypothesis of the leg
    holds there (the call graph and its feature set, the masking discipline, the core
    schedule), and `korpus59_ziel`'s `keinKernHalt` gives: the lock the handler stands at is
    NOT held by the thread of its core. That is the deadlock `H102` refuses, excluded in the
    model.
  * `masken_disziplin_59` / `masken_disziplin_460` -- THE REFUSAL. The discipline Bool is
    `true` for the graph of `takt_verteiler` (its lock masks interrupts) and `false` for the
    graph of `ruf_verteiler` (`RING` does not). The second is the shape of
    `beispiele/gift/460-eintritt-nimmt-unmaskierte-sperre.gab`, which the Rust `H102`
    refuses: a handler taking a lock without `masks irqs`.
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
    `masks irqs`; as a handler root its graph fails the discipline. The one-word difference
    of gift 460 from example 59 (`kMaskiert`), now read by the model. -/
theorem masken_disziplin_460 : maskenDisziplinB kP kFs kRufVert = false := by decide

/-- Both roots pass the checker: the refusal above is the HANDLER discipline, not the
    checker's Bool (the unit does not say which root is a handler -- OFFEN O19). -/
theorem masken_disziplin_nicht_pruefer :
    Akzeptiert kP kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] = true :=
  kP_akzeptiert

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

/-! ## 3. The handler's call graph and its feature set -/

/-- The handler thread's call graph: `takt_verteiler` and the `zaehle` it calls. -/
def kZTb : kD.mitRuhe.Fn → Bool := fun g => decide (g = some kTaktVert ∨ g = some kZaehle)

def kZT : kD.mitRuhe.Fn → Prop := fun f => kZTb f = true

/-- Its feature set: exactly those callees, no indirect call, and the locks are the ones
    that mask interrupts -- the model side of `H102`. -/
def kAT : kD.mitRuhe.Fn → Merkmal kD.mitRuhe := fun _ =>
  ⟨kZTb, fun _ => false, fun L => kD.mitRuhe.maskiert L⟩

theorem kAT_abg : MerkAbg kP.mitRuhe kZT kAT := by
  intro f hf
  refine ⟨?_, fun g hg => ?_⟩
  · rcases of_decide_eq_true hf with rfl | rfl <;> decide
  · rcases hg with h | h
    · exact h
    · exact Bool.noConfusion h

theorem kAT_maskiert (f : kD.mitRuhe.Fn) (L : kD.mitRuhe.Lock) (_ : kZT f)
    (h : (kAT f).sperre L = true) : kD.mitRuhe.maskiert L = true := h

theorem kAT_start : MerkInvG kZT kAT (kM0.faeden 0) := by
  intro F hF
  rcases List.mem_cons.mp hF with h | h
  · subst h
    refine ⟨?_, ?_⟩
    · show kZTb (kM0.faeden 0).kopf.f = true
      decide
    · show mE (kAT (some kTaktVert)) (kP.mitRuhe.rumpf (some kTaktVert)) = true
      decide
  · exact absurd h List.not_mem_nil

/-! ## 4. The witness -/

/-- **THE WITNESS.** Threads 0 (`takt_verteiler`, the handler) and 1 (`ruf_verteiler`) run
    on ONE core. Thread 1 unfolds its body and takes `RING`; then the handler steps and
    stands at `locks TAKT`, the lock declared `masks irqs`. The schedule is a real
    preemption: the handler entered while the thread of its core was inside its critical
    section, and it is the only thread of that core that steps from then on. The leg
    `keinKernHalt` of `Ziel` -- from `gabbro_ziel` through `korpus59_ziel` -- says the lock
    the handler stands at is not one the interrupted thread holds. -/
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
    have hplan : Zielsatz.KernPlan (fun _ => 0) (fun t => t = 0) ms fs 3 := by
      constructor
      · intro i hi hH _ f L hne _ hL
        have hi2 : i = 2 := by
          by_cases h0 : i < 2
          · exact absurd hH (by simp only [fs]; rw [if_pos h0]; exact fun h => by cases h)
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
        subst hg
        have hi2 : i = 2 := by
          by_cases h0 : i < 2
          · exact absurd hfi (by simp only [fs]; rw [if_pos h0]; exact fun h => by cases h)
          · omega
        subst hi2
        have hk2 : k = 2 := by omega
        subst hk2
        rfl
    exact hZiel.keinKernHalt (fun _ => 0) (fun t => t = 0) (fun _ => kZT) (fun _ => kAT)
      (fun t _ => kAT_abg) (fun t ht => by subst ht; exact kAT_start)
      (fun t _ f L hz h => h) (fun t L => anSperre_start_falsch _ _ _ t L)
      ms fs 3 hlauf rfl hplan 0 1 KLock.takt rfl (by decide) rfl hAn

#print axioms K59.masken_disziplin_59
#print axioms K59.masken_disziplin_460
#print axioms K59.kAT_abg
#print axioms K59.kAT_start
#print axioms K59.masken_zeuge

end K59

end Gabbro.Grammatik
