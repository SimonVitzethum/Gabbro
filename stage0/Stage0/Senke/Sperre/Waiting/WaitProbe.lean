/- Real encoded-memory witnesses. The test kernel explicitly models a foreign
   holder releasing while WAIT is pending; it is not a fairness assumption. -/
module
public import Stage0.Senke.Sperre.Retry
public import Stage0.Senke.Sperre.Waiting.Wake
public import Stage0.Senke.Sperre.ContendedProbe
@[expose] public section


namespace Gabbro.Stage0.Senke.WaitProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
open ContendedProbe (layout)
set_option maxRecDepth 100000

/-- A concrete allowed schedule at WAIT: the foreign holder completes release.
    WAKE returns zero. The rest of memory is unchanged by either call. -/
abbrev releaseKernel : Kern where
  ans q m answer mr := answer = some (0, 0) ∧
    ((q = futexReq 8192 128 2 ∧ mr = write (write m 8192 8 0) 8200 8 0) ∨
     (q = futexReq 8192 129 1 ∧ mr = m))

local instance : Kern := releaseKernel
local instance : FutexOK (fun _ _ _ _ => True) where
  wait_return := by intro a v m r x mr _; exact Or.inr trivial
  wake_return := by
    intro a n m r x mr h _
    obtain ⟨he, _⟩ := h
    cases he
    exact Nat.zero_le _

/-- The full contended acquisition on real instruction/frame/lock bytes:
    foreign owner 2/count 3, five pre-existing waiters; this thread registers,
    WAIT returns after explicit release, it unregisters and retry acquires.
    The waiter count returns to five; frame word 77 remains protected. -/
theorem nimm_wait_acquired_zeuge :
    @FutexOK (fun _ _ _ _ => True) releaseKernel ∧
    ∃ m' f', Star ⟨0, 4096⟩ ContendedProbe.memory ⟨768, 4096⟩ m' ∧
      LS ContendedProbe.memory m' 4096 4 8192 f' 1 1 5 ∧
      LockInv 1 1 5 ∧ m'.rd64 (slot 4096 3) = some 77 := by
  have E := ContendedProbe.environment
  have me : MeOK layout 4096 := ⟨by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨f0, initial⟩ := ls_init E (o := 2) (c := 3) (w := 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨m1, f1, s1, h1, id1, seen1, _⟩ := nimm_contended E initial
    (At.whole ContendedProbe.code) me (by decide) (by decide)
  obtain ⟨mw, fw, sw, hw, invw, args, idw, seenw, _⟩ := nimm_wait_entry E h1
    (At.whole ContendedProbe.code) (by unfold LockInv; decide +kernel) (by decide)
  let mr := write (write mw 8192 8 0) 8200 8 0
  have resume : LS ContendedProbe.memory mr 4096 4 8192 fw 0 0 (5 + 1) :=
    (hw.owner E 0).count E 0
  have args' : FutexArgs fw 8192 128 2 := by simpa [seen1] using args
  have answer : Kern.ans (futexReq 8192 128 2) mw (some (0, 0)) mr :=
    ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨_, m2, f2, s2, h2, inv2, id2⟩ := nimm_wait_retry (spurious := fun _ _ _ _ => True) E hw (At.whole ContendedProbe.code)
    args' answer resume (by unfold LockInv; decide +kernel) (by decide)
  have state2 : LS ContendedProbe.memory m2 4096 4 8192 f2 0 0 5 := h2
  have id : f2 0 = meW layout 4096 := id2.trans (idw.trans id1)
  obtain ⟨m3, f3, s3, h3, inv3⟩ := nimm_retry_acquired E state2 (At.whole ContendedProbe.code)
    id (s1.trans (sw.trans s2)) (by decide) me
  refine ⟨inferInstance, m3, f3, s3, h3, inv3, ?_⟩
  exact (h3.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

/-- An unchanged/spurious WAIT completes a full retry cycle and returns to
    the WAIT branch: no accidental acquisition and no leaked waiter entry. -/
theorem nimm_wait_spurious_zeuge :
    letI : Kern := futexKernel
    ∃ mw fw m' f', Star ⟨0, 4096⟩ ContendedProbe.memory ⟨576, 4096⟩ mw ∧
      StopAt ⟨576, 4096⟩ mw (futexReq 8192 128 2) ∧
      Star ⟨576, 4096⟩ mw ⟨352, 4096⟩ m' ∧
      LS ContendedProbe.memory m' 4096 4 8192 f' 2 3 5 ∧
      FutexArgs fw 8192 128 2 ∧ LockInv 2 3 5 := by
  letI : Kern := futexKernel
  letI : FutexOK (fun _ _ _ _ => True) := futexOK_zeuge
  have E := ContendedProbe.environment
  have me : MeOK layout 4096 := ⟨by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨f0, initial⟩ := ls_init E (o := 2) (c := 3) (w := 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨m1, f1, s1, h1, id1, seen1, _⟩ := nimm_contended E initial
    (At.whole ContendedProbe.code) me (by decide) (by decide)
  obtain ⟨mw, fw, sw, hw, invw, args, idw, _, entry⟩ := nimm_wait_entry E h1
    (At.whole ContendedProbe.code) (by unfold LockInv; decide +kernel) (by decide)
  have args' : FutexArgs fw 8192 128 2 := by simpa [seen1] using args
  have answer : Kern.ans (futexReq 8192 128 2) mw (some (0, 0)) mw :=
    ⟨rfl, 8192, 2, Or.inl rfl, rfl⟩
  obtain ⟨_, m2, f2, s2, h2, _, id2⟩ := nimm_wait_retry (spurious := fun _ _ _ _ => True) E hw (At.whole ContendedProbe.code)
    args' answer hw invw (by decide)
  have state2 : LS ContendedProbe.memory m2 4096 4 8192 f2 2 3 5 := h2
  obtain ⟨m3, f3, s3, h3, _⟩ := nimm_retry E state2 (At.whole ContendedProbe.code)
    (id2.trans (idw.trans id1))
  exact ⟨mw, fw, m3, f3, s1.trans sw, by simpa [seen1] using entry,
    s2.trans s3, h3.1, args', by unfold LockInv; decide +kernel⟩

def wakeCode : List II := gibC layout 8192 4

def wakeMemory : Mem where
  b a := if a.toNat = 4120 then 77
    else if a.toNat = 8192 then 1
    else if a.toNat = 8200 then 1
    else if a.toNat = 8208 then 5
    else ((wakeCode.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

/-- The generalized SyncOK is inhabited with real memory, nonzero waiters,
    a held lock and a callee frame in the same thread's stack. -/
theorem sync_waiters_zeuge :
    SyncOK wakeMemory layout 4096 22 (fun _ => 5) ∧
    SyncOK wakeMemory layout (slot 4096 4) 18 (fun _ => 5) := by
  have h : SyncOK wakeMemory layout 4096 22 (fun _ => 5) := by
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      ?_, by decide, ?_, fun _ _ _ => rfl, ?_⟩
    · intro lk; simp only [layout]; exact ⟨by decide, by decide⟩
    · intro lk lk' ne
      apply False.elim (ne ?_)
      apply Fin.ext
      have h1 := lk.isLt
      have h2 := lk'.isLt
      change lk.val < 1 at h1
      change lk'.val < 1 at h2
      omega
    · intro lk
      exact ⟨1, 1, by change wakeMemory.rd64 8192 = some 1; decide +kernel,
        by change wakeMemory.rd64 8200 = some 1; decide +kernel,
        by change wakeMemory.rd64 8208 = some 5; decide +kernel,
        Or.inr ⟨rfl, by decide, by decide⟩⟩
  exact ⟨h, h.call (by decide)⟩

theorem wakeEnvironment : LE wakeMemory 0 4096 4 8192 wakeCode := by
  refine ⟨⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    by decide, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · apply codeAt_bytes wakeCode 0 (by decide +kernel)
    intro i hi
    have length : (wakeCode.flatMap encII).length = 464 := by decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [wakeMemory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      ite_eq_right (show i ≠ 4120 by omega),
      ite_eq_right (show i ≠ 8192 by omega),
      ite_eq_right (show i ≠ 8200 by omega),
      ite_eq_right (show i ≠ 8208 by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar; decide +kernel

/-- Last release in real encoded memory with five waiters executes WAKE-one,
    returns to the end of gibC, keeps all five waiter entries and frame word 77. -/
theorem gib_waiters_zeuge :
    ∃ mw fw m' f', Star ⟨0, 4096⟩ wakeMemory ⟨448, 4096⟩ mw ∧
      StopAt ⟨448, 4096⟩ mw (futexReq 8192 129 1) ∧
      Star ⟨448, 4096⟩ mw ⟨464, 4096⟩ m' ∧
      LS wakeMemory m' 4096 4 8192 f' 0 0 5 ∧ LockInv 0 0 5 ∧
      FutexArgs fw 8192 129 1 ∧ m'.rd64 (slot 4096 3) = some 77 := by
  have E := wakeEnvironment
  have me : MeOK layout 4096 := ⟨by decide, by decide, by decide, by decide, by decide⟩
  obtain ⟨f0, initial⟩ := ls_init E (o := meW layout 4096) (c := 1) (w := 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨mw, fw, sw, hw, _, args, entry⟩ := gib_waiters_entry E initial
    (At.whole wakeCode) me (by decide) (by decide) (by decide)
  have answer : Kern.ans (futexReq 8192 129 1) mw (some (0, 0)) mw :=
    ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨_, m', f', steps, state, inv⟩ := gib_waiters_return (spurious := fun _ _ _ _ => True) E hw (At.whole wakeCode)
    args answer hw (by decide)
  refine ⟨mw, fw, m', f', sw, entry, steps, state, inv, args, ?_⟩
  exact (state.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

end Gabbro.Stage0.Senke.WaitProbe
