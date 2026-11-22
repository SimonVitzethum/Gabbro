module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
public import Stage0.Senke.Bild.Mehr.Ort.Footprint
public import Mathlib.Logic.Relation

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Mach Runner.Beweis

/-- A real WAIT or WAKE completion retains the projected image memory,
    even if its issuer still has private pending stores. -/
theorem image_futex_reply [Kern] {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St}
    {thread : Nat} {address mode value : W} {reply : Ans} {resume : Ans → Res T}
    (host : ImageFutexAnswers) (recognized : mode = 128 ∨ mode = 129)
    (waiting : machine.ths[thread]? = some (some (.ask (.sys (futexReq address mode value)) resume)))
    (answered : imageTSO.ans machine.ms thread (.sys (futexReq address mode value)) reply memory)
    (footprint : Nat → W → Prop) (buffered : PrivateBuffers footprint machine.ms.1) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread (some (resume reply))⟩
    ProcessStep imageTSO actI machine [(thread, futexReq address mode value, reply)] after ∧
      reply.isSome = true ∧ memory.1.buf = machine.ms.1.buf ∧
      projectSCState footprint memory = projectSCState footprint machine.ms ∧
      GleichAuf (fun byte => ∀ thread, ¬ footprint thread byte) memory.1.m machine.ms.1.m := by
  intro after
  let request := futexReq address mode value
  have number : request.nr ≠ cloneReq.nr := by
    change (202 : W) ≠ cloneReq.nr
    decide
  have noClone : request ≠ cloneReq := fun equal => number (congrArg Req.nr equal)
  have valid : (Op.sys request).special = false := rfl
  have external := answered.2
  change (if request = cloneReq then _ else Kern.ans request (machine.ms.1.view thread) reply (memory.1.view thread) ∧
    memory.1.buf = machine.ms.1.buf) at external
  rw [if_neg noClone] at external
  obtain ⟨view, result⟩ := host.unchanged address mode value reply _ _ recognized external.1
  have same := projectSCState_issuerView thread buffered external.2 view
  refine ⟨.ask waiting rfl valid answered rfl, result, external.2, same, ?_⟩
  intro byte unowned
  have unassigned : ¬ ∃ thread, footprint thread byte := fun ⟨other, owner⟩ => unowned other owner
  have agrees : GleichAt (mergedView memory.1 footprint) (mergedView machine.ms.1 footprint) byte :=
    congrArg Subtype.val same ▸ GleichAt.refl _ _
  change GleichAt (viewAt memory.1 footprint byte) (viewAt machine.ms.1 footprint byte) byte at agrees
  simpa only [viewAt, dif_neg unassigned] using agrees

/-- The returned WAIT advances the same thread to its waiter decrement.
    If the lower 32-bit word matched, the abstract execution may block
    and immediately return spuriously. A mismatch returns in one step. -/
theorem image_ticket_wait_reply [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T} {thread : Fin N}
    {base ticket sampled : Nat} {before : Zustand N}
    (host : ImageFutexAnswers) (saved : before.pc thread = .futexW ticket sampled)
    (footprint : Nat → W → Prop) (buffers : PrivateBuffers footprint machine.ms.1)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 128 (BitVec.ofNat 64 sampled))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 128 (BitVec.ofNat 64 sampled))) reply memory) :
    let request := futexReq (BitVec.ofNat 64 (base + 8)) 128 (BitVec.ofNat 64 sampled)
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    ProcessStep imageTSO actI machine [(thread.val, request, reply)] after ∧ reply.isSome = true ∧
      projectSCState footprint memory = projectSCState footprint machine.ms ∧
      Relation.ReflTransGen (fun current next => Schritt current thread next)
        before (before.mit thread (.decL ticket sampled)) := by
  intro request after
  obtain ⟨process, returned, _, same, _⟩ := image_futex_reply host (.inl rfl) waiting answered footprint buffers
  refine ⟨process, returned, same, ?_⟩
  by_cases equal : before.w.serv % 4294967296 = sampled % 4294967296
  · let blocked := before.mit thread (.blockiert ticket sampled)
    have sleeping : Schritt before thread blocked := .schlaeft saved equal
    have resumed : Schritt blocked thread (before.mit thread (.decL ticket sampled)) := by
      have atWait : blocked.pc thread = .blockiert ticket sampled := upd_self _ _ _
      have canonical := Schritt.scheinbar atWait
      have overwritten : upd (upd before.pc thread (.blockiert ticket sampled)) thread (.decL ticket sampled) =
          upd before.pc thread (.decL ticket sampled) := by
        funext other
        by_cases equal : other = thread
        · subst other
          rw [upd_self, upd_self]
        · rw [upd_ne _ _ equal, upd_ne _ _ equal, upd_ne _ _ equal]
      simpa only [blocked, Zustand.mit, overwritten] using canonical
    exact (Relation.ReflTransGen.single sleeping).tail resumed
  · exact Relation.ReflTransGen.single (.kehrtZurueck saved equal)

/-- The emitted hosted WAKE-all completion represents one wake step.
    It preserves the committed lock words, the projected program memory
    and the cross-thread ticket invariant. -/
theorem image_ticket_wake_reply [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T} {thread : Fin N}
    {base : Nat} {before : Zustand N}
    (host : ImageFutexAnswers) (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .weck) (represented : TicketWordsAt machine.ms.1.m base before)
    (footprint : Nat → W → Prop) (buffers : PrivateBuffers footprint machine.ms.1)
    (shared : ∀ offset, offset = 0 ∨ offset = 8 ∨ offset = 16 →
      ∀ byte, fenster (BitVec.ofNat 64 (base + offset)) byte → ∀ owner, ¬ footprint owner byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 129 2147483647)) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.sys (futexReq (BitVec.ofNat 64 (base + 8)) 129 2147483647)) reply memory) :
    let request := futexReq (BitVec.ofNat 64 (base + 8)) 129 2147483647
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    let next : Zustand N := ⟨before.w, upd (wecke before.pc) thread .frei, before.q⟩
    ProcessStep imageTSO actI machine [(thread.val, request, reply)] after ∧ reply.isSome = true ∧
      projectSCState footprint memory = projectSCState footprint machine.ms ∧
      Schritt before thread next ∧ TicketWordsAt memory.1.m base next ∧ Inv N next := by
  intro request after next
  obtain ⟨process, returned, _, same, preserve⟩ :=
    image_futex_reply host (.inr rfl) waiting answered footprint buffers
  have wake : Schritt before thread next := .weckt saved
  have word (offset : Nat) (inLock : offset = 0 ∨ offset = 8 ∨ offset = 16) :
      memory.1.m.rd64 (BitVec.ofNat 64 (base + offset)) =
        machine.ms.1.m.rd64 (BitVec.ofNat 64 (base + offset)) :=
    gleich_rd64 fun byte touched => preserve byte (shared offset inLock byte touched)
  refine ⟨process, returned, same, wake, ⟨?_, ?_, ?_⟩, invariant.schritt limit wake⟩
  · have first := word 0 (.inl rfl)
    simpa only [Nat.add_zero] using first.trans represented.next
  · exact (word 8 (.inr (.inl rfl))).trans represented.serving
  · exact (word 16 (.inr (.inr rfl))).trans represented.waiters

end Gabbro.Stage0.Senke.Faeden
