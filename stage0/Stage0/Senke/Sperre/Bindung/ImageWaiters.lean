module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Runner Runner.IR Runner.Mach Runner.Beweis Runner.Mem

/-- The two waiter-counter CAS loops share their physical representation
    and vary only in the saved position and updated word. -/
inductive WaitAdjustment where
  | register
  | unregister

def WaitAdjustment.expectedPlace (mode : WaitAdjustment) (ticket sampled expected : Nat) : Ort :=
  match mode with
  | .register => .incC ticket sampled expected
  | .unregister => .decC ticket sampled expected

def WaitAdjustment.retryPlace (mode : WaitAdjustment) (ticket sampled : Nat) : Ort :=
  match mode with
  | .register => .incL ticket sampled
  | .unregister => .decL ticket sampled

def WaitAdjustment.commitPlace (mode : WaitAdjustment) (ticket sampled : Nat) : Ort :=
  match mode with
  | .register => .futexW ticket sampled
  | .unregister => .ladeS ticket

def WaitAdjustment.count (mode : WaitAdjustment) (before : Nat) : Nat :=
  match mode with
  | .register => (before + 1) % 2 ^ 64
  | .unregister => wrapDec before

theorem WaitAdjustment.commit {N : Nat} {before : Zustand N} {thread : Fin N}
    {mode : WaitAdjustment} {ticket sampled expected : Nat}
    (saved : before.pc thread = mode.expectedPlace ticket sampled expected)
    (same : before.w.wait = expected) :
    Schritt before thread ⟨⟨before.w.next, before.w.serv, mode.count expected⟩,
      upd before.pc thread (mode.commitPlace ticket sampled), before.q⟩ := by
  cases mode
  · exact .erhoeht saved same
  · exact .senkt saved same

theorem WaitAdjustment.retry {N : Nat} {before : Zustand N} {thread : Fin N}
    {mode : WaitAdjustment} {ticket sampled expected : Nat}
    (saved : before.pc thread = mode.expectedPlace ticket sampled expected)
    (stale : before.w.wait ≠ expected) :
    Schritt before thread (before.mit thread (mode.retryPlace ticket sampled)) := by
  cases mode
  · exact .erhoehtNicht saved stale
  · exact .senktNicht saved stale

/-- The actual response to either hosted waiter-counter CAS is exactly
    the corresponding ticket step, including the retry on a stale read.
    The CAS leaves the other lock words and pending stores intact. -/
theorem image_ticket_waiter_CAS [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {base ticket sampled expected : Nat} {before : Zustand N}
    (mode : WaitAdjustment) (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = mode.expectedPlace ticket sampled expected)
    (isWord : expected < 2 ^ 64) (fits : base + 24 ≤ 2 ^ 64)
    (represented : TicketWordsAt machine.ms.1.m base before)
    (writable : all machine.ms.1.m.wr (BitVec.ofNat 64 (base + 16)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask (.cas
      (BitVec.ofNat 64 (base + 16)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (mode.count expected))) resume)))
    (answered : imageTSO.ans machine.ms thread.val (.cas (BitVec.ofNat 64 (base + 16))
      (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (mode.count expected))) reply memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (BitVec.ofNat 64 before.w.wait, 0) ∧
      memory.1.buf = machine.ms.1.buf ∧
      ∃ next, Schritt before thread next ∧ TicketWordsAt memory.1.m base next ∧ Inv N next := by
  intro after
  let address := BitVec.ofNat 64 (base + 16)
  let old := BitVec.ofNat 64 before.w.wait
  let requested := BitVec.ofNat 64 expected
  let update := BitVec.ofNat 64 (mode.count expected)
  obtain ⟨process, returned, memoryEq⟩ :=
    image_CAS_reply represented.waiters writable waiting answered
  have bufferEq := congrArg TSt.buf memoryEq
  refine ⟨process, returned, bufferEq, ?_⟩
  by_cases same : before.w.wait = expected
  · have matches : old = requested := congrArg (BitVec.ofNat 64) same
    rw [ite_eq_left matches] at memoryEq
    let next : Zustand N := ⟨⟨before.w.next, before.w.serv, mode.count expected⟩,
      upd before.pc thread (mode.commitPlace ticket sampled), before.q⟩
    have stepping : Schritt before thread next := WaitAdjustment.commit saved same
    refine ⟨next, stepping, ?_, invariant.schritt limit stepping⟩
    rw [memoryEq]
    have readable : all machine.ms.1.m.rd address 8 = true := by
      have read := represented.waiters
      unfold Mem.rd64 at read
      split at read
      · assumption
      · cases read
    have apart (offset : Nat) (within : offset ≤ 8) :
        Far address 8 (BitVec.ofNat 64 (base + offset)) 8 := by
      have first : base + 16 < 2 ^ 64 := by omega
      have second : base + offset < 2 ^ 64 := by omega
      simp only [Far, address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second]
      omega
    have first := rd64_write_far (apart 0 (Nat.zero_le 8))
    rw [Nat.add_zero] at first
    exact ⟨first.trans represented.next, (rd64_write_far (apart 8 (Nat.le_refl _))).trans represented.serving,
      rd64_write_same (w := update) readable⟩
  · have waitBound := List.countP_le_length (p := fun t => (before.pc t).gezaehlt) (l := before.q)
    have bounded : before.w.wait < 2 ^ 64 := by
      rw [invariant.wait]
      exact (waitBound.trans invariant.laenge).trans_lt (by omega)
    have different : old ≠ requested := by
      intro equal
      have naturals := congrArg BitVec.toNat equal
      exact same (by
        simpa only [old, requested, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt isWord]
          using naturals)
    rw [ite_eq_right different] at memoryEq
    let next := before.mit thread (mode.retryPlace ticket sampled)
    have stepping : Schritt before thread next := WaitAdjustment.retry saved same
    refine ⟨next, stepping, ?_, invariant.schritt limit stepping⟩
    rw [memoryEq]
    exact ⟨represented.next, represented.serving, represented.waiters⟩

end Gabbro.Stage0.Senke.Faeden
