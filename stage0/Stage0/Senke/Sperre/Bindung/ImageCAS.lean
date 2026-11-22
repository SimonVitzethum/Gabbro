module

public import Stage0.Senke.Images.Correctness
public import Stage0.Senke.Sperre.Bindung.Simulation
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Mem Runner.Mach Runner.Beweis

/-- The actual three committed words of one emitted ticket lock. The
    unbounded counters are observed exactly modulo the machine word. -/
structure TicketWordsAt (memory : Mem) (base : Nat) {N : Nat} (state : Zustand N) : Prop where
  next : memory.rd64 (BitVec.ofNat 64 base) = some (BitVec.ofNat 64 state.w.next)
  serving : memory.rd64 (BitVec.ofNat 64 (base + 8)) = some (BitVec.ofNat 64 state.w.serv)
  waiters : memory.rd64 (BitVec.ofNat 64 (base + 16)) = some (BitVec.ofNat 64 state.w.wait)

theorem _root_.Gabbro.Stage0.Emitted.loaded_ticketWords [Kern] {src : String} {reserve : Nat}
    {options : Profil.Options} (output : Emitted src reserve options) (N : Nat)
    {memory : Mem} (loaded : BytesAt memory Runner.Prog.IMG output.bytes)
    (lock : (declOf output.compiled.unit).Lock) :
    TicketWordsAt memory (output.image.Y.lk lock) (start N) ∧ Inv N (start N) := by
  obtain ⟨_, locks, sync, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  have layout := sync 0 (Nat.zero_le _)
  obtain ⟨low, high⟩ := layout.lay lock
  have bound := layout.sye
  refine ⟨⟨?_, ?_, ?_⟩, Inv.start⟩
  · exact (zero_word locks (by omega) (by omega) (by omega)).1
  · exact (zero_word locks (by omega) (by omega) (by omega)).1
  · exact (zero_word locks (by omega) (by omega) (by omega)).1

/-- The actual TSO response to the ticket draw executes exactly the
    matching ticket-machine step. Success appends the real issuing thread;
    a failed comparison retries with unchanged words. -/
theorem image_ticket_draw [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {base expected : Nat} {thread : Fin N} {before : Zustand N}
    (saved : before.pc thread = .casN expected) (isWord : expected < 2 ^ 64)
    (fits : base + 24 ≤ 2 ^ 64) (represented : TicketWordsAt machine.ms.1.m base before)
    (writable : all machine.ms.1.m.wr (BitVec.ofNat 64 base) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 base) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 base) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (BitVec.ofNat 64 before.w.next, 0) ∧
      memory.1.buf = machine.ms.1.buf ∧
      ∃ next, Schritt before thread next ∧ TicketWordsAt memory.1.m base next := by
  intro after
  let old := BitVec.ofNat 64 before.w.next
  let requested := BitVec.ofNat 64 expected
  let address := BitVec.ofNat 64 base
  let update := BitVec.ofNat 64 (expected + 1)
  have specification : machine.ms.1.m.cas address requested update =
      some (old, if old = requested then Mem.write machine.ms.1.m address 8 update.toNat else machine.ms.1.m) :=
    cas_spec represented.next writable
  obtain ⟨_, outcome⟩ := answered.1
  change (machine.ms.1.m.cas address requested update = none ∧ _) ∨
    (∃ oldWord newMemory, machine.ms.1.m.cas address requested update = some (oldWord, newMemory) ∧
      reply = some (oldWord, 0) ∧ memory.1 = { machine.ms.1 with m := newMemory }) at outcome
  rcases outcome with ⟨failure, _, _⟩ | ⟨oldWord, newMemory, actual, returned, memoryEq⟩
  · rw [specification] at failure
    cases failure
  · have exactPair := Option.some.inj (actual.symm.trans specification)
    have exactOld : oldWord = old := congrArg Prod.fst exactPair
    have exactMemory : newMemory =
        (if old = requested then Mem.write machine.ms.1.m address 8 update.toNat else machine.ms.1.m) :=
      congrArg Prod.snd exactPair
    refine ⟨.ask waiting rfl rfl answered rfl,
      returned.trans (congrArg (fun word => some (word, (0 : W))) exactOld), ?_, ?_⟩
    · exact congrArg TSt.buf memoryEq
    · have compare : old = requested ↔ before.w.next % 2 ^ 64 = expected := by
        constructor
        · intro equal
          have same := congrArg BitVec.toNat equal
          simpa only [old, requested, BitVec.toNat_ofNat, Nat.mod_eq_of_lt isWord] using same
        · intro equal
          apply BitVec.eq_of_toNat_eq
          simp only [old, requested, BitVec.toNat_ofNat, Nat.mod_eq_of_lt isWord, equal]
      by_cases same : old = requested
      · have got := compare.mp same
        let next : Zustand N := ⟨⟨before.w.next + 1, before.w.serv, before.w.wait⟩,
          upd before.pc thread (.ladeS before.w.next), before.q ++ [thread]⟩
        rw [if_pos same] at exactMemory
        refine ⟨next, .zieht saved got, ?_⟩
        rw [memoryEq, exactMemory]
        have readable : all machine.ms.1.m.rd address 8 = true := by
          have read := represented.next
          unfold Mem.rd64 at read
          split at read
          · assumption
          · cases read
        have exactUpdate : update = BitVec.ofNat 64 next.w.next := by
          change BitVec.ofNat 64 (expected + 1) = BitVec.ofNat 64 (before.w.next + 1)
          rw [BitVec.ofNat_add, BitVec.ofNat_add]
          exact congrArg (· + BitVec.ofNat 64 1) same.symm
        have separate (offset : Nat) (low : 8 ≤ offset) (high : offset ≤ 16) :
            Far address 8 (BitVec.ofNat 64 (base + offset)) 8 := by
          have a : base < 2 ^ 64 := by omega
          have b : base + offset < 2 ^ 64 := by omega
          simp only [Far, address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b]
          omega
        exact ⟨(rd64_write_same (w := update) readable).trans (congrArg some exactUpdate),
          (rd64_write_far (separate 8 (by decide) (by decide))).trans represented.serving,
          (rd64_write_far (separate 16 (by decide) (by decide))).trans represented.waiters⟩
      · rw [if_neg same] at exactMemory
        refine ⟨before.mit thread .ladeN, .verfehlt saved (fun equal => same (compare.mpr equal)), ?_⟩
        rw [memoryEq, exactMemory]
        exact represented

end Gabbro.Stage0.Senke.Faeden
