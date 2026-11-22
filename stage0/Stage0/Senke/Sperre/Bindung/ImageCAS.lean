module

public import Stage0.Senke.Images.Correctness
public import Stage0.Senke.Sperre.Bindung.Simulation
import Stage0.Senke.Bild.Mehr.PrivatePath
import Stage0.Senke.Bild.Mehr.ImageTransition
import Stage0.Senke.Bild.Mehr.StartupOperands
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

/-- Once the actual image is at a CAS cell, the decoded operands
    determine the exact locked request. The seven silent steps retain
    the same memory and every other thread's control. -/
theorem image_cas_at [Kern] {before : Cfg imageTSO (Res T)} {thread : Nat} {pointer : T}
    {base : W} {code : List II} {index : Nat} {dest addressSlot expectedSlot : Int}
    (running : before.ths[thread]? = some (some (.next pointer)))
    (encoded : CodeAt (before.ms.1.view thread) base code)
    (location : pointer.pc = base + BitVec.ofNat 64 (16 * index))
    (cell : code[index]? = some (ci 22 dest addressSlot expectedSlot))
    {address expected update : W}
    (addressRead : (before.ms.1.view thread).rd64 (slot pointer.fp (sx (II.f addressSlot))) = some address)
    (expectedRead : (before.ms.1.view thread).rd64 (slot pointer.fp (sx (II.f expectedSlot))) = some expected)
    (updateRead : (before.ms.1.view thread).rd64 (slot pointer.fp (sx (II.f expectedSlot)) + 8) = some update) :
    let resume : Ans → Res T := fun reply => opt reply fun pair => ret1 pointer pair.1
    ProcessPrefix imageTSO actI before [] 7
      ⟨before.ms, before.ths.set thread (some (.ask (.cas address expected update) resume))⟩ := by
  obtain ⟨inside, opcode⟩ := List.getElem?_eq_some_iff.mp cell
  have instruction := encoded index inside
  rw [opcode, ← location] at instruction
  have run := tso_cas_prefix (before := imageToTSO before) running instruction addressRead expectedRead updateRead
  exact tso_silent_prefix_image run rfl

/-- A readable and writable CAS returns the actual committed word, even
    when the comparison fails. Both outcomes preserve every store buffer. -/
theorem image_CAS_reply [Kern] {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {address expected update old : W} {thread : Nat}
    (readable : machine.ms.1.m.rd64 address = some old)
    (writable : all machine.ms.1.m.wr address 8 = true)
    (waiting : machine.ths[thread]? = some (some (.ask (.cas address expected update) resume)))
    (answered : imageTSO.ans machine.ms thread (.cas address expected update) reply memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread (some (resume reply))⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (old, 0) ∧
      memory.1 = { machine.ms.1 with m :=
        if old = expected then Mem.write machine.ms.1.m address 8 update.toNat else machine.ms.1.m } := by
  intro after
  have specification := cas_spec (e := expected) (n := update) readable writable
  obtain ⟨_, outcome⟩ := answered.1
  change (machine.ms.1.m.cas address expected update = none ∧ _) ∨
    (∃ oldWord newMemory, machine.ms.1.m.cas address expected update = some (oldWord, newMemory) ∧
      reply = some (oldWord, 0) ∧ memory.1 = { machine.ms.1 with m := newMemory }) at outcome
  rcases outcome with ⟨failure, _, _⟩ | ⟨oldWord, newMemory, actual, returned, changed⟩
  · rw [specification] at failure
    cases failure
  · have exactPair := Option.some.inj (actual.symm.trans specification)
    have exactOld : oldWord = old := congrArg Prod.fst exactPair
    have exactMemory : newMemory =
        (if old = expected then Mem.write machine.ms.1.m address 8 update.toNat else machine.ms.1.m) :=
      congrArg Prod.snd exactPair
    exact ⟨.ask waiting rfl rfl answered rfl,
      returned.trans (congrArg (fun word => some (word, (0 : W))) exactOld),
      changed.trans (congrArg (fun bytes => { machine.ms.1 with m := bytes }) exactMemory)⟩

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
  obtain ⟨stepped, returned, memoryEq⟩ :=
    image_CAS_reply represented.next writable waiting answered
  have bufferEq := congrArg TSt.buf memoryEq
  refine ⟨stepped, returned, bufferEq, ?_⟩
  have compare : old = requested ↔ before.w.next % 2 ^ 64 = expected := by
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
    rw [if_pos same] at memoryEq
    refine ⟨next, .zieht saved got, ?_⟩
    rw [memoryEq]
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
  · rw [if_neg same] at memoryEq
    refine ⟨before.mit thread .ladeN, .verfehlt saved (fun equal => same (compare.mpr equal)), ?_⟩
    rw [memoryEq]
    exact ⟨represented.next, represented.serving, represented.waiters⟩

/-- The holder's actual serving-word CAS publishes the next ticket and
    relinquishes ownership. The invariant excludes a failed comparison
    even when the physical counter wraps. -/
theorem image_ticket_release [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {base expected ticket : Nat} {thread : Fin N} {before : Zustand N}
    (limit : N ≤ 2147483647) (invariant : Inv N before)
    (saved : before.pc thread = .gibC ticket expected)
    (fits : base + 24 ≤ 2 ^ 64) (represented : TicketWordsAt machine.ms.1.m base before)
    (writable : all machine.ms.1.m.wr (BitVec.ofNat 64 (base + 8)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 (base + 8)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 (base + 8)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    let next : Zustand N := ⟨⟨before.w.next, before.w.serv + 1, before.w.wait⟩,
      upd before.pc thread .gibW, before.q.tail⟩
    ProcessStep imageTSO actI machine [] after ∧ reply = some (BitVec.ofNat 64 expected, 0) ∧
      memory.1 = { machine.ms.1 with
        m := Mem.write machine.ms.1.m (BitVec.ofNat 64 (base + 8)) 8 (BitVec.ofNat 64 (expected + 1)).toNat } ∧
      Schritt before thread next ∧ TicketWordsAt memory.1.m base next ∧ Inv N next ∧
      (before.pc thread).haelt = true ∧ (next.pc thread).haelt = false := by
  intro after next
  let address := BitVec.ofNat 64 (base + 8)
  let update := BitVec.ofNat 64 (expected + 1)
  have loaded : expected = before.w.serv % 2 ^ 64 := invariant.ort_an saved
  have equal : BitVec.ofNat 64 before.w.serv = BitVec.ofNat 64 expected := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, loaded, Nat.mod_mod]
  obtain ⟨process, returned, memoryEq⟩ :=
    image_CAS_reply represented.serving writable waiting answered
  rw [ite_eq_left equal] at memoryEq
  have step : Schritt before thread next := .gibt saved loaded.symm
  refine ⟨process, ?_, memoryEq, step, ?_, invariant.schritt limit step, ?_, ?_⟩
  · rwa [equal] at returned
  · rw [memoryEq]
    have readable : all machine.ms.1.m.rd address 8 = true := by
      have read := represented.serving
      unfold Mem.rd64 at read
      split at read
      · assumption
      · cases read
    have exactUpdate : update = BitVec.ofNat 64 next.w.serv := by
      change BitVec.ofNat 64 (expected + 1) = BitVec.ofNat 64 (before.w.serv + 1)
      rw [BitVec.ofNat_add, BitVec.ofNat_add]
      exact congrArg (· + BitVec.ofNat 64 1) equal.symm
    have separate (offset : Nat) (available : offset ≤ 16) (other : offset = 0 ∨ offset = 16) :
        Far address 8 (BitVec.ofNat 64 (base + offset)) 8 := by
      have first : base + 8 < 2 ^ 64 := by omega
      have second : base + offset < 2 ^ 64 := by omega
      simp only [Far, address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second]
      omega
    exact ⟨(rd64_write_far (separate 0 (by decide) (.inl rfl))).trans represented.next,
      (rd64_write_same (w := update) readable).trans (congrArg some exactUpdate),
      (rd64_write_far (separate 16 (by decide) (.inr rfl))).trans represented.waiters⟩
  · rw [saved]
    rfl
  · change (upd before.pc thread .gibW thread).haelt = false
    rw [upd_self]
    rfl

/-- A real serving-word read admits the issuing ticket precisely when
    it matches modulo the machine word. The hosted binding registers an
    unmatched waiter, while spin retries without changing the lock state. -/
theorem image_ticket_serving_read [Kern] {N : Nat} {machine : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {base ticket : Nat} {thread : Fin N} {before : Zustand N}
    (strategy : LockWait) (spins : strategy = .spin → SpinState before)
    (saved : before.pc thread = .ladeS ticket)
    (represented : TicketWordsAt machine.ms.1.m base before)
    (footprint : Nat → W → Prop) (buffers : PrivateBuffers footprint machine.ms.1)
    (shared : ∀ byte, fenster (BitVec.ofNat 64 (base + 8)) byte → ∀ owner, ¬ footprint owner byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask (.rd 8 (BitVec.ofNat 64 (base + 8))) resume)))
    (answered : imageTSO.ans machine.ms thread.val (.rd 8 (BitVec.ofNat 64 (base + 8))) reply memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, machine.ths.set thread.val (some (resume reply))⟩
    ProcessStep imageTSO actI machine [] after ∧ memory = machine.ms ∧
      (∃ extra, reply = some (BitVec.ofNat 64 before.w.serv, extra)) ∧
      ∃ next, BindingStep strategy before thread next ∧ TicketWordsAt memory.1.m base next ∧
        ((next.pc thread).haelt = true ↔ before.w.serv % 2 ^ 64 = ticket % 2 ^ 64) ∧
        (before.w.serv % 2 ^ 64 = ticket % 2 ^ 64 → next = before.mit thread (.drin ticket)) := by
  intro after
  let address := BitVec.ofNat 64 (base + 8)
  have agreement : GleichAuf (fenster address) (machine.ms.1.view thread.val) machine.ms.1.m :=
    fun byte hit => view_agrees_at (fun store pending touched =>
      shared byte hit thread.val ((buffers thread.val store pending byte touched).1))
  obtain ⟨memorySame, extra, result⟩ := answered.1
  have observed : reply = some (BitVec.ofNat 64 before.w.serv, extra) := by
    change reply = ((machine.ms.1.view thread.val).rd64 address).map (·, extra) at result
    rw [gleich_rd64 agreement, represented.serving] at result
    exact result
  refine ⟨.ask waiting rfl rfl answered rfl, memorySame, ⟨extra, observed⟩, ?_⟩
  by_cases admitted : before.w.serv % 2 ^ 64 = ticket % 2 ^ 64
  · let next := before.mit thread (.drin ticket)
    have stepped : Schritt before thread next := .tritt saved admitted
    have adopted : BindingStep strategy before thread next := by
      cases strategy
      · exact stepped
      · refine .inl ⟨stepped, spins rfl, ?_⟩
        intro other
        by_cases same : other = thread
        · subst other
          change (upd before.pc thread (.drin ticket) thread).spin
          rw [upd_self]
          trivial
        · change (upd before.pc thread (.drin ticket) other).spin
          rw [upd_ne _ _ same]
          exact spins rfl other
    refine ⟨next, adopted, ?_, ?_, fun _ => rfl⟩
    · rw [memorySame]
      exact ⟨represented.next, represented.serving, represented.waiters⟩
    · change (upd before.pc thread (.drin ticket) thread).haelt = true ↔ _
      rw [upd_self]
      exact ⟨fun _ => admitted, fun _ => rfl⟩
  · cases strategy
    · let next := before.mit thread (.incL ticket before.w.serv)
      refine ⟨next, .wartet saved admitted, ?_, ?_, fun equal => (admitted equal).elim⟩
      · rw [memorySame]
        exact ⟨represented.next, represented.serving, represented.waiters⟩
      · change (upd before.pc thread (.incL ticket before.w.serv) thread).haelt = true ↔ _
        rw [upd_self]
        constructor
        · intro impossible
          cases impossible
        · exact fun equal => (admitted equal).elim
    · refine ⟨before, .inr ⟨ticket, saved, admitted, rfl⟩, memorySame.symm ▸ represented, ?_,
        fun equal => (admitted equal).elim⟩
      rw [saved]
      constructor
      · intro impossible
        cases impossible
      · exact fun equal => (admitted equal).elim

end Gabbro.Stage0.Senke.Faeden
