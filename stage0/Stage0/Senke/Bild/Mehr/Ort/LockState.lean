module

public import Stage0.Senke.Bild.Mehr.Ort.LockOwnership
public import Stage0.Senke.Sperre.Bindung.ImageWaiters
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR Runner.Beweis Runner.Mem Runner.Mach

/-- The three consecutive machine words reserved for one declared lock. -/
def LockBytes {D : Deklaration} (layout : Lay D) (lock : D.Lock) (byte : W) : Prop :=
  layout.lk lock ≤ byte.toNat ∧ byte.toNat < layout.lk lock + 24

theorem lockWord_in_bytes {D : Deklaration} {layout : Lay D} {lock : D.Lock} {offset : Nat}
    (fits : layout.lk lock + 24 ≤ 2 ^ 64) (inside : offset ≤ 16) {byte : W}
    (touched : fenster (BitVec.ofNat 64 (layout.lk lock + offset)) byte) :
    LockBytes layout lock byte := by
  let base := layout.lk lock + offset
  let word := BitVec.ofNat 64 base
  have baseBound : base < 2 ^ 64 := by dsimp only [base]; omega
  have address : word.toNat = base := by
    change (BitVec.ofNat 64 base).toNat = base
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseBound]
  change (byte - word).toNat < 8 at touched
  have noWrap : (byte - word).toNat + word.toNat < 2 ^ 64 := by
    rw [address]
    dsimp only [base]
    omega
  have byteAddress := congrArg BitVec.toNat (BitVec.sub_add_cancel byte word)
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt noWrap, address] at byteAddress
  unfold LockBytes
  dsimp only [base] at byteAddress
  omega

theorem lockBytes_disjoint {D : Deklaration} {layout : Lay D} (separate : LaySync layout)
    {lock other : D.Lock} (different : other ≠ lock) {byte : W} (hit : LockBytes layout other byte) :
    ¬ LockBytes layout lock byte := by
  intro overlaps
  obtain ⟨a, b⟩ := hit
  obtain ⟨c, d⟩ := overlaps
  rcases separate.2 other lock different with left | right <;> omega

/-- All physical ticket locks of the image carry the corresponding
    source owner and the queue invariant in the same machine state. -/
structure ImageTicketStates {D : Deklaration} {N : Nat} (layout : Lay D)
    (memory : Mem) (source : RufMaschineG D) (states : D.Lock → Zustand N) : Prop where
  words : ∀ lock, TicketWordsAt memory (layout.lk lock) (states lock)
  protocol : ∀ lock, Inv N (states lock)
  owners : ∀ lock, TicketOwnership source lock (states lock)

/-- Loader bytes and one source checker verdict initialize the complete
    lock collection, including dormant and idle threads. -/
theorem _root_.Gabbro.Stage0.Emitted.loaded_ticketStates [Kern]
    {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) {E : Einheit (declOf output.compiled.unit)}
    {memory : Mem} (loaded : BytesAt memory Runner.Prog.IMG output.bytes)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true) :
    ImageTicketStates output.image.Y.withIdle memory (imageSourceStart E).m
      (fun _ => start (output.starts.length + 1)) := by
  exact ⟨fun lock => (output.loaded_ticketOwnership loaded accepted lock).1,
    fun lock => (output.loaded_ticketOwnership loaded accepted lock).2.1,
    fun lock => (output.loaded_ticketOwnership loaded accepted lock).2.2⟩

/-- A transition at one lock preserves the entire collection. Machine
    memory outside its reservation and source ownership of other locks
    are transported independently. -/
theorem ImageTicketStates.update {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {memory nextMemory : Mem} {source nextSource : RufMaschineG D}
    {states : D.Lock → Zustand N} {lock : D.Lock} {next : Zustand N}
    (current : ImageTicketStates layout memory source states) (separate : LaySync layout)
    (bound : layout.sye ≤ 2 ^ 64)
    (writes : GleichAuf (fun byte => ¬ LockBytes layout lock byte) nextMemory memory)
    (preserved : OtherLockOwners lock source nextSource)
    (words : TicketWordsAt nextMemory (layout.lk lock) next) (protocol : Inv N next)
    (owners : TicketOwnership nextSource lock next) :
    ImageTicketStates layout nextMemory nextSource (fun other => if other = lock then next else states other) where
  words other := by
    by_cases same : other = lock
    · subst other
      simpa only [ite_true] using words
    · rw [ite_eq_right same]
      have fits := (separate.1 other).2.trans bound
      have reads (offset : Nat) (inside : offset ≤ 16) :
          nextMemory.rd64 (BitVec.ofNat 64 (layout.lk other + offset)) =
            memory.rd64 (BitVec.ofNat 64 (layout.lk other + offset)) :=
        gleich_rd64 fun byte hit => writes byte
          (lockBytes_disjoint separate same (lockWord_in_bytes fits inside hit))
      obtain ⟨drawn, serving, waiters⟩ := current.words other
      have first := reads 0 (Nat.zero_le 16)
      rw [Nat.add_zero] at first
      exact ⟨first.trans drawn, (reads 8 (by decide)).trans serving, (reads 16 (by decide)).trans waiters⟩
  protocol other := by
    by_cases same : other = lock
    · subst other
      simpa only [ite_true] using protocol
    · simpa only [ite_eq_right same] using current.protocol other
  owners other := by
    by_cases same : other = lock
    · subst other
      simpa only [ite_true] using owners
    · rw [ite_eq_right same]
      refine ⟨?_, ?_⟩
      · intro thread
        exact ((current.owners other).inside thread).trans (preserved other same thread.val).symm
      · intro thread beyond held
        exact (current.owners other).outside thread beyond ((preserved other same thread).mp held)

/-- A serving-word write changes only the selected reservation. The
    release proof supplies the new owner, queue and words directly. -/
theorem ImageTicketStates.writeServing {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {memory : Mem} {source nextSource : RufMaschineG D}
    {states : D.Lock → Zustand N} {lock : D.Lock} {next : Zustand N} {word : W}
    (current : ImageTicketStates layout memory source states) (separate : LaySync layout)
    (bound : layout.sye ≤ 2 ^ 64)
    (preserved : OtherLockOwners lock source nextSource)
    (words : TicketWordsAt (Mem.write memory (BitVec.ofNat 64 (layout.lk lock + 8)) 8 word.toNat)
      (layout.lk lock) next)
    (protocol : Inv N next) (owners : TicketOwnership nextSource lock next) :
    ImageTicketStates layout (Mem.write memory (BitVec.ofNat 64 (layout.lk lock + 8)) 8 word.toNat)
      nextSource (fun other => if other = lock then next else states other) := by
  refine current.update separate bound ?_ preserved words protocol owners
  intro byte outside
  have fits := (separate.1 lock).2.trans bound
  exact (write_nurIn memory (BitVec.ofNat 64 (layout.lk lock + 8)) word.toNat).gleichAt (fun touched =>
    outside (lockWord_in_bytes fits (by decide) touched))

/-- The actual draw CAS maintains the registry for every lock. Queuing
    changes the selected lock's counter and ticket position, and the
    committed GX state stays at the same lock-scope boundary. -/
theorem ImageTicketStates.draw [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {expected : Nat}
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (registered : (states lock).pc thread = .casN expected) (representable : expected < 2 ^ 64)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.lk lock)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 (layout.lk lock)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 (layout.lk lock)) (BitVec.ofNat 64 expected) (BitVec.ofNat 64 (expected + 1))) reply memory) :
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
      reply = some (BitVec.ofNat 64 (states lock).w.next, 0) ∧ memory.1.buf = machine.ms.1.buf ∧
      ∃ next, Schritt (states lock) thread next ∧
        ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  have space := (geometry.1 lock).2.trans bound
  obtain ⟨run, result, buffers, next, transition, words, ownership⟩ :=
    image_ticket_draw registered representable space (current.words lock) writable waiting answered
  obtain ⟨_, _, changed⟩ := image_CAS_reply (current.words lock).next writable waiting answered
  have otherBytes : GleichAuf (fun byte => ¬ LockBytes layout lock byte) memory.1.m machine.ms.1.m := by
    rw [changed]
    split
    · intro byte outside
      exact (write_nurIn _ _ _).gleichAt (fun touched =>
        outside (lockWord_in_bytes space (offset := 0) (by decide) (by simpa only [Nat.add_zero] using touched)))
    · intro byte _
      exact GleichAt.refl _ _
  have sameOwners : TicketOwnership source lock next := by
    refine ⟨?_, (current.owners lock).outside⟩
    intro other
    rw [ownership other]
    exact (current.owners lock).inside other
  exact ⟨run, result, buffers, next, transition,
    current.update geometry bound otherBytes (fun _ _ _ => Iff.rfl) words
      ((current.protocol lock).schritt capacity transition) sameOwners⟩

/-- Registering or unregistering a waiter changes only the selected
    lock's counter and wait phase. Failure of CAS changes neither the
    counter nor ownership, and lets the thread reload the word. -/
theorem ImageTicketStates.adjustWaiters [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {ticket sampled expected : Nat} (mode : WaitAdjustment)
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (saved : (states lock).pc thread = mode.expectedPlace ticket sampled expected)
    (representable : expected < 2 ^ 64)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.lk lock + 16)) 8 = true)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.cas (BitVec.ofNat 64 (layout.lk lock + 16)) (BitVec.ofNat 64 expected)
        (BitVec.ofNat 64 (mode.count expected))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.cas (BitVec.ofNat 64 (layout.lk lock + 16)) (BitVec.ofNat 64 expected)
        (BitVec.ofNat 64 (mode.count expected))) reply memory) :
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
      reply = some (BitVec.ofNat 64 (states lock).w.wait, 0) ∧ memory.1.buf = machine.ms.1.buf ∧
      ∃ next, Schritt (states lock) thread next ∧
        ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  have fits := (geometry.1 lock).2.trans bound
  obtain ⟨step, returned, buffers, next, advanced, words, invariant, owners, write⟩ :=
    image_ticket_waiter_CAS mode capacity (current.protocol lock) saved representable fits
      (current.words lock) writable waiting answered
  have untouched : GleichAuf (fun byte => ¬ LockBytes layout lock byte) memory.1.m machine.ms.1.m := by
    intro byte outside
    exact write byte (fun hit => outside (lockWord_in_bytes fits (by decide) hit))
  have sameOwners : TicketOwnership source lock next := by
    refine ⟨?_, (current.owners lock).outside⟩
    intro issuer
    rw [owners issuer]
    exact (current.owners lock).inside issuer
  exact ⟨step, returned, buffers, next, advanced,
    current.update geometry bound untouched (fun _ _ _ => Iff.rfl) words invariant sameOwners⟩

/-- A serving read that returns a different ticket preserves every
    source owner. The hosted strategy prepares its waiter increment,
    and the freestanding spin strategy stays at the same position. -/
theorem ImageTicketStates.retryServing [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {ticket : Nat} {footprint : Nat → W → Prop}
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (spins : layout.lockWait = .spin → SpinState (states lock))
    (saved : (states lock).pc thread = .ladeS ticket)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (shared : ∀ byte, fenster (BitVec.ofNat 64 (layout.lk lock + 8)) byte →
      ∀ owner, ¬ footprint owner byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.rd 8 (BitVec.ofNat 64 (layout.lk lock + 8))) resume)))
    (answered : imageTSO.ans machine.ms thread.val (.rd 8 (BitVec.ofNat 64 (layout.lk lock + 8))) reply memory)
    (unmatched : ∀ extra, reply ≠ some (BitVec.ofNat 64 ticket, extra)) :
    let next := match layout.lockWait with
      | .futex => (states lock).mit thread (.incL ticket (states lock).w.serv)
      | .spin => states lock
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
      memory = machine.ms ∧ BindingStep layout.lockWait (states lock) thread next ∧
      ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  intro next
  obtain ⟨step, unchanged, ⟨extra, observed⟩, actual, binding, words, _, _, exactRetry⟩ :=
    image_ticket_serving_read layout.lockWait spins saved (current.words lock) footprint buffers shared waiting answered
  have different : (states lock).w.serv % 2 ^ 64 ≠ ticket % 2 ^ 64 := by
    intro equality
    have word : BitVec.ofNat 64 (states lock).w.serv = BitVec.ofNat 64 ticket :=
      BitVec.eq_of_toNat_eq (by simpa only [BitVec.toNat_ofNat] using equality)
    apply unmatched extra
    exact observed.trans (congrArg (fun value => some (value, extra)) word)
  have exactNext : actual = next := exactRetry different
  rw [exactNext] at binding words
  have valid : Inv N next := by
    rcases (waitModel layout.lockWait).refines binding with same | stepped
    · rw [same]
      exact current.protocol lock
    · exact (current.protocol lock).schritt capacity stepped
  have sameOwners : TicketOwnership source lock next := by
    refine ⟨?_, (current.owners lock).outside⟩
    intro other
    have unchangedOwner : (next.pc other).haelt = ((states lock).pc other).haelt := by
      unfold next
      split
      · by_cases issuer : other = thread
        · subst other
          simp only [Zustand.mit, upd_self, saved, Ort.haelt]
        · change (upd (states lock).pc thread (.incL ticket (states lock).w.serv) other).haelt = _
          rw [upd_ne _ _ issuer]
      · rfl
    rw [unchangedOwner]
    exact (current.owners lock).inside other
  have stable : GleichAuf (fun byte => ¬ LockBytes layout lock byte) memory.1.m machine.ms.1.m := by
    rw [unchanged]
    exact fun byte _ => GleichAt.refl _ byte
  exact ⟨step, unchanged, binding, current.update geometry bound stable (fun _ _ _ => Iff.rfl) words valid sameOwners⟩

/-- A buffer drain may publish private writes, but cannot alter any
    of the shared ticket words or the source lock ownership. -/
theorem ImageTicketStates.flush [Kern] {D : Deklaration} {N : Nat} {layout : Lay D}
    {source : RufMaschineG D} {states : D.Lock → Zustand N}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {footprint : Nat → W → Prop}
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ lock byte, LockBytes layout lock byte → ∀ issuer, ¬ footprint issuer byte)
    (flushed : imageTSO.tau machine.ms memory) :
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths⟩ ∧
      PrivateBuffers footprint memory.1 ∧ projectSCState footprint memory = projectSCState footprint machine.ms ∧
      ImageTicketStates layout memory.1.m source states := by
  refine ⟨.tau flushed, buffers.flush flushed, projectSCState_flush flushed footprint
    (fun issuer store pending byte hit => (buffers issuer store pending byte hit).1) buffers.disjoint, ?_⟩
  have stable (lock : D.Lock) : GleichAuf (LockBytes layout lock) memory.1.m machine.ms.1.m := by
    obtain ⟨issuer, address, value, tail, head, changed⟩ := flushed
    intro byte lockByte
    have pending : (address, value) ∈ machine.ms.1.buf issuer := by
      rw [head]
      exact List.mem_cons_self
    rw [changed]
    exact (write_nurIn _ _ _).gleichAt (fun hit =>
      outside lock byte lockByte issuer (buffers issuer (address, value) pending byte hit).1)
  refine ⟨?_, current.protocol, current.owners⟩
  intro lock
  have fits := (geometry.1 lock).2.trans bound
  have read (offset : Nat) (within : offset ≤ 16) :
      memory.1.m.rd64 (BitVec.ofNat 64 (layout.lk lock + offset)) =
        machine.ms.1.m.rd64 (BitVec.ofNat 64 (layout.lk lock + offset)) :=
    gleich_rd64 fun byte hit => stable lock byte (lockWord_in_bytes fits within hit)
  have first := read 0 (by decide)
  rw [Nat.add_zero] at first
  exact ⟨first.trans (current.words lock).next,
    (read 8 (by decide)).trans (current.words lock).serving,
    (read 16 (by decide)).trans (current.words lock).waiters⟩

/-- A control-only lock transition can change the entire waiter queue.
    Only its ownership bits and the three physical counters must stay
    the same. Hosts can change hidden buffered bytes outside the locks. -/
theorem ImageTicketStates.control_update {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N}
    {memory nextMemory : Mem} {lock : D.Lock} {next : Zustand N}
    (current : ImageTicketStates layout memory source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64)
    (sameBytes : ∀ other byte, LockBytes layout other byte → GleichAt nextMemory memory byte)
    (sameWords : next.w = (states lock).w)
    (nextInv : Inv N next) (owners : ∀ t, (next.pc t).haelt = ((states lock).pc t).haelt) :
    ImageTicketStates layout nextMemory source (fun other => if other = lock then next else states other) where
  words other := by
    have fits := (geometry.1 other).2.trans bound
    have read (offset : Nat) (inside : offset ≤ 16) :
        nextMemory.rd64 (BitVec.ofNat 64 (layout.lk other + offset)) =
          memory.rd64 (BitVec.ofNat 64 (layout.lk other + offset)) :=
      gleich_rd64 fun byte touched => sameBytes other byte (lockWord_in_bytes fits inside touched)
    have first := read 0 (Nat.zero_le 16)
    rw [Nat.add_zero] at first
    obtain ⟨drawn, serving, waiters⟩ := current.words other
    have w : (if other = lock then next else states other).w = (states other).w := by
      split
      · rename_i same
        subst other
        exact sameWords
      · rfl
    exact ⟨by rw [w]; exact first.trans drawn,
      by rw [w]; exact (read 8 (by decide)).trans serving,
      by rw [w]; exact (read 16 (by decide)).trans waiters⟩
  protocol other := by
    split
    · exact nextInv
    · exact current.protocol other
  owners other := by
    split
    · rename_i same
      subst other
      refine ⟨?_, (current.owners lock).outside⟩
      intro t
      rw [owners t]
      exact (current.owners lock).inside t
    · exact current.owners other

/-- A real returning WAIT keeps every lock word readable and exact.
    Spurious resumption changes the ghost waiter phase in the same
    scheduled thread, while the source owner and world stay unchanged. -/
theorem ImageTicketStates.wait_reply [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {ticket sampled : Nat} {footprint : Nat → W → Prop}
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (host : ImageFutexAnswers) (saved : (states lock).pc thread = .futexW ticket sampled)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ other byte, LockBytes layout other byte → ∀ i, ¬ footprint i byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask (.sys
      (futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 128 (BitVec.ofNat 64 sampled))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.sys (futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 128 (BitVec.ofNat 64 sampled))) reply memory) :
    let request := futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 128 (BitVec.ofNat 64 sampled)
    let next := (states lock).mit thread (.decL ticket sampled)
    ProcessStep imageTSO actI machine [(thread.val, request, reply)]
      ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
    reply.isSome = true ∧ projectSCState footprint memory = projectSCState footprint machine.ms ∧
    ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  intro request next
  obtain ⟨ran, returned, sameMemory, trace, committed⟩ :=
    image_ticket_wait_reply host saved footprint buffers waiting answered
  have preserve {target : Zustand N}
      (steps : Relation.ReflTransGen (fun current target => Schritt current thread target) (states lock) target) :
      Inv N target := by
    induction steps with
    | refl => exact current.protocol lock
    | tail _ step ih => exact ih.schritt capacity step
  have owns (t : Fin N) : (next.pc t).haelt = ((states lock).pc t).haelt := by
    change (upd (states lock).pc thread (.decL ticket sampled) t).haelt = _
    by_cases same : t = thread
    · subst t
      simp only [upd_self, saved, Ort.haelt]
    · rw [upd_ne _ _ same]
  exact ⟨ran, returned, sameMemory,
    current.control_update geometry bound (fun other byte present => committed byte (outside other byte present))
      rfl (preserve trace) owns⟩

/-- The real WAKE-all response updates every blocked position at this
    lock and preserves the complete registry, including other locks. -/
theorem ImageTicketStates.wake_reply [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {footprint : Nat → W → Prop}
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (host : ImageFutexAnswers) (saved : (states lock).pc thread = .weck)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ other byte, LockBytes layout other byte → ∀ i, ¬ footprint i byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask (.sys
      (futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 129 2147483647)) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.sys (futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 129 2147483647)) reply memory) :
    let request := futexReq (BitVec.ofNat 64 (layout.lk lock + 8)) 129 2147483647
    let next : Zustand N := ⟨(states lock).w, upd (wecke (states lock).pc) thread .frei, (states lock).q⟩
    ProcessStep imageTSO actI machine [(thread.val, request, reply)]
      ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
    reply.isSome = true ∧ projectSCState footprint memory = projectSCState footprint machine.ms ∧
    Schritt (states lock) thread next ∧
    ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  intro request next
  have fits := (geometry.1 lock).2.trans bound
  obtain ⟨ran, returned, sameMemory, wake, _, nextInv, committed⟩ :=
    image_ticket_wake_reply host capacity (current.protocol lock) saved (current.words lock) footprint buffers
      (fun offset within byte touched => outside lock byte (lockWord_in_bytes fits (by omega) touched)) waiting answered
  have owns (t : Fin N) : (next.pc t).haelt = ((states lock).pc t).haelt := by
    change (upd (wecke (states lock).pc) thread .frei t).haelt = _
    by_cases same : t = thread
    · subst t
      simp only [upd_self, saved, Ort.haelt]
    · rw [upd_ne _ _ same, wecke_apply, geweckt_haelt]
  exact ⟨ran, returned, sameMemory, wake,
    current.control_update geometry bound (fun other byte present => committed byte (outside other byte present))
      rfl nextInv owns⟩

end Gabbro.Stage0.Senke.Faeden
