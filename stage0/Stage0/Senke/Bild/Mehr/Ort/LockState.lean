module

public import Stage0.Senke.Bild.Mehr.Ort.LockOwnership
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR Runner.Beweis Runner.Mem

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
    (preserved : ∀ other, other ≠ lock → ∀ thread,
      other ∈ offen (nextSource.faeden thread).spur ↔ other ∈ offen (source.faeden thread).spur)
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

end Gabbro.Stage0.Senke.Faeden
