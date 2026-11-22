module

public import Stage0.Senke.Bild.Mehr.Ort.LockState

@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Grammatik Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR Runner.Mach Runner.Beweis

/-- Reads which only select the next ticket operation. Admission is
    separate because it changes the source's lock ownership. -/
inductive CounterLoad where
  | draw
  | increment (ticket sampled : Nat)
  | decrement (ticket sampled : Nat)
  | release (ticket : Nat)
  | wake

def CounterLoad.offset : CounterLoad → Nat
  | .draw => 0
  | .release _ => 8
  | _ => 16

def CounterLoad.word (load : CounterLoad) (words : Wort) : Nat :=
  match load with
  | .draw => words.next
  | .release _ => words.serv
  | _ => words.wait

def CounterLoad.before : CounterLoad → Ort
  | .draw => .ladeN
  | .increment ticket sampled => .incL ticket sampled
  | .decrement ticket sampled => .decL ticket sampled
  | .release ticket => .gibL ticket
  | .wake => .gibW

def CounterLoad.after (load : CounterLoad) (words : Wort) : Ort :=
  match load with
  | .draw => .casN (words.next % 2 ^ 64)
  | .increment ticket sampled => .incC ticket sampled words.wait
  | .decrement ticket sampled => .decC ticket sampled words.wait
  | .release ticket => .gibC ticket (words.serv % 2 ^ 64)
  | .wake => if words.wait = 0 then .frei else .weck

private theorem CounterLoad.inside (load : CounterLoad) : load.offset ≤ 16 := by
  cases load <;> decide

private theorem CounterLoad.read {N : Nat} {memory : Mem} {base : Nat} {current : Zustand N}
    (load : CounterLoad) (words : TicketWordsAt memory base current) :
    memory.rd64 (BitVec.ofNat 64 (base + load.offset)) = some (BitVec.ofNat 64 (load.word current.w)) := by
  cases load with
  | draw => simpa only [CounterLoad.offset, CounterLoad.word, Nat.add_zero] using words.next
  | increment | decrement | wake => exact words.waiters
  | release => exact words.serving

private theorem CounterLoad.step {N : Nat} {current : Zustand N} {thread : Fin N}
    (load : CounterLoad) (saved : current.pc thread = load.before) :
    Schritt current thread (current.mit thread (load.after current.w)) := by
  cases load with
  | draw => exact .liestN saved
  | increment => exact .liestInc saved
  | decrement => exact .liestDec saved
  | release => exact .liestGib saved
  | wake =>
    by_cases empty : current.w.wait = 0
    · simpa only [CounterLoad.after, if_pos empty] using Schritt.keinWarter saved empty
    · simpa only [CounterLoad.after, if_neg empty] using Schritt.warter saved empty

private theorem CounterLoad.sameOwner (load : CounterLoad) (words : Wort) :
    (load.after words).haelt = load.before.haelt := by
  cases load <;> try rfl
  case wake => unfold CounterLoad.after; split <;> rfl

/-- Real shared reads at the draw, waiter and release phases perform
    the corresponding protocol step, retain the complete lock registry
    and preserve the committed GX state. -/
theorem ImageTicketStates.readCounter [Kern] {D : Deklaration} [DecidableEq D.Lock] {N : Nat}
    {layout : Lay D} {source : RufMaschineG D} {states : D.Lock → Zustand N} {lock : D.Lock}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Fin N} {footprint : Nat → W → Prop} (load : CounterLoad)
    (current : ImageTicketStates layout machine.ms.1.m source states)
    (geometry : LaySync layout) (bound : layout.sye ≤ 2 ^ 64) (capacity : N ≤ 2147483647)
    (saved : (states lock).pc thread = load.before)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ byte, LockBytes layout lock byte → ¬ footprint thread.val byte)
    (waiting : machine.ths[thread.val]? = some (some (.ask
      (.rd 8 (BitVec.ofNat 64 (layout.lk lock + load.offset))) resume)))
    (answered : imageTSO.ans machine.ms thread.val
      (.rd 8 (BitVec.ofNat 64 (layout.lk lock + load.offset))) reply memory) :
    let next := (states lock).mit thread (load.after (states lock).w)
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread.val (some (resume reply))⟩ ∧
      memory = machine.ms ∧ (∃ extra, reply = some (BitVec.ofNat 64 (load.word (states lock).w), extra)) ∧
      Schritt (states lock) thread next ∧
      ImageTicketStates layout memory.1.m source (fun other => if other = lock then next else states other) := by
  intro next
  have fits := (geometry.1 lock).2.trans bound
  obtain ⟨step, unchanged, returned⟩ :=
    image_shared_word_reply (load.read (current.words lock)) buffers
      (fun byte hit => outside byte (lockWord_in_bytes fits load.inside hit)) waiting answered
  have move := load.step saved
  have stable : GleichAuf (fun byte => ¬ LockBytes layout lock byte) memory.1.m machine.ms.1.m := by
    rw [unchanged]
    exact fun byte _ => GleichAt.refl _ byte
  have words : TicketWordsAt memory.1.m (layout.lk lock) next := by
    rw [unchanged]
    exact ⟨(current.words lock).next, (current.words lock).serving, (current.words lock).waiters⟩
  have owners : TicketOwnership source lock next := by
    refine ⟨?_, (current.owners lock).outside⟩
    intro other
    change (upd (states lock).pc thread (load.after (states lock).w) other).haelt = true ↔ _
    by_cases issuer : other = thread
    · subst other
      rw [upd_self, load.sameOwner, ← saved]
      exact (current.owners lock).inside thread
    · rw [upd_ne _ _ issuer]
      exact (current.owners lock).inside other
  exact ⟨step, unchanged, returned, move, current.update geometry bound stable (fun _ _ _ => Iff.rfl)
    words ((current.protocol lock).schritt capacity move) owners⟩

end Gabbro.Stage0.Senke.Faeden
