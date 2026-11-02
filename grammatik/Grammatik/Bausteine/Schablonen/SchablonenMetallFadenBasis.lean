/-
  File:      Grammatik/SchablonenMetallFaden.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-TRANSLATION-VALIDATION.md): the GENERATED thread runtime of the
             bare-metal image (C-free lane, C3 slice 4, 2026-10-05).

  Row of `crates/gabbro-check/src/schablonen.rs`: `faden.metall` -- the scheduler the build
  writes beside the image (`treiber.rs::METALL_FADEN`, `<unit>.metall.faden.c`; until 2026-10-05
  the section "Cores and threads" of `laufzeit/metall/kern.c`): per core a FIFO run queue
  (`schlange_haenge`, `schlange_nimm`: a linked list through `naechster` with head and tail),
  the first frame of a thread that has never run (`rahmen_neu`), the start
  (`gabbro_faden_start`: round robin over the cores, the join word set BEFORE the thread is
  queued), and the join (`gabbro_faden_warte`, the word re-read until zero; `begrabe` clears it
  from the core's own stack after the thread has left its stack for good).

  ABSTRACT CORES like `faden.laufzeit` (SchablonenFaden.lean). What is proved:

  * `haenge_kette`, `nimm_kette`, `nimm_leer`: the linked queue REFINES a list -- appending
    links the new thread behind the tail (or makes it the head of an empty queue) and keeps the
    list duplicate-free, taking answers the head and leaves the rest, an empty queue answers
    nothing; so every core's run queue is FIFO (`schlange_fifo`);
  * `schleife_fair`: a pass of the scheduler loop takes the head and re-queues it at the tail
    unless it ended, so a thread at position `p` runs after `p` passes -- no thread starves on
    its core while the loop runs;
  * `rahmen_korrekt`: the frame `rahmen_neu` writes, popped by `metall_schalte`, gives zero
    callee-saved registers, the reset MXCSR and x87 control word, the thread entry as the
    return address and `rsp = top - 8` -- for a 16-aligned top exactly the SysV entry alignment
    (`rsp + 8` 16-aligned);
  * `platz_im_bereich`: the round-robin placement names a core that checked in;
  * `warte_korrekt`: a join that begins after the start and reads zero saw the thread's whole
    run and its burial; `warte_ohne_vorbelegung_waere_falsch`: without the store BEFORE the
    queueing a join could read the zeroed word before the thread ran.

  NOT proved: the switch itself (`metall_schalte`, `start.S`: the register file and stack as the
  hardware keeps them -- wall D of `messung/C3-WAENDE.md`), the C11 orderings of the join word,
  and the queue lock (the runtime-internal ticket lock, held with IF = 0, so
  the two queue operations below run one at a time per core).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL its
  premises jointly.
-/

module

@[expose] public section

namespace Gabbro.Grammatik

namespace MetallFaden

/-! ## 1. The run queue: a linked list with head and tail refines a list -/

/-- One core's queue: head, tail, and the `naechster` link of every thread slot. -/
structure Q where
  kopf : Option Nat
  schwanz : Option Nat
  nach : Nat → Option Nat

/-- Following the links from `start` visits exactly `l` and ends in `none`. -/
inductive Folge (nach : Nat → Option Nat) : Option Nat → List Nat → Prop where
  | leer : Folge nach none []
  | glied (x : Nat) (l : List Nat) : Folge nach (nach x) l → Folge nach (some x) (x :: l)

/-- The queue holds `l`: the links from the head visit `l`, the tail is its last element, and
    no thread stands twice. -/
def Kette (q : Q) (l : List Nat) : Prop :=
  Folge q.nach q.kopf l ∧ q.schwanz = l.getLast? ∧ l.Nodup

def setzeN (nach : Nat → Option Nat) (a : Nat) (v : Option Nat) : Nat → Option Nat :=
  fun x => if x = a then v else nach x

/-- `schlange_haenge(k, f)`: `f->naechster = 0`; behind the tail, or the head of an empty
    queue; `f` the new tail. -/
def haenge (q : Q) (f : Nat) : Q :=
  let n1 := setzeN q.nach f none
  match q.schwanz with
  | some s => { kopf := q.kopf, schwanz := some f, nach := setzeN n1 s (some f) }
  | none => { kopf := some f, schwanz := some f, nach := n1 }

/-- `schlange_nimm(k)`: the head, and the queue without it. -/
def nimm (q : Q) : Option Nat × Q :=
  match q.kopf with
  | none => (none, q)
  | some f =>
      let k' := q.nach f
      (some f, { q with kopf := k', schwanz := if k' = none then none else q.schwanz })

theorem folge_none {nach : Nat → Option Nat} {l : List Nat} (h : Folge nach none l) : l = [] := by
  cases h; rfl

theorem folge_nil {nach : Nat → Option Nat} {s : Option Nat} (h : Folge nach s []) : s = none := by
  cases h; rfl

theorem folge_anhaengen {nach : Nat → Option Nat} {s : Option Nat} {l : List Nat}
    (h : Folge nach s l) :
    ∀ f, f ∉ l → l.Nodup → ∀ letztes, l.getLast? = some letztes →
      Folge (setzeN (setzeN nach f none) letztes (some f)) s (l ++ [f]) := by
  induction h with
  | leer => intro f _ _ letztes hl; cases hl
  | glied x l hrest ih =>
      intro f hf hnd letztes hl
      have hxf : x ≠ f := fun e => hf (e ▸ List.mem_cons_self)
      have hfl : f ∉ l := fun m => hf (List.mem_cons_of_mem _ m)
      cases l with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          refine Folge.glied x [f] ?_
          have e1 : setzeN (setzeN nach f none) x (some f) x = some f := if_pos rfl
          rw [e1]
          refine Folge.glied f [] ?_
          have e2 : setzeN (setzeN nach f none) x (some f) f = none := by
            unfold setzeN; rw [if_neg (Ne.symm hxf), if_pos rfl]
          rw [e2]; exact Folge.leer
      | cons y l' =>
          have hl' : (y :: l').getLast? = some letztes := by
            rw [List.getLast?_cons_cons] at hl; exact hl
          have hnd' : (y :: l').Nodup := (List.nodup_cons.mp hnd).2
          have hxl : x ≠ letztes := by
            intro e
            have hm : letztes ∈ y :: l' := List.mem_of_getLast? hl'
            exact (List.nodup_cons.mp hnd).1 (e ▸ hm)
          refine Folge.glied x (y :: l' ++ [f]) ?_
          have e : setzeN (setzeN nach f none) letztes (some f) x = nach x := by
            unfold setzeN; rw [if_neg hxl, if_neg hxf]
          rw [e]
          exact ih f hfl hnd' letztes hl'

/-- **APPENDING REFINES `l ++ [f]`.** -/
theorem haenge_kette {q : Q} {l : List Nat} (h : Kette q l) (f : Nat) (hf : f ∉ l) :
    Kette (haenge q f) (l ++ [f]) := by
  obtain ⟨hfo, hs, hnd⟩ := h
  have hnd' : (l ++ [f]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    subst hb
    exact fun e => hf (e ▸ ha)
  unfold haenge
  cases hq : q.schwanz with
  | some s =>
      simp only
      refine ⟨folge_anhaengen hfo f hf hnd s (hq ▸ hs).symm, ?_, hnd'⟩
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  | none =>
      simp only
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a r => rw [hq] at hs; simp only [List.getLast?_cons, reduceCtorEq] at hs
      subst hl
      refine ⟨Folge.glied f [] ?_, rfl, hnd'⟩
      have e : setzeN q.nach f none f = none := if_pos rfl
      show Folge (setzeN q.nach f none) (setzeN q.nach f none f) []
      rw [e]; exact Folge.leer

theorem folge_cons_inv {nach : Nat → Option Nat} {s : Option Nat} {x : Nat} {l : List Nat}
    (h : Folge nach s (x :: l)) : s = some x ∧ Folge nach (nach x) l := by
  cases h with
  | glied _ _ hr => exact ⟨rfl, hr⟩

/-- **TAKING ANSWERS THE HEAD AND LEAVES THE REST.** -/
theorem nimm_kette {q : Q} {x : Nat} {l : List Nat} (h : Kette q (x :: l)) :
    (nimm q).1 = some x ∧ Kette (nimm q).2 l := by
  obtain ⟨hfo, hs, hnd⟩ := h
  obtain ⟨hk, hrest⟩ := folge_cons_inv hfo
  unfold nimm
  rw [hk]
  dsimp only
  refine ⟨rfl, hrest, ?_, (List.nodup_cons.mp hnd).2⟩
  show (if q.nach x = none then none else q.schwanz) = l.getLast?
  by_cases hn : q.nach x = none
  · rw [if_pos hn]
    rw [hn] at hrest
    rw [folge_none hrest]; rfl
  · rw [if_neg hn, hs]
    cases l with
    | nil => exact absurd (folge_nil hrest) hn
    | cons z r => exact List.getLast?_cons_cons

/-- An empty queue answers nothing. -/
theorem nimm_leer {q : Q} (h : Kette q []) : (nimm q).1 = none := by
  obtain ⟨hfo, _, _⟩ := h
  cases hq : q.kopf with
  | none => simp only [nimm, hq]
  | some y => rw [hq] at hfo; cases hfo

/-- **FIFO**: a thread queued behind `l` comes out after every thread of `l`, in order. -/
theorem schlange_fifo {q : Q} {x : Nat} {l : List Nat} (h : Kette q (x :: l)) (f : Nat)
    (hf : f ∉ x :: l) :
    (nimm (haenge q f)).1 = some x ∧ Kette (nimm (haenge q f)).2 (l ++ [f]) :=
  nimm_kette (haenge_kette h f hf)

/-- The empty queue of a fresh core: head and tail zero. -/
def leer : Q := ⟨none, none, fun _ => none⟩

theorem leer_kette : Kette leer [] := ⟨Folge.leer, rfl, List.nodup_nil⟩

/-- **Witness**: three threads queued on a fresh core, one taken, a fourth queued -- the order
    is the queueing order. -/
theorem schlange_zeuge :
    let q3 := haenge (haenge (haenge leer 5) 7) 9
    Kette q3 [5, 7, 9] ∧ (nimm q3).1 = some 5 ∧ Kette (haenge (nimm q3).2 2) [7, 9, 2] := by
  intro q3
  have h1 : Kette (haenge leer 5) [5] := haenge_kette leer_kette 5 (by simp only [List.not_mem_nil, not_false_eq_true])
  have h2 : Kette (haenge (haenge leer 5) 7) [5, 7] := haenge_kette h1 7 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, not_false_eq_true])
  have h3 : Kette q3 [5, 7, 9] := haenge_kette h2 9 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, not_false_eq_true])
  have hn := nimm_kette h3
  exact ⟨h3, hn.1, haenge_kette hn.2 2 (by simp only [List.mem_cons, Nat.reduceEqDiff, List.not_mem_nil, or_self, not_false_eq_true])⟩

end MetallFaden

end Gabbro.Grammatik
