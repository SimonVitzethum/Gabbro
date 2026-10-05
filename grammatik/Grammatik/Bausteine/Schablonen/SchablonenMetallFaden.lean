/-
  File:      Grammatik/SchablonenMetallFaden.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): the GENERATED thread runtime of the
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
  and the queue lock (the runtime-internal ticket lock of `CTicket.lean`, held with IF = 0, so
  the two queue operations below run one at a time per core).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL its
  premises jointly.
-/

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
      simp
  | none =>
      simp only
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a r => rw [hq] at hs; simp [List.getLast?_cons] at hs
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
  | none => simp [nimm, hq]
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
  have h1 : Kette (haenge leer 5) [5] := haenge_kette leer_kette 5 (by simp)
  have h2 : Kette (haenge (haenge leer 5) 7) [5, 7] := haenge_kette h1 7 (by simp)
  have h3 : Kette q3 [5, 7, 9] := haenge_kette h2 9 (by simp)
  have hn := nimm_kette h3
  exact ⟨h3, hn.1, haenge_kette hn.2 2 (by simp)⟩

/-! ### The scheduler loop is round robin on its core -/

/-- One pass of `metall_kern_schleife` over the queue as a list: take the head, run it until it
    gives the core back; a thread that ended (`tot`) is buried, any other goes to the tail. -/
def schritt (tot : Nat → Bool) : List Nat → List Nat
  | [] => []
  | t :: r => if tot t then r else r ++ [t]

def nachSchritten (tot : Nat → Bool) : Nat → List Nat → List Nat
  | 0, l => l
  | n + 1, l => nachSchritten tot n (schritt tot l)

theorem schritt_rueckt (tot : Nat → Bool) (h : Nat) (r : List Nat) (p : Nat) (hp : p < r.length) :
    (schritt tot (h :: r))[p]? = r[p]? := by
  show (if tot h then r else r ++ [h])[p]? = r[p]?
  split
  · rfl
  · exact List.getElem?_append_left hp

/-- **NO THREAD STARVES ON ITS CORE**: a thread at position `p` of its core's queue is at the
    head -- the next to run -- after `p` passes of the loop, whatever the threads ahead of it
    do (end, or give the core back). -/
theorem schleife_fair (tot : Nat → Bool) :
    ∀ (p : Nat) (l : List Nat) (t : Nat), l[p]? = some t → (nachSchritten tot p l).head? = some t := by
  intro p
  induction p with
  | zero =>
      intro l t h
      cases l with
      | nil => cases h
      | cons a r => simpa [nachSchritten] using h
  | succ p ih =>
      intro l t h
      cases l with
      | nil => cases h
      | cons a r =>
          have hp : p < r.length := by
            have := List.getElem?_eq_some_iff.mp h
            obtain ⟨hl, _⟩ := this
            simp only [List.length_cons] at hl; omega
          have hr : r[p]? = some t := by simpa using h
          exact ih (schritt tot (a :: r)) t (by rw [schritt_rueckt tot a r p hp]; exact hr)

theorem schleife_zeuge :
    (nachSchritten (fun t => t == 7) 2 [5, 7, 9, 2]).head? = some 9 ∧
      nachSchritten (fun t => t == 7) 2 [5, 7, 9, 2] = [9, 2, 5] := by
  exact ⟨rfl, rfl⟩

/-! ## 2. The first frame of a thread -/

/-- The nine words `rahmen_neu` writes below the 16-aligned top, read from the new `rsp`
    upwards: MXCSR | FCW << 32, r15, r14, r13, r12, rbx, rbp (all zero), the thread entry
    (`metall_schalte`'s return address), and a zero fake return address. -/
def rahmen (eintritt : Nat) : List Nat :=
  [0x1F80 + 0x037F * 4294967296, 0, 0, 0, 0, 0, 0, eintritt, 0]

/-- What `metall_schalte` leaves after `movq %rsi, %rsp` onto a frame `w` at `rsp`:
    `ldmxcsr (%rsp)`, `fldcw 4(%rsp)`, `addq $8`, six pops, `ret`. -/
structure Nach where
  mxcsr : Nat
  fcw : Nat
  regs : List Nat
  rip : Nat
  rsp : Nat

def schalteAuf (rsp : Nat) (w : List Nat) : Nach :=
  { mxcsr := w.getD 0 0 % 4294967296,
    fcw := (w.getD 0 0 / 4294967296) % 65536,
    regs := [w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0, w.getD 5 0, w.getD 6 0],
    rip := w.getD 7 0,
    rsp := rsp + 8 * 8 }

/-- **THE FRAME STARTS THE THREAD AT ITS ENTRY, ALIGNED**: written at `top - 72` below a
    16-aligned `top`, the switch pops zero registers, the reset MXCSR (`0x1F80`) and x87
    control word (`0x037F`), returns into the entry, and leaves `rsp = top - 8` -- so `rsp + 8`
    is 16-aligned, the condition at a function's first instruction. -/
theorem rahmen_korrekt (top eintritt : Nat) (h72 : 72 ≤ top) (hal : top % 16 = 0) :
    (schalteAuf (top - 72) (rahmen eintritt)).mxcsr = 0x1F80 ∧
      (schalteAuf (top - 72) (rahmen eintritt)).fcw = 0x037F ∧
      (schalteAuf (top - 72) (rahmen eintritt)).regs = [0, 0, 0, 0, 0, 0] ∧
      (schalteAuf (top - 72) (rahmen eintritt)).rip = eintritt ∧
      (schalteAuf (top - 72) (rahmen eintritt)).rsp = top - 8 ∧
      ((schalteAuf (top - 72) (rahmen eintritt)).rsp + 8) % 16 = 0 := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp [schalteAuf, rahmen]
  · simp [schalteAuf, rahmen]
  · show top - 72 + 8 * 8 = top - 8; omega
  · show (top - 72 + 8 * 8 + 8) % 16 = 0; omega

/-! ## 3. The placement -/

/-- **ROUND ROBIN STAYS ON THE CORES THAT CHECKED IN**: `fetch_add(&naechster_kern, 1) % n`
    with `n = metall_kerne() >= 1` (the BSP counts itself before any start). -/
theorem platz_im_bereich (zaehler n : Nat) (hn : 0 < n) : zaehler % n < n := Nat.mod_lt _ hn

/-! ## 4. The join -/

/-- What happens to a thread's join word, in the order the runtime does it. -/
inductive Ereignis where
  | setzt (v : Nat)   -- `atomic_store(wort, index + 1)` in `faden_anlegen`, BEFORE the queueing
  | schritt           -- one step of the thread's root
  | ende              -- `t->zustand = TOT`, the last switch off its stack
  | null              -- `begrabe`: `atomic_store(wort, 0)` from the core's own stack
  deriving DecidableEq

def wort (w0 : Nat) : List Ereignis → Nat
  | [] => w0
  | .setzt v :: r => wort v r
  | .null :: r => wort 0 r
  | _ :: r => wort w0 r

/-- The template's order for a thread of slot `i` whose root takes `k` steps. -/
def spur (i k : Nat) : List Ereignis :=
  .setzt (i + 1) :: (List.replicate k .schritt ++ [.ende, .null])

theorem wort_schritte (v k : Nat) (r : List Ereignis) :
    wort v (List.replicate k .schritt ++ r) = wort v r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, wort]; exact ih

theorem wort_take_schritte (v k m : Nat) (hm : m ≤ k) (r : List Ereignis) :
    wort v ((List.replicate k Ereignis.schritt ++ r).take m) = v := by
  induction k generalizing m with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ k ih =>
      cases m with
      | zero => rfl
      | succ m =>
          simp only [List.replicate_succ, List.cons_append, List.take_succ_cons, wort]
          exact ih m (by omega)

theorem wort_take_nach (v k j : Nat) (r : List Ereignis) :
    wort v ((List.replicate k Ereignis.schritt ++ r).take (k + j)) = wort v (r.take j) := by
  induction k with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ k ih =>
      rw [show k + 1 + j = (k + j) + 1 by omega]
      simp only [List.replicate_succ, List.cons_append, List.take_succ_cons, wort]
      exact ih

/-- **A JOIN THAT READS ZERO SAW THE WHOLE RUN AND THE BURIAL**: a join begins after
    `gabbro_faden_start` returned, so after the first event; if the word it reads after any
    prefix of the template's order is zero, that prefix is the whole order -- every step of the
    root, its end, and the store of zero from the core's stack. -/
theorem warte_korrekt (i k w0 m : Nat) (hm : 1 ≤ m) (h0 : wort w0 ((spur i k).take m) = 0) :
    (spur i k).length ≤ m := by
  unfold spur at *
  cases m with
  | zero => omega
  | succ m =>
      simp only [List.take_succ_cons, wort] at h0
      simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
      by_cases hk : m ≤ k
      · rw [wort_take_schritte (i + 1) k m hk] at h0; omega
      · by_cases hk1 : m = k + 1
        · subst hk1
          rw [wort_take_nach (i + 1) k 1] at h0
          simp [wort] at h0
        · omega

/-- **The store before the queueing is load-bearing**: without it the word is the zeroed
    static's, and a join that begins right after the start reads zero while all `k` steps of
    the root are still ahead. -/
theorem warte_ohne_vorbelegung_waere_falsch (k : Nat) (_hk : 0 < k) :
    let ohne := List.replicate k Ereignis.schritt ++ [Ereignis.ende, Ereignis.null]
    wort 0 (ohne.take 0) = 0 ∧ 0 < ohne.length := by
  intro ohne
  exact ⟨rfl, by simp [ohne]⟩

/-- **Witness**: a thread of slot 3 with five steps -- the word reads 4 midway and right
    before the burial, and 0 at the end; the frame on a top of `0x200000`; a placement on 4
    cores. -/
theorem faden_metall_zeuge :
    wort 0 ((spur 3 5).take 3) = 4 ∧ wort 0 ((spur 3 5).take 7) = 4 ∧
      wort 0 (spur 3 5) = 0 ∧ (spur 3 5).length ≤ (spur 3 5).length ∧
      (schalteAuf (0x200000 - 72) (rahmen 0x101000)).rip = 0x101000 ∧
      (schalteAuf (0x200000 - 72) (rahmen 0x101000)).rsp = 0x200000 - 8 ∧ 9 % 4 < 4 := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, rfl, rfl, by decide⟩

end MetallFaden

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.MetallFaden.haenge_kette
#print axioms Gabbro.Grammatik.MetallFaden.nimm_kette
#print axioms Gabbro.Grammatik.MetallFaden.nimm_leer
#print axioms Gabbro.Grammatik.MetallFaden.schlange_fifo
#print axioms Gabbro.Grammatik.MetallFaden.schlange_zeuge
#print axioms Gabbro.Grammatik.MetallFaden.schleife_fair
#print axioms Gabbro.Grammatik.MetallFaden.schleife_zeuge
#print axioms Gabbro.Grammatik.MetallFaden.rahmen_korrekt
#print axioms Gabbro.Grammatik.MetallFaden.platz_im_bereich
#print axioms Gabbro.Grammatik.MetallFaden.warte_korrekt
#print axioms Gabbro.Grammatik.MetallFaden.warte_ohne_vorbelegung_waere_falsch
#print axioms Gabbro.Grammatik.MetallFaden.faden_metall_zeuge
