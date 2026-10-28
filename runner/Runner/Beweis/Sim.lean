import Runner.Beweis.Lauf
import Runner.IR.Step
import Runner.Prog.Code

/-! # The simulation of one thread: the x86 thread makes the IR's requests

* `Lay`: the runner's code `C`, the handler of each opcode and the dispatch table. `CInv L`: every handler lies
  at its address in `C`.
* `Disp L t x`: `x` stands at a copy of the dispatch with `r12 = pc`, `r13 = fp` and `r14` the table.
* `Match L r x`: run from `x`, the x86 thread makes exactly the requests of the IR tree `r`, in the same order,
  and after each answer goes on matching what the IR does with that answer -- up to steps of its own (`priv`)
  and reads of the dispatch table (`tbl`, answered by the table's word). It ends where the IR ends: the same
  fault, or a dispatch copy related to the IR's next state.

`Match` speaks of requests, not of a memory: it holds under every memory model that answers a table read with
the table's word. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

structure Lay where
  C : W → B
  H : Nat → W
  T : W

/-- The address of the table entry of opcode byte `op`, as the dispatch computes it. -/
def taddr (L : Lay) (op : W) : W := L.T + op * BitVec.ofNat 64 (2 ^ 3) + sx32 0

def CInv (L : Lay) : Prop := ∀ k, Code L.C (L.H k) (handler k)

structure Disp (L : Lay) (t : IR.T) (x : X) : Prop where
  code : Code L.C x.rip dispatch
  pc : x.r12 = t.pc
  fp : x.r13 = t.fp
  tb : x.r14 = L.T

mutual
inductive Match (L : Lay) : Res IR.T → X → Prop
  | priv {r : Res IR.T} {x y : X} : step L.C x = .next y → Match L r y → Match L r x
  | tbl {r : Res IR.T} {x : X} {k : Ans → Res X} (op : Nat) :
      step L.C x = .ask (.rd 8 (taddr L (BitVec.ofNat 64 op))) k →
      (∀ w, MatchK L r (k (some (L.H op, w)))) → Match L r x
  | ask {o : Op} {kI : Ans → Res IR.T} {kX : Ans → Res X} {x : X} :
      step L.C x = .ask o kX → (∀ a, MatchK L (kI a) (kX a)) → Match L (.ask o kI) x
  | fault {x : X} : step L.C x = .fault → Match L .fault x
  | disp {t : IR.T} {x : X} : Disp L t x → Match L (.next t) x

/-- After an answer: both fault, or the x86 thread continues in a state that goes on matching. -/
inductive MatchK (L : Lay) : Res IR.T → Res X → Prop
  | fault : MatchK L .fault .fault
  | next {r : Res IR.T} {y : X} : Match L r y → MatchK L r (.next y)
end

/-! ## Straight code: the trees side by side -/

/-- The IR tree and the tree of a straight body from `y0`: the same requests, the same faults, and ends that
    agree on `r12`, `r13` and keep `r14`. -/
def Corr (y0 : X) : Res IR.T → Res X → Prop
  | .next t, .next z => z.r12 = t.pc ∧ z.r13 = t.fp ∧ z.r14 = y0.r14
  | .fault, .fault => True
  | .ask o k, .ask o' k' => o = o' ∧ ∀ a, Corr y0 (k a) (k' a)
  | _, _ => False

/-- After an answer, an instruction is done: it never asks twice. -/
theorem exec_once (i : Ins) (n : Nat) (x : X) {o : Op} {k : Ans → Res X} (h : exec i n x = .ask o k) (a : Ans) :
    k a = .fault ∨ ∃ y, k a = .next y := by
  cases i <;> simp only [exec, rd64, rd32, rd8, wr64, cas] at h
  all_goals first
    | (cases h; cases a <;> simp)
    | (split at h <;> cases h)
    | (split at h; cases h; split at h <;> cases h)
    | cases h

theorem straight_go {L : Lay} {y0 : X} (htb : y0.r14 = L.T) :
    ∀ (is : List Ins) (x : X) (r : Res IR.T), (∀ i ∈ is, Fall i = true) →
    Code L.C x.rip (is ++ dispatch) → Corr y0 r (runL is x) → Match L r x
  | [], x, r, _, hc, hco => by
    cases r with
    | next t =>
      obtain ⟨h1, h2, h3⟩ := hco
      exact .disp ⟨hc, h1, h2, h3.trans htb⟩
    | _ => simp [runL, Corr] at hco
  | i :: is, x, r, hf, hc, hco => by
    have hs := step_code hc
    have hfi := hf i (List.mem_cons_self ..)
    have hfs : ∀ j ∈ is, Fall j = true := fun j hj => hf j (List.mem_cons_of_mem _ hj)
    have hrip := exec_rip hfi (enc i).length x
    have hc' : ∀ y : X, y.rip = x.rip + BitVec.ofNat 64 (enc i).length → Code L.C y.rip (is ++ dispatch) :=
      fun y hy => by rw [hy]; exact hc.2.2
    simp only [runL] at hco
    cases he : exec i (enc i).length x with
    | next y =>
      rw [he, bind_next] at hco
      rw [he] at hrip
      exact .priv (hs.trans he) (straight_go htb is y r hfs (hc' y hrip) hco)
    | fault =>
      rw [he] at hco
      cases r <;> simp [Corr] at hco
      exact .fault (hs.trans he)
    | unk => rw [he] at hco; cases r <;> simp [Corr] at hco
    | ask o k =>
      rw [he, bind_ask] at hco
      cases r with
      | ask o' kI =>
        obtain ⟨rfl, hk⟩ := hco
        refine .ask (hs.trans he) fun a => ?_
        rw [he] at hrip
        rcases exec_once i _ x he a with hka | ⟨y, hka⟩
        · have : Corr y0 (kI a) ((k a).bind (runL is)) := hk a
          rw [hka, bind_fault] at this
          cases hkI : kI a <;> rw [hkI] at this <;> simp [Corr] at this
          rw [hka]; exact .fault
        · have : Corr y0 (kI a) ((k a).bind (runL is)) := hk a
          rw [hka, bind_next] at this
          have hy := hrip a
          rw [hka] at hy
          rw [hka]; exact .next (straight_go htb is y (kI a) hfs (hc' y hy) this)
      | _ => simp [Corr] at hco

/-! ## Code ending in a jump: the trees side by side, the ends matched by `Match` itself -/

def CorrM (L : Lay) : Res IR.T → Res X → Prop
  | r, .next z => Match L r z
  | .fault, .fault => True
  | .ask o k, .ask o' k' => o = o' ∧ ∀ a, CorrM L (k a) (k' a)
  | _, _ => False

theorem go {L : Lay} : ∀ (is : List Ins) (x : X) (r : Res IR.T), (∀ i ∈ is.dropLast, Fall i = true) →
    Code L.C x.rip is → CorrM L r (runL is x) → Match L r x
  | [], x, r, _, _, hco => by simpa [runL, CorrM] using hco
  | i :: is, x, r, hf, hc, hco => by
    have hs := step_code hc
    have hnext : ∀ y : X, y.rip = x.rip + BitVec.ofNat 64 (enc i).length → Code L.C y.rip is :=
      fun y hy => by rw [hy]; exact hc.2.2
    have hfs : ∀ j ∈ is.dropLast, Fall j = true := by
      intro j hj
      cases is with
      | nil => simp at hj
      | cons _ _ => exact hf j (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hj)
    -- the rest of the list: when it is empty the end is matched directly
    have hrest : ∀ (y : X) (r' : Res IR.T), (is ≠ [] → y.rip = x.rip + BitVec.ofNat 64 (enc i).length) →
        CorrM L r' (runL is y) → Match L r' y := by
      intro y r' hy hc'
      cases is with
      | nil => simpa [runL, CorrM] using hc'
      | cons j js => exact go (j :: js) y r' hfs (hnext y (hy (by simp))) hc'
    have hrip : is ≠ [] → Leaves (fun y => y.rip = x.rip + BitVec.ofNat 64 (enc i).length)
        (exec i (enc i).length x) := by
      intro hne
      cases is with
      | nil => exact absurd rfl hne
      | cons _ _ => exact exec_rip (hf i (by simp)) _ x
    simp only [runL] at hco
    cases he : exec i (enc i).length x with
    | next y =>
      rw [he, bind_next] at hco
      refine .priv (hs.trans he) (hrest y r (fun hne => ?_) hco)
      have := hrip hne
      rw [he] at this
      exact this
    | fault =>
      rw [he] at hco
      cases r <;> simp [CorrM] at hco
      exact .fault (hs.trans he)
    | unk => rw [he] at hco; cases r <;> simp [CorrM] at hco
    | ask o k =>
      rw [he, bind_ask] at hco
      cases r with
      | ask o' kI =>
        obtain ⟨rfl, hk⟩ := hco
        refine .ask (hs.trans he) fun a => ?_
        rcases exec_once i _ x he a with hka | ⟨y, hka⟩
        · have : CorrM L (kI a) ((k a).bind (runL is)) := hk a
          rw [hka, bind_fault] at this
          cases hkI : kI a <;> rw [hkI] at this <;> simp [CorrM] at this
          rw [hka]; exact .fault
        · have : CorrM L (kI a) ((k a).bind (runL is)) := hk a
          rw [hka, bind_next] at this
          rw [hka]
          refine .next (hrest y (kI a) (fun hne => ?_) this)
          have := hrip hne
          rw [he] at this
          have := this a
          rw [hka] at this
          exact this
      | _ => simp [CorrM] at hco

end Runner.Beweis
