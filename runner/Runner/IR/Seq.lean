import Runner.IR.Step
import Runner.Basis.MemLemma

/-! # One `S0IR` thread on one memory, and the steps of single instructions

`Run r m t m'`: the request tree `r`, answered by the memory `m` (sequentially consistent) and by the kernel
(`Kern`, a system call), ends in the thread state `t` with the memory `m'`. `Star t m t' m'`: instruction after instruction. This is the
IR side of `ir_sim` (the lowering of stage 0 against machine G); with `runner_sc` it reaches the runner.

`InsAt m pc o a b c`: the memory holds the instruction with opcode `o` and fields `a b c` at `pc`. The lemmas
below run one instruction from its fields and slots. -/

namespace Runner.IR

/-- The answer of the memory to a request; `none` for a system call (not answered here). -/
def memAns (m : Mem) : Op → Option (Ans × Mem)
  | .rd 1 a => some ((m.rd8 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd 4 a => some ((m.rd32 a).map (fun v => (v.setWidth 64, 0)), m)
  | .rd _ a => some ((m.rd64 a).map (fun v => (v, 0)), m)
  | .wr a v => some (match m.wr64 a v with | some m' => (some (0, 0), m') | none => (none, m))
  | .cas a e n => some (match m.cas a e n with | some (o, m') => (some (o, 0), m') | none => (none, m))
  | .sys _ => none

/-- **The kernel**: which answer and which memory a system call may leave. Any relation; what a program may rely
    on is the named assumption at its gates (`Stage0/Senke/Tor`). -/
class Kern where
  ans : Req → Mem → Ans → Mem → Prop

variable [Kern]

inductive Run : Res T → Mem → T → Mem → Prop
  | next {t : T} {m : Mem} : Run (.next t) m t m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      memAns m o = some (a, m') → Run (k a) m' t m'' → Run (.ask o k) m t m''
  | sys {q : Req} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      Kern.ans q m a m' → Run (k a) m' t m'' → Run (.ask (.sys q) k) m t m''

inductive Star : T → Mem → T → Mem → Prop
  | refl (t : T) (m : Mem) : Star t m t m
  | next {t t' t'' : T} {m m' m'' : Mem} : Run (Runner.IR.step t) m t' m' → Star t' m' t'' m'' →
      Star t m t'' m''

theorem Star.trans {t1 t2 t3 : T} {m1 m2 m3 : Mem} (h1 : Star t1 m1 t2 m2) (h2 : Star t2 m2 t3 m3) :
    Star t1 m1 t3 m3 := by
  induction h1 with
  | refl => exact h2
  | next h _ ih => exact .next h (ih h2)

theorem Star.one {t t' : T} {m m' : Mem} (h : Run (step t) m t' m') : Star t m t' m' := .next h (.refl _ _)

/-! ## Reading the instruction -/

structure InsAt (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) : Prop where
  op : m.rd8 pc = some (BitVec.ofNat 8 o)
  f1 : m.rd32 (pc + 4) = some a
  f2 : m.rd32 (pc + 8) = some b
  f3 : m.rd32 (pc + 12) = some c

theorem run_rd8 {a : W} {v : B} {m : Mem} {f : W → Res T} {t : T} {m' : Mem} (h : m.rd8 a = some v)
    (hr : Run (f (v.setWidth 64)) m t m') : Run (rd8 a f) m t m' := by
  refine .ask (a := some (v.setWidth 64, 0)) (m' := m) (by simp [memAns, h]) ?_
  simpa [opt] using hr

theorem run_rd32 {a : W} {v : BitVec 32} {m : Mem} {f : BitVec 32 → Res T} {t : T} {m' : Mem}
    (h : m.rd32 a = some v) (hr : Run (f v) m t m') : Run (rd32 a f) m t m' := by
  refine .ask (a := some (v.setWidth 64, 0)) (m' := m) (by simp [memAns, h]) ?_
  simpa [opt] using hr

theorem run_rd64 {a : W} {v : W} {m : Mem} {f : W → Res T} {t : T} {m' : Mem}
    (h : m.rd64 a = some v) (hr : Run (f v) m t m') : Run (rd64 a f) m t m' :=
  .ask (a := some (v, 0)) (m' := m) (by simp [memAns, h]) (by simpa [opt] using hr)

theorem run_wr64 {a v : W} {m m1 : Mem} {s : T} (h : m.wr64 a v = some m1) : Run (wr64 a v s) m s m1 :=
  .ask (a := some (0, 0)) (m' := m1) (by simp [memAns, h]) (by simpa [opt] using Run.next)

theorem run_step {t : T} {m : Mem} {o : Nat} {a b c : BitVec 32} (hi : InsAt m t.pc o a b c) (ho : o < 256)
    {t' : T} {m' : Mem} (hr : Run (op o t) m t' m') : Run (step t) m t' m' := by
  refine run_rd8 hi.op ?_
  have : ((BitVec.ofNat 8 o).setWidth 64).toNat = o := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  rw [this]
  exact hr

/-! ## Single instructions -/

theorem f1_run {t : T} {m : Mem} {o : Nat} {a b c : BitVec 32} (hi : InsAt m t.pc o a b c) {f : W → Res T}
    {t' : T} {m' : Mem} (h : Run (f (sx a)) m t' m') : Run (f1 t f) m t' m' := run_rd32 hi.f1 h

theorem f2_run {t : T} {m : Mem} {o : Nat} {a b c : BitVec 32} (hi : InsAt m t.pc o a b c) {f : W → Res T}
    {t' : T} {m' : Mem} (h : Run (f (sx b)) m t' m') : Run (f2 t f) m t' m' := run_rd32 hi.f2 h

theorem f3_run {t : T} {m : Mem} {o : Nat} {a b c : BitVec 32} (hi : InsAt m t.pc o a b c) {f : W → Res T}
    {t' : T} {m' : Mem} (h : Run (f (sx c)) m t' m') : Run (f3 t f) m t' m' := run_rd32 hi.f3 h

/-- `d := g a b` for a binary opcode `o` (3-14), the slot `d` writable. -/
theorem run_bin {t : T} {m m1 : Mem} {o : Nat} {d a b : BitVec 32} (hi : InsAt m t.pc o d a b)
    {g : W → W → Option W} {va vb r : W} (ha : m.rd64 (slot t.fp (sx a)) = some va)
    (hb : m.rd64 (slot t.fp (sx b)) = some vb) (hg : g va vb = some r)
    (hw : m.wr64 (slot t.fp (sx d)) r = some m1) : Run (bin g t) m (nxt t) m1 := by
  refine f2_run hi (run_rd64 ha (f3_run hi (run_rd64 hb ?_)))
  simp only [hg, opt_some, ret1]
  exact f1_run hi (run_wr64 hw)

/-- `brz a L` with slot `a` zero: the jump is taken. -/
theorem run_brz_zero {t : T} {m : Mem} {a l c : BitVec 32} (hi : InsAt m t.pc 19 a l c)
    (ha : m.rd64 (slot t.fp (sx a)) = some 0) : Run (op 19 t) m { t with pc := t.pc + sx l } m := by
  simp only [op]
  refine f1_run hi ?_
  simp only [ld]
  refine run_rd64 ha ?_
  simp only [↓reduceIte]
  exact f2_run hi Run.next

/-- `brz a L` with slot `a` not zero: on to the next instruction. -/
theorem run_brz_ne {t : T} {m : Mem} {a l c : BitVec 32} {v : W} (hi : InsAt m t.pc 19 a l c)
    (ha : m.rd64 (slot t.fp (sx a)) = some v) (hv : v ≠ 0) : Run (op 19 t) m (nxt t) m := by
  simp only [op]
  refine f1_run hi ?_
  simp only [ld]
  refine run_rd64 ha ?_
  simp only [hv, ↓reduceIte]
  exact Run.next

theorem run_jmp {t : T} {m : Mem} {l b c : BitVec 32} (hi : InsAt m t.pc 18 l b c) :
    Run (op 18 t) m { t with pc := t.pc + sx l } m := by
  simp only [op]
  exact f1_run hi Run.next

/-- `call a k`: the target from slot `a`; the return `pc` and the caller's `fp` into the new frame's first two
    words; on at the target with the new frame. -/
theorem run_call {t : T} {m m1 m2 : Mem} {a k c : BitVec 32} {tg : W} (hi : InsAt m t.pc 20 a k c)
    (ha : m.rd64 (slot t.fp (sx a)) = some tg) (h1 : m.wr64 (slot t.fp (sx k)) (t.pc + 16) = some m1)
    (h2 : m1.wr64 (slot t.fp (sx k) + 8) t.fp = some m2) :
    Run (op 20 t) m ⟨tg, slot t.fp (sx k)⟩ m2 := by
  simp only [op]
  refine f1_run hi ?_
  simp only [ld]
  refine run_rd64 ha ?_
  refine f2_run hi ?_
  refine .ask (a := some (0, 0)) (m' := m1) ?_ (by simpa [opt] using run_wr64 h2)
  simp only [memAns, h1]

/-- `ld d a`: the word at the address in slot `a` into slot `d`. -/
theorem run_ld {t : T} {m m1 : Mem} {d a c : BitVec 32} (hi : InsAt m t.pc 15 d a c) {va v : W}
    (ha : m.rd64 (slot t.fp (sx a)) = some va) (hv : m.rd64 va = some v)
    (hw : m.wr64 (slot t.fp (sx d)) v = some m1) : Run (op 15 t) m (nxt t) m1 := by
  simp only [op]
  exact f2_run hi (run_rd64 ha (run_rd64 hv (f1_run hi (run_wr64 hw))))

/-- `st a b`: the word of slot `b` to the address in slot `a`. -/
theorem run_st {t : T} {m m1 : Mem} {a b c : BitVec 32} (hi : InsAt m t.pc 16 a b c) {va vb : W}
    (ha : m.rd64 (slot t.fp (sx a)) = some va) (hb : m.rd64 (slot t.fp (sx b)) = some vb)
    (hw : m.wr64 va vb = some m1) : Run (op 16 t) m (nxt t) m1 := by
  simp only [op]
  exact f1_run hi (run_rd64 ha (f2_run hi (run_rd64 hb (run_wr64 hw))))

/-- `ret`: on at the return `pc` and the caller's `fp`, the frame's first two words. -/
theorem run_ret {t : T} {m : Mem} {p f : W} (h0 : m.rd64 t.fp = some p) (h1 : m.rd64 (t.fp + 8) = some f) :
    Run (op 21 t) m ⟨p, f⟩ m := by
  simp only [op]
  exact run_rd64 h0 (run_rd64 h1 Run.next)

/-! ## Stopping: the run reaches a request to the kernel -/

/-- The tree, answered by the memory, reaches the system call `q` (which the memory does not answer). -/
inductive RunTo : Res T → Mem → Req → Prop
  | sys {q : Req} {k : Ans → Res T} {m : Mem} : RunTo (.ask (.sys q) k) m q
  | ask {o : Op} {k : Ans → Res T} {m m' : Mem} {a : Ans} {q : Req} :
      memAns m o = some (a, m') → RunTo (k a) m' q → RunTo (.ask o k) m q

theorem runTo_rd8 {a : W} {v : B} {m : Mem} {f : W → Res T} {q : Req} (h : m.rd8 a = some v)
    (hr : RunTo (f (v.setWidth 64)) m q) : RunTo (rd8 a f) m q :=
  .ask (a := some (v.setWidth 64, 0)) (m' := m) (by simp [memAns, h]) (by simpa [opt] using hr)

theorem runTo_rd32 {a : W} {v : BitVec 32} {m : Mem} {f : BitVec 32 → Res T} {q : Req}
    (h : m.rd32 a = some v) (hr : RunTo (f v) m q) : RunTo (rd32 a f) m q :=
  .ask (a := some (v.setWidth 64, 0)) (m' := m) (by simp [memAns, h]) (by simpa [opt] using hr)

theorem runTo_rd64 {a : W} {v : W} {m : Mem} {f : W → Res T} {q : Req}
    (h : m.rd64 a = some v) (hr : RunTo (f v) m q) : RunTo (rd64 a f) m q :=
  .ask (a := some (v, 0)) (m' := m) (by simp [memAns, h]) (by simpa [opt] using hr)

/-- The thread at `t` asks the kernel `q` in its next instruction. -/
def StopAt (t : T) (m : Mem) (q : Req) : Prop := RunTo (step t) m q

/-- `sys d a` with the number and the six arguments in slots `a .. a+6`. -/
theorem runTo_sys {t : T} {m : Mem} {d a c : BitVec 32} (hi : InsAt m t.pc 23 d a c)
    {nr a1 a2 a3 a4 a5 a6 : W}
    (h0 : m.rd64 (slot t.fp (sx a)) = some nr) (h1 : m.rd64 (slot t.fp (sx a) + 8) = some a1)
    (h2 : m.rd64 (slot t.fp (sx a) + 16) = some a2) (h3 : m.rd64 (slot t.fp (sx a) + 24) = some a3)
    (h4 : m.rd64 (slot t.fp (sx a) + 32) = some a4) (h5 : m.rd64 (slot t.fp (sx a) + 40) = some a5)
    (h6 : m.rd64 (slot t.fp (sx a) + 48) = some a6) : StopAt t m ⟨nr, a1, a2, a3, a4, a5, a6⟩ := by
  unfold StopAt step
  refine runTo_rd8 hi.op ?_
  have : ((BitVec.ofNat 8 23).setWidth 64).toNat = 23 := by decide
  rw [this]
  simp only [op]
  refine runTo_rd32 hi.f1 (runTo_rd32 hi.f2 ?_)
  simp only [ld]
  refine runTo_rd64 h0 (runTo_rd64 h1 (runTo_rd64 h2 (runTo_rd64 h3 (runTo_rd64 h4 (runTo_rd64 h5
    (runTo_rd64 h6 RunTo.sys))))))

end Runner.IR
