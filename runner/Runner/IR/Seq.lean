import Runner.IR.Step
import Runner.Basis.MemLemma

/-! # One `S0IR` thread on one memory, and the steps of single instructions

`Run r m t m'`: the request tree `r`, answered by the memory `m` (sequentially consistent, no system call),
ends in the thread state `t` with the memory `m'`. `Star t m t' m'`: instruction after instruction. This is the
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

inductive Run : Res T → Mem → T → Mem → Prop
  | next {t : T} {m : Mem} : Run (.next t) m t m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      memAns m o = some (a, m') → Run (k a) m' t m'' → Run (.ask o k) m t m''

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

end Runner.IR
