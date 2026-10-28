import Runner.Beweis.Sim
import Runner.Beweis.BV

/-! # Matching the two request trees of a straight handler

`corr` unfolds the IR instruction and the x86 body into request trees, then walks them together: the same request
on both sides, a case split on the answer (refused: both fault), and at the end the same `pc`, `fp` and table. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

@[simp] theorem ir_sx (v : BitVec 32) : IR.sx v = sx32 v := rfl
@[simp] theorem sx32_zero : sx32 0#32 = 0#64 := by decide
@[simp] theorem sx32_4 : sx32 4#32 = 4#64 := by decide
@[simp] theorem sx32_8 : sx32 8#32 = 8#64 := by decide
@[simp] theorem sx32_12 : sx32 12#32 = 12#64 := by decide
@[simp] theorem sx32_16 : sx32 16#32 = 16#64 := by decide
@[simp] theorem sx32_24 : sx32 24#32 = 24#64 := by decide
@[simp] theorem sx32_32 : sx32 32#32 = 32#64 := by decide
@[simp] theorem sx32_40 : sx32 40#32 = 40#64 := by decide
@[simp] theorem sx32_48 : sx32 48#32 = 48#64 := by decide

theorem corr_ask {y0 : X} {o : Op} {k : Ans → Res IR.T} {k' : Ans → Res X} (h : ∀ a, Corr y0 (k a) (k' a)) :
    Corr y0 (.ask o k) (.ask o k') := ⟨rfl, h⟩

theorem corr_opt {σ : Type} {y0 : X} {o : Option σ} {f : σ → Res IR.T} {g : σ → Res X}
    (h : ∀ a, Corr y0 (f a) (g a)) : Corr y0 (opt o f) (opt o g) := by
  cases o
  · trivial
  · exact h _

macro "corr_tail" : tactic => `(tactic|
  repeat (first
    | (apply corr_ask; intro _)
    | (apply corr_opt; intro _)
    | (simp only [opt_some, bind_next, bind_ask, bind_opt])
    | (simp only [Corr, and_self]; done)
    | (simp [Corr, aluStep, aluOp, X.set, X.get, X.nof, exec, ea]; done)))

macro "corr" : tactic => `(tactic| (
  simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
    ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf, rd64, rd32, rd8, wr64, cas] <;>
  corr_tail))

end Runner.Beweis
