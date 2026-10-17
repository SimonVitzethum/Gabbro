import Grammatik.Llvm.Model.Facts
import Grammatik.Llvm.Model.Print
import Grammatik.Llvm.Model.Weak

/-
  File:      Grammatik/Llvm/Model/Witness.lean
  Subject:   TRACK L, PHASE L0 -- A NON-DEGENERATE WITNESS of the IR model.

  One module, two functions and two globals, and every form the model is about used at least once:
    * `@sq`  -- a leaf that squares its argument;
    * `@main` -- an `alloca` with a `!range`/`!tbaa` load and a `llvm.assume`, a LOOP with two
      phis (i = 0 .. 4), a CALL of `@sq` per round, a `getelementptr` into a global array and a
      store through it, an `atomicrmw add` on a global counter, and after the loop an atomic
      load of the counter, a plain load through `gep`, and the result `sum + count + tab[3]`.
  The run is computed by the kernel (`decide`): sum of squares 0..4 is 30, the counter is 5,
  `tab[3]` is 9 (written in round 3), so `@main` returns 44.

  The same module is printed to `.ll` text (`Print.modl`), pinned by a few exact lines, and the
  weak-memory interface is shown NON-DEGENERATE: with two messages at a location the step
  relation has two different successors at an atomic load (`weak_two_successors`), where the SC
  interface has exactly one.
-/

namespace Gabbro.Llvm

open Gabbro.Grammatik.Speichermodell

namespace Witness

def i32 : Ty := .int 32

/-- `@sq(i32 %t0) -> i32 { ret x*x }`. -/
def sq : Func :=
  { name := "sq", params := [⟨i32, 0, false⟩], ret := i32,
    blks := [⟨0, [], [.bin 1 .mul 32 (.reg 0) (.reg 0)], .ret (some (.reg 1))⟩] }

/-- `@main() -> i32`, see the header. Registers: t0 the alloca, t1 the loaded 7, t2 the assumed
    comparison, t3/t4 the loop phis (i, acc), t5 the loop test, t6 the call result, t7 the
    index, t8 the 64-bit index, t9 the element pointer, t10 the next acc, t11 the next i,
    t12 the rmw result, t13 the counter, t14 the tab pointer, t15 tab[3], t16/t17 the sums. -/
def main : Func :=
  { name := "main", params := [], ret := i32,
    blks :=
      [ ⟨0, [],
          [ .alloc 0 i32 4,
            .store i32 (.int 32 7) (.reg 0) 4 false [.tbaa i32],
            .load 1 i32 (.reg 0) 4 false [.range 0 100, .tbaa i32],
            .icmp 2 .ult 32 (.reg 1) (.int 32 100),
            .fact (.reg 2) ],
          .jmp 1⟩,
        ⟨1, [⟨3, i32, [(0, .int 32 0), (2, .reg 11)]⟩, ⟨4, i32, [(0, .int 32 0), (2, .reg 10)]⟩],
          [ .icmp 5 .ult 32 (.reg 3) (.int 32 5) ],
          .br (.reg 5) 2 3⟩,
        ⟨2, [],
          [ .call (some 6) 0 [.reg 3],
            .bin 7 .and 32 (.reg 3) (.int 32 3),
            .cast 8 .zext i32 (.int 64) (.reg 7),
            .gep 9 (.arr 4 i32) (.glob 1) [.int 64 0, .reg 8] true,
            .store i32 (.reg 6) (.reg 9) 4 false [.tbaa i32],
            .bin 10 .add 32 (.reg 4) (.reg 6),
            .armw 12 .add i32 (.glob 0) (.int 32 1) .seqc,
            .bin 11 .add 32 (.reg 3) (.int 32 1) ],
          .jmp 1⟩,
        ⟨3, [],
          [ .aload 13 i32 (.glob 0) .seqc 4,
            .gep 14 (.arr 4 i32) (.glob 1) [.int 64 0, .int 64 3] true,
            .load 15 i32 (.reg 14) 4 false [.tbaa i32],
            .bin 16 .add 32 (.reg 4) (.reg 13),
            .bin 17 .add 32 (.reg 16) (.reg 15) ],
          .ret (some (.reg 17))⟩ ] }

def modl : Modl :=
  { globs := [⟨"cnt", i32⟩, ⟨"tab", .arr 4 i32⟩], funs := [sq, main] }

/-- The memory of the module's globals, all zero. -/
def Modl.init (M : Modl) : Mem :=
  M.globs.foldl (fun m g => (m.alloc g.t.size true).1) Mem.empty

/-- The start configuration: call function `fi` with arguments `vs`, no caller. -/
def start (M : Modl) (fi : Nat) (vs : List Val) : Option Cfg :=
  (Frame.callee M fi vs none).map fun f => .run (Modl.init M) f []

/-- The result a bounded run yields (`none` if it did not finish). -/
def result (M : Modl) (fi : Nat) (vs : List Val) (fuel : Nat) : Option Val :=
  match start M fi vs with
  | none => none
  | some c => match exec M fuel c with
      | .fin _ v => v
      | .run .. => none

/-- **The run of `@main` is computed by the kernel: it returns 44.** -/
theorem main_returns : result modl 1 [] 2000 = some (Val.ofInt 32 44) := by decide

theorem sq_returns : result modl 0 [Val.ofInt 32 12] 20 = some (Val.ofInt 32 144) := by decide

theorem modl_no_asm : modl.NoAsm := by decide

/-- The computed run is a `Reach` of the step relation (not only of the executable `exec`):
    the module, started in `@main`, finishes with 44 under sequential consistency. -/
theorem main_runs :
    ∃ c m, start modl 1 [] = some c ∧ Runs modl Sees.sc c m (some (Val.ofInt 32 44)) := by
  have h : (start modl 1 []).isSome = true := by decide
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have hr := main_returns
  simp only [result, hc] at hr
  cases he : exec modl 2000 c with
  | run m f ks => simp [he] at hr
  | fin m v =>
      simp only [he] at hr
      subst hr
      refine ⟨c, m, hc, ?_⟩
      have := exec_reach modl_no_asm 2000 c
      rw [he] at this
      exact this

/-! ## The printed text -/

theorem sq_prints : Print.func modl sq =
    "define i32 @sq(i32 %t0) {\nl0:\n  %t1 = mul i32 %t0, %t0\n  ret i32 %t1\n}\n" := by decide

set_option maxRecDepth 100000 in
theorem loop_block_prints : Print.block modl i32 (main.blks.getD 1 ⟨0, [], [], .dead⟩) =
    "l1:\n  %t3 = phi i32 [ 0, %l0 ], [ %t11, %l2 ]\n  %t4 = phi i32 [ 0, %l0 ], [ %t10, %l2 ]\n" ++
    "  %t5 = icmp ult i32 %t3, 5\n  br i1 %t5, label %l2, label %l3\n" := by decide

theorem globals_print : Print.globals modl =
    "@cnt = global i32 zeroinitializer\n@tab = global [4 x i32] zeroinitializer\n" := by decide

/-! ## The weak interface is not degenerate -/

/-- A one-function module: an acquire load of the global counter, returned. -/
def wmod : Modl :=
  { globs := [⟨"cnt", i32⟩],
    funs := [{ name := "peek", params := [], ret := i32,
               blks := [⟨0, [], [.aload 0 i32 (.glob 0) .acq 4], .ret (some (.reg 0))⟩] }] }

/-- Two messages at location (block 0, offset 0): the initial 0 and a later 5. -/
def whist : Loc → List (Nachricht Loc Val) := fun _ =>
  [⟨1, Val.ofInt 32 5, Sicht.null⟩, ⟨0, Val.ofInt 32 0, Sicht.null⟩]

def regOf : Cfg → Option Val
  | .run _ f _ => f.regs 0
  | .fin .. => none

def wstart : Cfg := .run (Modl.init wmod) ⟨0, 0, 0, fun _ => none, none⟩ []

/-- **With two messages the weak interface has two different successors at one atomic load**
    (it reads 0 or 5), where the SC interface has exactly one (`step_sc_det`): the weak
    interface really is weaker, and the semantics keeps both. -/
theorem weak_two_successors :
    ∃ c1 c2, Step wmod (Sees.weak whist Sicht.null) wstart c1 ∧
      Step wmod (Sees.weak whist Sicht.null) wstart c2 ∧ regOf c1 ≠ regOf c2 := by
  have hn : Cfg.nextI wmod wstart = some (.aload 0 i32 (.glob 0) .acq 4) := rfl
  have key : ∀ (n : Nachricht Loc Val), n ∈ whist (0, 0) → n.ts ≥ 0 → n.wert.ty = i32 →
      Step wmod (Sees.weak whist Sicht.null) wstart
        (.run (Modl.init wmod) ((⟨0, 0, 1, fun _ => none, none⟩ : Frame).setr 0 n.wert) []) := by
    intro n hm _ hty
    refine ⟨⟨fun _ _ _ _ _ => some n.wert, fun _ _ m => (m, none)⟩, ?_, ?_⟩
    · simp only [Oracle.legal, wstart]
      intro b o v hp hld
      simp only [Opd.ev, Option.some.injEq, Val.ptr.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [Option.some.injEq] at hld
      subst hld
      exact ⟨n, ⟨hm, by simp [Sicht.null]⟩, rfl⟩
    · simp only [step, wstart, Modl.blk, Modl.init, wmod, Opd.ev, hty, alignOk]
      simp
      rfl
  refine ⟨_, _, key ⟨1, Val.ofInt 32 5, Sicht.null⟩ (by simp [whist]) (by omega) rfl,
    key ⟨0, Val.ofInt 32 0, Sicht.null⟩ (by simp [whist]) (by omega) rfl, ?_⟩
  simp [regOf, Frame.setr, Regs.set, Val.ofInt]

end Witness

end Gabbro.Llvm
