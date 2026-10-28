import Grammatik.Code.Model.Facts
import Grammatik.Code.Model.Weak

/-
  File:      Grammatik/Code/Model/Witness.lean
  Subject:   TRACK L -- A NON-DEGENERATE WITNESS of `Code`, run at TWO target configurations.

  One module, two functions and two globals, built for a word width `W` and run at `W = 64`
  (little endian) and `W = 32` (big endian), so the parameters `Conf` are exercised:
    * `@sq`   -- a leaf that squares its argument;
    * `@main` -- an `alloc` cell with a load and a `fact`, a LOOP with two phis (i = 0 .. 4), a
      CALL of `@sq` per round, a `gep` into a global array and a store through it, an atomic
      `armw` on a global word counter, and after the loop an atomic load of the counter, a plain
      load through `gep`, and the result `sum + count + tab[3]`.
  The run is computed by the kernel (`decide`): the squares 0..4 sum to 30, the counter is 5,
  `tab[3]` is 9, so `@main` returns 44 -- at both configurations. The weak-memory interface is
  shown NON-DEGENERATE: with two messages at a location the step relation has two different
  successors at an atomic load (`weak_two_successors`), where the SC interface has exactly one.
-/

namespace Gabbro.Code

open Gabbro.Grammatik.Speichermodell

namespace Witness

/-- The word-sized integer type. -/
def iw (W : Nat) : Ty := .int W

def sq (W : Nat) : Func :=
  { name := "sq", params := [⟨iw W, 0⟩], ret := iw W,
    blks := [⟨0, [], [.bin 1 .mul W (.reg 0) (.reg 0)], .ret (some (.reg 1))⟩] }

def main (W : Nat) : Func :=
  { name := "main", params := [], ret := iw W,
    blks :=
      [ ⟨0, [],
          [ .alloc 0 (iw W),
            .store (iw W) (.int W 7) (.reg 0),
            .load 1 (iw W) (.reg 0),
            .icmp 2 .ult W (.reg 1) (.int W 100),
            .fact (.reg 2) ],
          .jmp 1⟩,
        ⟨1, [⟨3, iw W, [(0, .int W 0), (2, .reg 11)]⟩, ⟨4, iw W, [(0, .int W 0), (2, .reg 10)]⟩],
          [],
          .brc .ult W (.reg 3) (.int W 5) 2 3⟩,
        ⟨2, [],
          [ .call (some 6) 0 [.reg 3],
            .bin 7 .and W (.reg 3) (.int W 3),
            .gep 9 (.arr 4 (iw W)) (.glob 1) [.int W 0, .reg 7] true,
            .store (iw W) (.reg 6) (.reg 9),
            .bin 10 .add W (.reg 4) (.reg 6),
            .armw 12 .add (iw W) (.glob 0) (.int W 1) .seqc,
            .bin 11 .add W (.reg 3) (.int W 1) ],
          .jmp 1⟩,
        ⟨3, [],
          [ .aload 13 (iw W) (.glob 0) .seqc,
            .gep 14 (.arr 4 (iw W)) (.glob 1) [.int W 0, .int W 3] true,
            .load 15 (iw W) (.reg 14),
            .bin 16 .add W (.reg 4) (.reg 13),
            .bin 17 .add W (.reg 16) (.reg 15) ],
          .ret (some (.reg 17))⟩ ] }

def modl (W : Nat) : Modl :=
  { globs := [⟨"cnt", iw W⟩, ⟨"tab", .arr 4 (iw W)⟩], funs := [sq W, main W] }

/-- The memory of the module's globals, all zero. -/
def Modl.init [Conf] (M : Modl) : Mem :=
  M.globs.foldl (fun m g => (m.alloc g.t.size true).1) Mem.empty

/-- The start configuration: call function `fi` with arguments `vs`, no caller. -/
def start [Conf] (M : Modl) (fi : Nat) (vs : List Val) : Option Cfg :=
  (Frame.callee M fi vs none).map fun f => .run (Modl.init M) f []

/-- The result a bounded run yields (`none` if it did not finish). -/
def result [Conf] (M : Modl) (fi : Nat) (vs : List Val) (fuel : Nat) : Option Val :=
  match start M fi vs with
  | none => none
  | some c => match exec M fuel c with
      | .fin _ v => v
      | .run .. => none

/-- A 64-bit little-endian target. -/
@[reducible] def c64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- A 32-bit big-endian target. -/
@[reducible] def c32 : Conf := ⟨32, true, Or.inl rfl⟩

section W64
attribute [local instance] c64

/-- **`@main` returns 44 at 64 bits, little endian** (computed by the kernel). -/
theorem main64_returns : result (modl 64) 1 [] 2000 = some (Val.ofInt 64 44) := by decide +kernel

theorem sq64_returns : result (modl 64) 0 [Val.ofInt 64 12] 20 = some (Val.ofInt 64 144) := by decide +kernel

/-- The computed run is a `Reach` of the step relation (not only of the executable `exec`). -/
theorem main64_runs :
    ∃ c m, start (modl 64) 1 [] = some c ∧ Runs (modl 64) Sees.sc c m (some (Val.ofInt 64 44)) := by
  have h : (start (modl 64) 1 []).isSome = true := by decide +kernel
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have hr := main64_returns
  simp only [result, hc] at hr
  cases he : exec (modl 64) 2000 c with
  | run m f ks => simp only [he, reduceCtorEq] at hr
  | fin m v =>
      simp only [he] at hr
      subst hr
      refine ⟨c, m, hc, ?_⟩
      have := exec_reach (M := modl 64) 2000 c
      rw [he] at this
      exact this

/-! ### The weak interface is not degenerate -/

/-- A one-function module: an acquire load of the global counter, returned. -/
def wmod : Modl :=
  { globs := [⟨"cnt", iw 64⟩],
    funs := [{ name := "peek", params := [], ret := iw 64,
               blks := [⟨0, [], [.aload 0 (iw 64) (.glob 0) .acq], .ret (some (.reg 0))⟩] }] }

/-- Two messages at location (block 0, offset 0): the initial 0 and a later 5. -/
def whist : Loc → List (Nachricht Loc Val) := fun _ =>
  [⟨1, Val.ofInt 64 5, Sicht.null⟩, ⟨0, Val.ofInt 64 0, Sicht.null⟩]

def regOf : Cfg → Option Val
  | .run _ f _ => f.regs 0
  | .fin .. => none

def wstart : Cfg := .run (Modl.init wmod) ⟨0, 0, 0, fun _ => none, none⟩ []

/-- **With two messages the weak interface has two different successors at one atomic load**
    (it reads 0 or 5), where the SC interface has exactly one (`step_sc_det`). -/
theorem weak_two_successors :
    ∃ c1 c2, Step wmod (Sees.weak whist Sicht.null) wstart c1 ∧
      Step wmod (Sees.weak whist Sicht.null) wstart c2 ∧ regOf c1 ≠ regOf c2 := by
  have key : ∀ (n : Nachricht Loc Val), n ∈ whist (0, 0) → n.wert.ty = iw 64 →
      Step wmod (Sees.weak whist Sicht.null) wstart
        (.run (Modl.init wmod) ((⟨0, 0, 1, fun _ => none, none⟩ : Frame).setr 0 n.wert) []) := by
    intro n hm hty
    refine ⟨⟨fun _ _ _ _ _ => some n.wert⟩, ?_, ?_⟩
    · have hn : Cfg.nextI wmod wstart = some (.aload 0 (iw 64) (.glob 0) .acq) := rfl
      simp only [Oracle.legal, hn]
      intro b o v hp hld
      simp only [Opd.ev, Option.some.injEq, Val.ptr.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [Option.some.injEq] at hld
      subst hld
      exact ⟨n, ⟨hm, by simp only [Sicht.null, Nat.zero_le]⟩, rfl⟩
    · simp only [step, wstart, Modl.blk, Modl.init, wmod, Opd.ev, hty, atomicOk]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.bind_some, BEq.rfl, List.find?_cons_of_pos, decide_eq_true_eq, List.foldl_cons,
  List.foldl_nil, ↓reduceIte, Option.ite_none_right_eq_some, Option.some.injEq, Cfg.run.injEq, and_true, true_and]
      exact ⟨⟨by decide +kernel, by decide +kernel⟩, rfl⟩
  refine ⟨_, _, key ⟨1, Val.ofInt 64 5, Sicht.null⟩ (by simp only [whist, List.mem_cons, Nachricht.mk.injEq, Nat.succ_ne_self, and_true, false_and, List.not_mem_nil,
  or_self, or_false]) rfl,
    key ⟨0, Val.ofInt 64 0, Sicht.null⟩ (by simp only [whist, List.mem_cons, Nachricht.mk.injEq, Nat.zero_ne_one, and_true, false_and, List.not_mem_nil,
  or_false, or_true]) rfl, ?_⟩
  simp only [regOf, Frame.setr, Val.ofInt, BitVec.ofInt_ofNat, Regs.set, ↓reduceIte, ne_eq, Option.some.injEq,
  Val.int.injEq, heq_eq_eq, BitVec.reduceEq, and_false, not_false_eq_true]

end W64

section W32
attribute [local instance] c32

/-- **The same module at 32 bits, big endian, returns the same 44.** -/
theorem main32_returns : result (modl 32) 1 [] 2000 = some (Val.ofInt 32 44) := by decide +kernel

end W32

end Witness

end Gabbro.Code
