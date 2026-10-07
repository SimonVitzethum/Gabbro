/-
  File:      Arm/Lit/Prog.lean
  Subject:   A tiny litmus-test language: per-core instruction lists, initial memory,
             and a final condition on registers and memory.
  Note:      This is test-bench vocabulary, not a translation of Sail semantics;
             there is no Sail source line to cite for the DSL itself. Event shapes
             reuse the FROZEN `Arm.Mem.Event` vocabulary. Expectation sources for
             concrete tests live in `Arm/Lit/Tests.lean` (from knowledge, herd7
             litmus names, not measured copies).
-/
import Arm.Basic
import Arm.Mem.Event

namespace Arm.Lit

/-- Register-to-register dependency flavour carried by a `dep` marker. -/
inductive DepKind where
  | addr | data | ctrl
  deriving DecidableEq, Repr

/-- One litmus instruction. Registers and locations are `Nat` ids; values are `Nat`. -/
inductive LitInstr where
  | ld (dst loc : Nat) (ord : AccOrd)
  | st (loc val : Nat) (ord : AccOrd)
  | stReg (loc src : Nat) (ord : AccOrd)
  | fence (b : Barrier)
  | dep (k : DepKind) (src dst : Nat)
  deriving DecidableEq, Repr

/-- One atomic final-state condition: a register or a memory location holds a value. -/
inductive Atom where
  | regEq (core reg val : Nat)
  | memEq (loc val : Nat)
  deriving DecidableEq, Repr

/-- A litmus program: per-core instructions, initial memory, final condition. -/
structure LitProg where
  cores : List (List LitInstr)
  init : List (Nat × Nat)
  final : List Atom
  deriving DecidableEq, Repr

end Arm.Lit

/-
CUTS: elaboration to events lives in `Arm/Lit/Enumerate.lean`; outcome checking
against candidate executions lives there as well. No theorem yet.
-/
