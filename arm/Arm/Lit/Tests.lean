/-
  File:      Arm/Lit/Tests.lean
  Subject:   Classic litmus tests as data with expected AArch64 verdicts, written
             BEFORE the memory model exists so they are a real check on it.
  Note:      Test-bench data, not a Sail translation (no Sail line to cite).
             Expectation sources name the herd7 litmus test of the same shape;
             the mapping is FROM KNOWLEDGE, not a measured copy of herd sources.
             Location ids: x = 0, y = 1. Initial memory is 0 everywhere.
-/
import Arm.Basic
import Arm.Mem.Event
import Arm.Lit.Prog
import Arm.Lit.Enumerate

namespace Arm.Lit

/-- One litmus test: the program, the outcome that must be FORBIDDEN, one
    outcome that must be ALLOWED, and where the expectation comes from. -/
structure LitTest where
  name : String
  herd : String
  prog : LitProg
  forbidden : Outcome
  allowedF : Outcome
  note : String
  deriving DecidableEq, Repr

/-- MP: P0 writes x then y; P1 reads y then x. `(1, 0)` is forbidden. -/
def testMP : LitTest :=
  { name := "MP", herd := "MP", prog := { cores := [[.st 0 1 .plain, .st 1 1 .plain], [.ld 0 1 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 1), (1, 1, 0)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (1, 1, 1)], mem := [] },
    note := "Message passing: causality forbids reading the flag but not the data (herd MP, from knowledge)." }

/-- MP+dmb.st: fence on the writer side only; `(1, 0)` stays ALLOWED. -/
def testMPdmbSt : LitTest :=
  { name := "MP+dmb.st", herd := "MP+dmb.st", prog := { cores := [[.st 0 1 .plain, .fence (.dmb .sy .st), .st 1 1 .plain], [.ld 0 1 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 2)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (1, 1, 0)], mem := [] },
    note := "Writer-side DMB ST alone does not restore MP; the reader can still reorder (herd MP+dmb.st, from knowledge)." }

/-- MP+dmb.ld: fence on the reader side only; `(1, 0)` stays ALLOWED. -/
def testMPdmbLd : LitTest :=
  { name := "MP+dmb.ld", herd := "MP+dmb.ld", prog := { cores := [[.st 0 1 .plain, .st 1 1 .plain], [.ld 0 1 .plain, .fence (.dmb .sy .ld), .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 2)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (1, 1, 0)], mem := [] },
    note := "Reader-side DMB LD alone does not restore MP (herd MP+dmb.ld, from knowledge)." }

/-- MP+dmb.st+dmb.ld: both fences; `(1, 0)` is FORBIDDEN again. -/
def testMPdmbFull : LitTest :=
  { name := "MP+dmb.st+dmb.ld", herd := "MP+dmb.st+dmb.ld", prog := { cores := [[.st 0 1 .plain, .fence (.dmb .sy .st), .st 1 1 .plain], [.ld 0 1 .plain, .fence (.dmb .sy .ld), .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 1), (1, 1, 0)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (1, 1, 1)], mem := [] },
    note := "Both fences restore MP on AArch64 (herd MP+dmb.st+dmb.ld, from knowledge)." }

/-- MP+rel+acq: release store and acquire load; `(1, 0)` is FORBIDDEN. -/
def testMPrelAcq : LitTest :=
  { name := "MP+rel+acq", herd := "MP+rel+acq", prog := { cores := [[.st 0 1 .plain, .st 1 1 .release], [.ld 0 1 .acquire, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 1), (1, 1, 0)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (1, 1, 1)], mem := [] },
    note := "STLR/LDAR restores MP without fences (herd MP+rel+acq, from knowledge)." }

/-- SB: each core writes then reads the other's location. `(0, 0)` is ALLOWED. -/
def testSB : LitTest :=
  { name := "SB", herd := "SB", prog := { cores := [[.st 0 1 .plain, .ld 0 1 .plain], [.st 1 1 .plain, .ld 0 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(0, 0, 2)], mem := [] },
    allowedF := { regs := [(0, 0, 0), (1, 0, 0)], mem := [] },
    note := "Store buffering is observable on AArch64; value 2 is never written (herd SB, from knowledge)." }

/-- SB+dmb: DMB SY between write and read on both sides; `(0, 0)` is FORBIDDEN. -/
def testSBdmb : LitTest :=
  { name := "SB+dmb", herd := "SB+dmb", prog := { cores := [[.st 0 1 .plain, .fence (.dmb .sy .all), .ld 0 1 .plain], [.st 1 1 .plain, .fence (.dmb .sy .all), .ld 0 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(0, 0, 0), (1, 0, 0)], mem := [] },
    allowedF := { regs := [(0, 0, 1), (1, 0, 1)], mem := [] },
    note := "DMB SY restores SB on AArch64 (herd SB+dmb, from knowledge)." }

/-- LB: each core reads then writes the other's location. `(1, 1)` is ALLOWED. -/
def testLB : LitTest :=
  { name := "LB", herd := "LB", prog := { cores := [[.ld 0 0 .plain, .st 1 1 .plain], [.ld 0 1 .plain, .st 0 1 .plain]], init := [], final := [] },
    forbidden := { regs := [(0, 0, 2)], mem := [] },
    allowedF := { regs := [(0, 0, 1), (1, 0, 1)], mem := [] },
    note := "Load buffering is observable on AArch64; value 2 is never written (herd LB, from knowledge)." }

/-- LB+data: a data dependency from each load to its store; `(1, 1)` is FORBIDDEN. -/
def testLBdata : LitTest :=
  { name := "LB+data", herd := "LB+datas", prog := { cores := [[.ld 0 0 .plain, .dep .data 0 1, .st 1 1 .plain], [.ld 0 1 .plain, .dep .data 0 1, .st 0 1 .plain]], init := [], final := [] },
    forbidden := { regs := [(0, 0, 1), (1, 0, 1)], mem := [] },
    allowedF := { regs := [(0, 0, 0), (1, 0, 0)], mem := [] },
    note := "Address/data dependencies order LB on AArch64 (herd LB+datas, from knowledge)." }

/-- IRIW: two writers, two readers reading both in opposite orders. Forbidden. -/
def testIRIW : LitTest :=
  { name := "IRIW", herd := "IRIW", prog := { cores := [[.st 0 1 .plain], [.st 1 1 .plain], [.ld 0 0 .plain, .ld 1 1 .plain], [.ld 0 1 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(2, 0, 1), (2, 1, 0), (3, 0, 1), (3, 1, 0)], mem := [] },
    allowedF := { regs := [(2, 0, 1), (2, 1, 1), (3, 0, 1), (3, 1, 1)], mem := [] },
    note := "Independent reads of independent writes: multicopy atomicity forbids it on AArch64 (herd IRIW, from knowledge)." }

/-- 2+2W: crossed writes, each reader sees only one thread's pair. Forbidden. -/
def test2p2W : LitTest :=
  { name := "2+2W", herd := "2+2W", prog := { cores := [[.st 0 1 .plain, .st 1 2 .plain], [.st 1 1 .plain, .st 0 2 .plain], [.ld 0 0 .plain, .ld 1 1 .plain], [.ld 0 1 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(2, 0, 1), (2, 1, 2), (3, 0, 1), (3, 1, 2)], mem := [] },
    allowedF := { regs := [(2, 0, 2), (2, 1, 2), (3, 0, 2), (3, 1, 2)], mem := [] },
    note := "Store atomicity probe: multicopy atomicity forbids it on AArch64 (herd 2+2W, from knowledge)." }

/-- R: three-thread causality; the stale read `(y=1, x=0)` stays ALLOWED. -/
def testR : LitTest :=
  { name := "R", herd := "R", prog := { cores := [[.st 0 1 .plain], [.ld 0 0 .plain, .stReg 1 0 .plain], [.ld 0 1 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(2, 0, 2)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (2, 0, 1), (2, 1, 0)], mem := [] },
    note := "Read-causality without barriers stays allowed on AArch64 (herd R, from knowledge)." }

/-- S: P1 reads P0's write before writing, pinning `co`; P2 must not see `(2, 1)`. -/
def testS : LitTest :=
  { name := "S", herd := "S", prog := { cores := [[.st 0 1 .plain], [.ld 0 0 .plain, .st 0 2 .plain], [.ld 0 0 .plain, .ld 1 0 .plain]], init := [], final := [] },
    forbidden := { regs := [(1, 0, 1), (2, 0, 2), (2, 1, 1)], mem := [] },
    allowedF := { regs := [(1, 0, 1), (2, 0, 1), (2, 1, 2)], mem := [] },
    note := "Write serialisation pinned by P1's read: P2 then respects coherence (herd S, from knowledge)." }

end Arm.Lit

/-
CUTS: only the MP family so far. SB, LB, IRIW, 2+2W, R, S and the coherence
tests CoRR/CoWW/CoRW/CoWR, the suite list, the model-parameterised runner and
the sanity/count examples are NOT yet written.
-/
