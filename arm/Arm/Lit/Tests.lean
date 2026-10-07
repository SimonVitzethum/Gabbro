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

end Arm.Lit

/-
CUTS: only the MP family so far. SB, LB, IRIW, 2+2W, R, S and the coherence
tests CoRR/CoWW/CoRW/CoWR, the suite list, the model-parameterised runner and
the sanity/count examples are NOT yet written.
-/
