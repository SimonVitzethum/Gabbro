/-
  File:      Grammatik/X86/OptCallArgSel.lean
  Subject:   Call-argument selection rule lemma (lane 894).

  DESIGN section 7 row (layout/allocation, plus §2 line "call arguments use
  the ABI registers before stack slots"): the lowering places the first
  `regBudget` (6) integer arguments in ABI registers and the rest in
  8-aligned stack slots, under the per-image calling convention the
  validator re-decided from the image (never trusted from Rust).

  Certificate (local rewrite record + recomputed analysis citations):
  `CallArgCert` (four decided Bools) plus the computed `platziere` list;
  the validator rechecks admission (`callArgZulassen`), the arity bound
  (`platzOk`) and the recomputed per-site placement. Failure case (must
  NOT fire): unchecked convention, over-budget arity, hidden/variadic
  parameters, or misaligned stack slots -- each proved to force `false`.
  Phase L, cost O(args).

  Proved over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`): value preservation at
  arbitrary types, regs-before-stack shape, IEEE outcome stability
  (`gleitPasst` over preserved values), bounded cost, no new fault, and
  the source call-outcome connection (`execStmt` `.call` equality under
  equal `orte`/`evalArgs`, so contracts at their place, call logs,
  concurrency and budget observations agree downstream). No `ensures`
  is derived, no refusal becomes a warning, no faulting form is
  speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one call-argument selection
    site (DESIGN section 7 row): the per-image calling convention was
    re-decided from the image, the arity fits the register budget plus
    the stack window, no hidden/variadic parameter is present, and the
    stack slots are 8-aligned with the 16-aligned entry preserved. -/
structure CallArgCert where
  konventionGeprueft : Bool
  registerBudgetOk : Bool
  keineVersteckten : Bool
  stapelBuendig : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def callArgZulassen (c : CallArgCert) : Bool :=
  c.konventionGeprueft && c.registerBudgetOk && c.keineVersteckten && c.stapelBuendig

/-- One lowered argument location: an ABI register or a stack slot at a
    byte offset. -/
inductive ArgPlatz where
  | reg (r : Nat)
  | stapel (off : Nat)
  deriving DecidableEq, Repr

/-- Number of integer arguments carried in ABI registers (System-V-like
    six: rdi rsi rdx rcx r8 r9); the rest goes on the stack. -/
def regBudget : Nat := 6

/-- Maximum admitted argument count (register window plus stack window);
    anything above is refused, never truncated. -/
def maxArgs : Nat := 64

/- CUTS:
  - Placement model (`platzFuer`, `platziere`, `liesWerte`), value/fault/
    IEEE preservation, cost bound, regs-first/stack-aligned shape, the
    `OptCallArgSel_verbindung` rule lemma with its joint `_zeuge`
    witness on a table-writing program with a memory-changing reached
    run, and the exact refusal case are added next, one piece at a time.
  - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
    correspondence stops at preserved source values and `gleitPasst`
    outcomes over the canonical vocabulary.
-/

#print axioms callArgZulassen

end Gabbro.Grammatik.X86
