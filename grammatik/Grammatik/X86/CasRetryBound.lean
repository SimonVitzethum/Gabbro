/-
  File:      Grammatik/X86/CasRetryBound.lean
  Subject:   Static CAS retry attempt bound derived from contention
    structure, with per-program DIVERGENCE where contention is unknown.

  Lane 784 (hardware completion): one bounded-or-divergent retry discipline
  over the accepted single-attempt steps (`LockedOps.casSchritt`, the
  `LockedInstructionExecution` LOCK CMPXCHG rows). A terminating retry trace
  `fs ++ [true]` whose failures charge against at most `n` distinct foreign
  installers runs at most `n + 1` attempts; the cost summary carrying the
  derived bound names exactly `some (n + 1)`. Unknown contention derives
  `none` (recorded DIVERGENCE, never a free constant) and refuses every
  claimed constant through the accepted refusals. No new interpreter, no new
  decoder, no cycle claim, no source/checker/goal change.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US September 2026):
  - CMPXCHG compare-and-exchange, Vol. 2A 3-194 (txt line 46967): REX.W +
    0F B1/r compares RAX with r/m64; equal sets ZF and loads the source
    into the destination, else clears ZF and loads the destination into
    RAX. With LOCK the instruction executes atomically; the destination
    receives a write cycle regardless of the comparison result.
  - LOCK prefix, Vol. 2A 3-565 (txt line 63495): LOCK may prepend to
    CMPXCHG (among others) with a memory destination; the processor then
    has exclusive use of the shared memory for the instruction duration.
  - What the manual does NOT give: any bound on SOFTWARE retry loops.
    One attempt is atomic; how many attempts a loop needs depends on
    contention, which is a program property carried here as checked data.
-/
import Grammatik.X86.LockedOps
import Grammatik.X86.CostSummary
import Grammatik.X86.BudgetExecution
import Grammatik.X86.LockedInstructionExecution
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-- Contention structure at one CAS retry site, as checked data: either a
    bound on distinct foreign installers overlapping the retry window, or
    unknown. Unknown records per-program DIVERGENCE; it never defaults to
    a constant. -/
inductive Contention where
  | begrenzt (fremd : Nat)
  | unbekannt
  deriving DecidableEq, Repr

/-- Static retry bound derived from contention: `n` distinct foreign
    installers admit at most `n + 1` attempts (each failure charges to a
    distinct installer, the final attempt succeeds); unknown contention is
    `none` = recorded DIVERGENCE, never a free constant. -/
def retryBoundOf : Contention → Option Nat
  | .begrenzt n => some (n + 1)
  | .unbekannt => none

/- CUTS (skeleton; extended with each added theorem):
   - So far only the contention datatype and the derived-bound function.
-/

#print axioms retryBoundOf

end Gabbro.Grammatik.X86
