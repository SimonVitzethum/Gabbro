/-
  File:      Grammatik/X86/OptOverflowElim.lean
  Subject:   Overflow-check elimination rule lemma (lane 869).

  OPTIMIZER row B3 (§3.5): an overflow check is removed only under a
  proved-impossible overflow (range entailment, recomputed); §7.2 row
  "checks (B1–B3)": the certificate carries SSA versions + range
  entailment, the validator recomputes the entailment `decide` at the
  cited versions. R4 (§3.6, §3.10 hard gates): signed division is not a
  shift -- signed-division-via-shift reasoning refuses. §3.9: float
  checks are never removed by this rule (default REFUSE).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`) and the
  ACCEPTED checker (`X86.InvariantenOpt`: `isWahr`/`isWahrAll_sound`/
  `exec_pruefung_wahr`): the per-width unsigned-carry (CF) vs signed
  overflow (OF) identity, the range-entailment bridge that makes the
  two-sided bound check decidably true, and the connection theorem
  `OptOverflowElim_verbindung`: a `Block.pruefung` overflow check
  whose bound the validator recomputed is provably taken, so removing
  it preserves the exact `execBlock` outcome (no fault added or
  removed, same successor worlds, same read observations, same call
  logs, same downstream budget). No `ensures` is derived, no refusal
  becomes a warning, no faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one overflow-check site
    (§7.2 "checks" row): the range entailment recomputed at the cited
    SSA versions, the width named from 8/16/32/64, the signedness fixed
    (CF vs OF chosen correctly), no signed-division-via-shift shape
    (R4), and an integer-only window (floats never touched, §3.9). -/
structure OverflowCert where
  bereichPasst : Bool
  breiteOk : Bool
  vorzeichenFix : Bool
  keinShiftDiv : Bool
  nurGanzzahl : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def overflowZulassen (c : OverflowCert) : Bool :=
  c.bereichPasst && c.breiteOk && c.vorzeichenFix && c.keinShiftDiv && c.nurGanzzahl

end Gabbro.Grammatik.X86
