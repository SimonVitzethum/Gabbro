/-
  File:      Grammatik/X86/TimeTransfer.lean
  Subject:   TARGET-WORK TO SOURCE-TIME TRANSFER SKELETON (lane 547, N17).

  Reuses the accepted cost aggregation (`HardwareAssumptions`: per-form
  named bounds, `laufKosten` and its lemmas) and the accepted summary
  schema (`CostSummary`: `kostenSummeOk`, `expandBound`, `targetWork`,
  `blattSummary`), plus the actual source bound (`KostenG.kostenTiefF`,
  the `ZeitAb` right-hand side `kostenTief` at the use site) and the
  non-degenerate source fixture (`ZielOrtEinfadenZeuge`, via CostSummary).

  Claim: a finite executed target prefix whose every step carries a
  named per-form bound, covered in machine work by an admitted summary
  over a source budget, is covered in target time. Hardware timing
  supplies per-form bounds only; source correspondence and the
  conclusion are proved, never assumed. Full scheduling / IR
  correspondence stays CUT; no constant-time or CAS-progress promise.
-/
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Transfer admission: an admitted summary AND an admitted profile.
    Data and admission are separate so a refused transfer stays statable. -/
def zeitTransferZulaessig (s : CostSummary) (p : HardwareProfil) : Bool :=
  kostenSummeOk s && profilGueltig p

/-- Admission splits into its two halves; both premises are used. -/
theorem zeitTransferZulaessig_braucht_ok (s : CostSummary) (p : HardwareProfil)
    (h : zeitTransferZulaessig s p = true) :
    kostenSummeOk s = true ∧ profilGueltig p = true := by
  unfold zeitTransferZulaessig at h
  simp at h
  exact h

/- CUTS:
    - Skeleton only: transfer core, refusals and the joint witness follow.
    - No source/target scheduling or IR correspondence (`XCorr`); no
      constant-time and no CAS-progress promise.
-/

#print axioms zeitTransferZulaessig_braucht_ok

end Gabbro.Grammatik.X86
