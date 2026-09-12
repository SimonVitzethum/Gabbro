/-
  Audit 26, finding F1 -- Erhaltung.lean: `kosten_produktion_frei` (line 729)
  claims NOTHING: its conclusion `costKept k` is definitionally
  `k.carrier = .cerCo -> ...`, so under `hc : carrier = .produktion` it
  holds vacuously. The header says "claims NOTHING". This demo shows the
  vacuity is total: production costKept holds even with DIVERGING counts,
  while the CerCo twin with the same counts FAILS.
-/
import Grammatik.Erhaltung

open Gabbro.Grammatik

/-- F1: production `costKept` holds with diverging counts (vacuous). -/
example : costKept ⟨.produktion, 4, 9⟩ := by decide

/-- F1 mirror: the same diverging counts on the CerCo carrier FAIL. -/
example : ¬ costKept ⟨.cerCo, 4, 9⟩ := by decide

/-- F1 core: `kosten_produktion_frei` never looks at the counts. -/
theorem audit26_kosten_produktion_frei_vacuous (k : CostClaim)
    (hc : k.carrier = .produktion) : costKept k :=
  kosten_produktion_frei k hc

#print axioms audit26_kosten_produktion_frei_vacuous

/-
CUTS:
  (C1) No claim beyond the vacuity itself; the question whether `costKept`
       SHOULD be carrier-conditional lives with the contract, not here.
-/
