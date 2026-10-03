/-
  File:      Grammatik/X86/OptLicmLoop.lean
  Subject:   Loop-invariant code motion (LICM) rule lemma (lane 872).

  DESIGN section 7 row: local premise "invariance recomputed (exact-value,
  not rounded-value), non-faulting over hoisted inputs from rechecked source
  facts", certificate "B+C", failure case "hoist `x/n` above `n!=0`; hoist
  token op on shared access on local evidence", phase M, cost O(sites).

  Covered fragment (no accepted IR yet): `Stmt.assignVar` motion across a
  `Stmt.ite` guard over the real `Syntax`/`Semantik` (`eval`/`execBlock`).
  The hoisted temp is env-only (no world write); reads are identical up to
  order (`licmOrte_gleich`); the taken path agrees fully. Cost (CostSummary:
  same statements on the taken path, no wait hidden), layout (TableLayout:
  no carrier touched) and duties follow from the exec equality.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Hoisted operation kinds. `tokenO` (shared/atomic/call/token op) is
    refused BY KIND: a token op is never pure, never speculation-safe. -/
inductive LicmOp where
  | addO | subO | mulO | divO | gleitO (op : GleitOp) | tokenO
  deriving DecidableEq, Repr

/-- Kind admission: token ops never hoist. -/
def licmOpOk : LicmOp → Bool
  | .tokenO => false
  | _ => true

/-- A pure read of an empty footprint leaves the world unchanged. -/
theorem licmLeseLeer {D : Deklaration} (σ : World D) (Λ : List (Res D)) :
    σ.lese Λ ([] : List (D.Tab ⊕ D.Glob)) = σ := rfl

/- CUTS:
    - Skeleton only: certificate, refusals, value lemmas, connection and
      witness follow in small pieces.
-/

#print axioms licmOpOk
#print axioms licmLeseLeer

end Gabbro.Grammatik.X86
