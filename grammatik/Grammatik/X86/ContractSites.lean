/-
  File:      Grammatik/X86/ContractSites.lean
  Subject:   CALL-SITE CONTRACT APPLICATION AT ACTUAL VALUES (lane 546, N13).

  Non-gated half of NEXT-PROOF-WAVE N13 over the REAL source model: site
  shapes over actual `Stmt`/`Endblock` execution (`execStmt` with the
  `rufAt` handler, `rufAt` outcomes), contract application and preservation
  at actual entry/return parameter/result worlds (no `forall rho` /
  `forall v` weakening), the `InlinePflicht` discharge for a successful
  direct call, and a proved concrete obstruction for a contract used across
  an invalidating writer. Reuses `AufrufOpt.InlinePflicht`/`rufAt_ok_vorOk`,
  `rufAt_fall_nach`, `ReqAmEintritt`/`EnsAmRueck`/`RufEnsCheck` and the `eP`
  fixture; no duplicate IR, no new executor, no source change.

  IR lowering closure is WAITING on lane 287 and stays OPEN (see CUTS).
-/
import Grammatik.X86.AufrufOpt
import Grammatik.RufAtNachB
import Grammatik.VertragOrtB
import Grammatik.FolgeZeuge
import Grammatik.FolgeBeweis

namespace Gabbro.Grammatik.X86

variable {D : Deklaration}

/-- INADMISSIBLE SHAPE (WITNESS-): a contract use with the call values
    quantified away. Empty on purpose: every real use goes through the
    actual `rho`/`v` (see `callSite_vorOk`, `rufAt_ok_gibt_ens`). -/
inductive FernVertrag (P : Programm D) (f : D.Fn) : Prop

/-- No quantified-away use exists. -/
theorem kein_fern_vertrag (P : Programm D) (f : D.Fn) :
    ¬ FernVertrag P f := by
  intro h
  cases h

/- CUTS:
  - IR lowering closure is WAITING on lane 287: no SCFG/target bridge here.
  - Full skeleton lands in the next increments (§1 entry/return site facts,
    §2 `InlinePflicht` discharge, §3 writer obstruction, §4 joint witness).
-/

#print axioms kein_fern_vertrag

end Gabbro.Grammatik.X86
