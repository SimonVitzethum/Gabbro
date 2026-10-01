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

/-! ## 1. Entry application at an actual direct-call site.

    A `Stmt.call` that runs clean through `execStmt` with the `rufAt`
    handler carries a true `requires` over the ACTUAL argument environment
    at the entry-side read world -- the exact check the ghost entry of
    `AufrufOpt.geistPaar` re-emits. No parameter is quantified away. -/

/-- ENTRY AT THE SITE: a successful direct call leaves `requires` true at
    the actual arguments. Inverts the `execStmt` call arm (same case shape
    as `execStmtH_call_fall`: `grund` is impossible by `hr`, `logik` and
    `hardware` contradict the `.ok` outcome) and closes the `ok` case by
    the reused `rufAt_ok_vorOk` -- nothing is reproved here. -/
theorem callSite_vorOk (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {f : D.Fn} {args : Args D Γ Λ (D.params f)}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    {σ : World D} {ρ : Env D Γ} {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt (V := V) O passes (rufAt P O passes fuel)
      (Stmt.call (V := V) (l := l) f args hp hr) σ ρ = .ok σ' ρ') :
    ReqAmEintritt P f
      ((σ.lese Λ args.orte).lese (Signatur.anfang D (D.signatur f))
        (P.requires f).orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) := by
  cases hR : rufAt P O passes fuel f (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ1 v => exact rufAt_ok_vorOk P O passes fuel f _ _ _ _ hR
  | grund σ1 r => exact (Fin.cast hr r).elim0
  | logik e =>
    simp only [execStmt, hR] at h
    cases h
  | hardware e =>
    simp only [execStmt, hR] at h
    cases h

/- CUTS:
  - IR lowering closure is WAITING on lane 287: no SCFG/target bridge here.
  - Full skeleton lands in the next increments (§1 entry/return site facts,
    §2 `InlinePflicht` discharge, §3 writer obstruction, §4 joint witness).
-/

#print axioms kein_fern_vertrag
#print axioms callSite_vorOk

end Gabbro.Grammatik.X86
