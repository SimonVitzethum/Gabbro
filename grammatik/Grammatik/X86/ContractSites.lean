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

/-! ## 2. Return application at the actual values.

    The matching `ensures` half, which `AufrufOpt` leaves OPEN
    (`InlinePflicht.nachOk` is stated, only `vorOk` derived): a `.ok`
    outcome of `rufAt` at depth `fuel + 1` carries a true `ensures` over
    the ACTUAL result between the entry-side and return-side read worlds,
    and the returned world is the invariant-read world. Derived -- never
    assumed -- through the shared unfolding `rufAt_fall_nach`. -/

/-- RETURN AT THE SITE: a successful call leaves `ensures` true at the
    actual result. From the `rufAt` equation (`hfall`) the outcome is the
    ensures `if` over the actual `v`; the `.logik` branch contradicts the
    `.ok` equation, the `.ok` branch fixes both the check and the world. -/
theorem rufAt_ok_gibt_ens (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (sread : World D)
    (hread : sread = σ.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte)
    (hreq : wahr? (eval sread (P.requires f) sread ρ) = true)
    (σ1 : World D) (v : ErgVal D (D.erg f))
    (hbody : execEnd (V := vertragVon D f) O passes (rufAt P O passes fuel)
      (P.rumpf f) sread ρ = EndAusgang.zurueck σ1 v)
    (sret : World D)
    (hret : sret = σ1.lese (vertragVon D f).ende (P.ensures f).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet f)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet f i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none)
    (σ' : World D)
    (h : rufAt P O passes (fuel + 1) f σ ρ =
      RufAusgang.ok (D := D) (f := f) σ' v) :
    RufEnsCheck P f sread sret ρ v ∧ σ' = sinv := by
  have hfall := rufAt_fall_nach P O passes fuel f σ ρ sread hread hreq
    σ1 v hbody sret hret sinv hsinv hinv
  rw [hfall] at h
  by_cases hc : wahr? (eval sread (P.ensures f) sret
      (ergEnv (D.erg f) v ρ)) = false
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    cases h
    refine ⟨?_, rfl⟩
    show wahr? (eval sread (P.ensures f) sret
      (ergEnv (D.erg f) v ρ)) = true
    cases heq : wahr? (eval sread (P.ensures f) sret
        (ergEnv (D.erg f) v ρ)) with
    | true => rfl
    | false => exact absurd heq hc

/-! ## 3. The inline obligation discharged at a successful call.

    `AufrufOpt.InlinePflicht` carries `hp`/`hr` and states `vorOk`/`nachOk`
    as fields. Here every field is DERIVED from one successful `rufAt`
    outcome at depth `fuel + 1`: `vorOk` is the `hreq` gate, `nachOk` the
    derived `RufEnsCheck` (§2) at the body-return world `σ1` (whose
    ensures-read is exactly `sret`, so no trace-frame lemma is needed). -/

/-- DISCHARGE: one successful call yields the full inline obligation with
    the actual `rho`/worlds/result -- the duty the ghost pair re-emits. -/
def inlinePflicht_aus_rufAt (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (caller g : D.Fn) (Λ : List (Res D))
    (hp : RufPasst D (vertragVon D caller) (D.signatur g) Λ)
    (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D (D.params g))
    (sread : World D)
    (hread : sread = σ.lese (Signatur.anfang D (D.signatur g))
      (P.requires g).orte)
    (hreq : wahr? (eval sread (P.requires g) sread ρ) = true)
    (σ1 : World D) (v : ErgVal D (D.erg g))
    (hbody : execEnd (V := vertragVon D g) O passes (rufAt P O passes fuel)
      (P.rumpf g) sread ρ = EndAusgang.zurueck σ1 v)
    (sret : World D)
    (hret : sret = σ1.lese (vertragVon D g).ende (P.ensures g).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet g)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet g i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none)
    (h : rufAt P O passes (fuel + 1) g σ ρ =
      RufAusgang.ok (D := D) (f := g) sinv v) :
    InlinePflicht P caller g Λ := by
  have hens := (rufAt_ok_gibt_ens P O passes fuel g σ ρ sread hread hreq
    σ1 v hbody sret hret sinv hsinv hinv sinv h).1
  refine ⟨hp, hr, ρ, σ, σ1, v, ?_, ?_⟩
  · rw [← hread]
    exact hreq
  · unfold RufEnsCheck at hens
    rw [← hread, ← hret]
    exact hens

/-! ## 4. Obstruction: a contract used across an invalidating writer.

    On the `eP` fixture `pruefe` requires `konto[0] == 5`. Any world whose
    slot still reads `0` -- the start world, or any world a writer reset --
    refuses the entry contract: the contract does NOT survive the writer.
    The second half ties the inadmissible shape of §0 to an inhabited
    contract: at their place the checks hold (`mini_ens_am_ort`), while the
    quantified-away `ensures` is false (`mini_qensures_falsch`). -/

/-- A writer that leaves `konto[0]` at `0` invalidates `pruefe`'s entry
    contract: from the required slot value (`of_decide_eq_true`, the same
    extraction `geistRekon_zeuge` uses) against the actual one. -/
theorem vertrag_bricht_nach_schreiber (σ : World eD)
    (hslot : (σ.slots () 0 ()).n = 0) :
    ¬ ReqAmEintritt eP ePruefe σ .nil := by
  intro hreq
  have h5 : (σ.slots () 0 ()).n = 5 := of_decide_eq_true hreq
  omega

/-- At the start world (which left `konto[0]` at `0`) the entry contract
    is already refused -- no call has established anything yet. -/
theorem pruefe_requires_falsch_am_start :
    ¬ ReqAmEintritt eP ePruefe (eSp.welt []) .nil :=
  vertrag_bricht_nach_schreiber _ rfl

/-- PLACE HOLDS, QUANTIFIED FAILS, on one inhabited contract: the return
    check at its actual values (`mini_ens_am_ort`) with the quantified
    `ensures` false on the same contract (`mini_qensures_falsch`). Hence a
    use that quantifies the values away is not a weakening -- it is false. -/
theorem ort_statt_allquantor :
    EnsAmRueck miniContrP fTrue miniWelt miniWelt miniRho miniV ∧
      ¬ QEnsuresB miniContrP fTrue miniWelt :=
  ⟨mini_ens_am_ort, mini_qensures_falsch⟩

/- CUTS:
  - IR lowering closure is WAITING on lane 287: no SCFG/target bridge here.
  - Full skeleton lands in the next increments (§1 entry/return site facts,
    §2 `InlinePflicht` discharge, §3 writer obstruction, §4 joint witness).
-/

#print axioms kein_fern_vertrag
#print axioms callSite_vorOk
#print axioms rufAt_ok_gibt_ens
#print axioms inlinePflicht_aus_rufAt
#print axioms vertrag_bricht_nach_schreiber
#print axioms pruefe_requires_falsch_am_start
#print axioms ort_statt_allquantor

end Gabbro.Grammatik.X86
