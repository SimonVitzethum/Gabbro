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

/-! ## 5. Joint witnesses: actual values on a table-writing run.

    `callSite_vorOk_zeuge` instantiates every premise of `callSite_vorOk`
    jointly: the `execStmt` equation for the real `setze` call of `haupt`
    holds by reduction, and the entry contract follows at the actual
    argument environment. `rufAt_ok_gibt_ens_zeuge` does the same for
    `rufAt_ok_gibt_ens` (plus the `InlinePflicht` discharge, the written
    table and the `0 -> 5` memory change). `vertragStandort_lauf_zeuge`
    replays the reached five-step machine run: the writing call, the
    memory change and the entry contract co-occur with the order leg. -/

/-- JOINT WITNESS (entry): the real `setze` call runs clean and its
    `requires` holds at the actual arguments. -/
theorem callSite_vorOk_zeuge :
    ∃ (σ' : World eD) (ρ' : Env eD []) (sargs : World eD)
      (rhoargs : Env eD (eD.params eSetze)),
      sargs = (((eSp.welt []).lese [] []).lese []
        ((.nil : Args eD [] [] (eD.params eSetze)).orte)) ∧
      rhoargs = evalArgs sargs (.nil : Args eD [] [] (eD.params eSetze))
        sargs .nil ∧
      execStmt (V := vertragVon eD eHaupt) eO 0 (rufAt eP eO 0 1)
        (Stmt.call (V := vertragVon eD eHaupt) (l := false) eSetze
          (.nil : Args eD [] [] (eD.params eSetze)) eHpSetze rfl)
        ((eSp.welt []).lese [] []) .nil = .ok σ' ρ' ∧
      ReqAmEintritt eP eSetze
        (sargs.lese (Signatur.anfang eD (eD.signatur eSetze))
          (eP.requires eSetze).orte) rhoargs := by
  have hexec : ∃ σ' ρ', execStmt (V := vertragVon eD eHaupt) eO 0
      (rufAt eP eO 0 1)
      (Stmt.call (V := vertragVon eD eHaupt) (l := false) eSetze
        (.nil : Args eD [] [] (eD.params eSetze)) eHpSetze rfl)
      ((eSp.welt []).lese [] []) .nil = .ok σ' ρ' := ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hexec⟩ := hexec
  exact ⟨σ', ρ', _, _, rfl, rfl, hexec, callSite_vorOk eP eO 0 1 hexec⟩

/-- JOINT WITNESS (return + discharge): every premise of
    `rufAt_ok_gibt_ens` holds jointly on the real `setze` call -- the
    body outcome and the `.ok` outcome both by reduction -- hence the
    `ensures` at the actual result, the written table, the `0 -> 5`
    memory change and the discharged `InlinePflicht`. -/
theorem rufAt_ok_gibt_ens_zeuge :
    ∃ (sread σ1 sret sinv σ' : World eD) (v : ErgVal eD (eD.erg eSetze)),
      sread = ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte)) ∧
      wahr? (eval sread (eP.requires eSetze) sread .nil) = true ∧
      execEnd (V := vertragVon eD eSetze) eO 0 (rufAt eP eO 0 0)
        (eP.rumpf eSetze) sread .nil = EndAusgang.zurueck σ1 v ∧
      sret = σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte ∧
      sinv = (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte) sret ∧
      (eD.invs.find? (fun i => schuldet eSetze i &&
        !wahr? (eval sinv (eP.invariante i) sinv .nil))) = none ∧
      rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
        RufAusgang.ok σ' v ∧
      RufEnsCheck eP eSetze sread sret .nil v ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ((((eSp.welt []).lese [] []).slots () 0 ()).n = 0 ∧
        (sret.slots () 0 ()).n = 5) ∧
      Nonempty (InlinePflicht eP eHaupt eSetze []) := by
  have hread0 : ((((eSp.welt []).lese [] []).lese
      (Signatur.anfang eD (eD.signatur eSetze))
      (eP.requires eSetze).orte)) =
      ((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte := rfl
  have hreq0 : wahr? (eval ((((eSp.welt []).lese [] []).lese
      (Signatur.anfang eD (eD.signatur eSetze))
      (eP.requires eSetze).orte)) (eP.requires eSetze)
      ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte)) .nil) = true := by rfl
  have hschr : (eD.signatur eSetze).schreibt () = true := rfl
  have hsl0 : (((eSp.welt []).lese [] []).slots () 0 ()).n = 0 := rfl
  have hok : ∃ σ1 v σ', execEnd (V := vertragVon eD eSetze) eO 0
        (rufAt eP eO 0 0) (eP.rumpf eSetze)
        ((((eSp.welt []).lese [] []).lese
          (Signatur.anfang eD (eD.signatur eSetze))
          (eP.requires eSetze).orte)) .nil =
        EndAusgang.zurueck σ1 v ∧
      rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
        RufAusgang.ok σ' v := by
    refine ⟨_, _, _, rfl, rfl⟩
  obtain ⟨σ1, v, σ', hbody, hok⟩ := hok
  have hret0 : σ1.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte =
      σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte := rfl
  have hsinv0 : (eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte) =
      (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte) := rfl
  have hinv0 : (eD.invs.find? (fun i => schuldet eSetze i &&
      !wahr? (eval ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte))
        (eP.invariante i)
        ((eD.invs.filter (schuldet eSetze)).foldl
          (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
          (σ1.lese (vertragVon eD eSetze).ende
            (eP.ensures eSetze).orte)) .nil))) = none := by rfl
  have hens := rufAt_ok_gibt_ens eP eO 0 0 eSetze ((eSp.welt []).lese [] [])
    .nil _ hread0 hreq0 _ _ hbody _ hret0 _ hsinv0 hinv0 _ hok
  have hens1 : RufEnsCheck eP eSetze
      ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte))
      (σ1.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte)
      .nil v := hens.1
  have hsl5 : ((σ1.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte).slots () 0 ()).n = 5 :=
    of_decide_eq_true hens1
  have hok_sinv : rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
      RufAusgang.ok ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte)) v := by
    rw [← hens.2]
    exact hok
  have hpfl : Nonempty (InlinePflicht eP eHaupt eSetze []) :=
    ⟨inlinePflicht_aus_rufAt eP eO 0 0 eHaupt eSetze [] eHpSetze rfl
      ((eSp.welt []).lese [] []) .nil _ hread0 hreq0 _ _ hbody _ hret0 _
      hsinv0 hinv0 hok_sinv⟩
  exact ⟨_, σ1, _, _, σ', v, hread0, hreq0, hbody, hret0, hsinv0, hinv0,
    hok, hens1, hschr, ⟨hsl0, hsl5⟩, hpfl⟩

/-- JOINT WITNESS (reached run): on a reached five-step machine run the
    log holds the real ghost pair of `pruefe` over the return of `setze`,
    the entry world carries the write (`0` at the start, `5` at entry),
    the entry contract holds there by the certified leg, and the order
    leg holds -- a table-writing, memory-changing, non-degenerate run. -/
theorem vertragStandort_lauf_zeuge :
    ∃ M : RufMaschineG eD,
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ∃ (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
        (vP : ErgVal eD (eD.erg ePruefe))
        (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
        (aS bS : World eD) (rest : List (RufEreignisF eD)),
        (M.faeden 0).log = RufEreignisF.rueck ePruefe rhoP vP wP bP ::
          RufEreignisF.eintritt ePruefe rhoP wP ::
          RufEreignisF.rueck eSetze rhoS vS aS bS :: rest ∧
        (wP.slots () 0 ()).n = 5 ∧
        ReqAmEintritt eP ePruefe wP rhoP ∧
        FolgeLog Φ50 (M.faeden 0).log := by
  obtain ⟨M, hr, hsl0, hschr, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest,
    hlog, hsl5, hgp, hpf, harm, hfol⟩ := geistRekon_zeuge
  have hm : RufEreignisF.eintritt ePruefe rhoP wP ∈ (M.faeden 0).log := by
    rw [hlog]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hreq : ReqAmEintritt eP ePruefe wP rhoP :=
    ((eP_zertifiziert M hr).1 0 _ hm).1 _ _ _ rfl
  exact ⟨M, hr, hsl0, hschr, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest,
    hlog, hsl5, hreq, hfol⟩

/- CUTS:
  - IR lowering closure is WAITING on lane 287: no SCFG/target bridge here.
    Everything proved is source-side (`execStmt`/`rufAt`/`RufEreignisF`/
    `FolgeLog`); the lowering to the shared representation (QUELLBRUECKE,
    phase B) is the named open dependency.
  - `InlinePflicht.hp`/`hr` are CARRIED into `inlinePflicht_aus_rufAt`
    (the same `RufPasst` and empty-channel proofs the call needed),
    not discharged against the caller's footprint or lock floor.
  - Indirect calls (`callInd`, `bindCallInd`) have no site form here:
    `callSite_vorOk` covers direct `Stmt.call` only.
  - Value-carrying call sites (`Block.bindCall`, whose `execBlock` arm
    keeps the result) are not separately wrapped: the return half is
    proved at the `rufAt` outcome (`rufAt_ok_gibt_ens`), which is what
    both arms consult.
  - The `FernVertrag` refusal is a stated inadmissible shape (empty
    inductive); its force as "quantifying away is false, not weaker"
    comes from `ort_statt_allquantor` on the inhabited mini contract.
  - No executable source-body inline rewrite: there is no function
    splicing a callee body at a call site, hence no body-splice
    simulation against `rufAt` (same cut as `AufrufOpt`).
  - Bounds/depth and budget timing are untouched (decreases/depth
    discipline, cost model are separate obligations).
-/

#print axioms kein_fern_vertrag
#print axioms callSite_vorOk
#print axioms rufAt_ok_gibt_ens
#print axioms inlinePflicht_aus_rufAt
#print axioms vertrag_bricht_nach_schreiber
#print axioms pruefe_requires_falsch_am_start
#print axioms ort_statt_allquantor
#print axioms callSite_vorOk_zeuge
#print axioms rufAt_ok_gibt_ens_zeuge
#print axioms vertragStandort_lauf_zeuge

end Gabbro.Grammatik.X86
