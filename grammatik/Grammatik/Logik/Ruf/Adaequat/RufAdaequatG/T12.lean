/- Part 12 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T11
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- At an EMPTY stack a head `ende (ret e)` is final for the log: no step
    of `f` changes frame, stack or log (no frame to pop to, no call to make;
    the bare lock steps that fired here were removed on 2026-09-13). -/
theorem ret_leer_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) (hS : z.stapel = []) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hperm)⟩) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt => kopfwegH
    | blatt => kopfwegH
    | ruf => kopfwegH
    | rueck => kopfwegH
    | endeEntf => kopfwegH
    | endeForm _ _ _ _ _ _ hent hhead => (rw [hR] at hhead; cases hhead; exact absurd hent (by simp only [EndEntfaltbar, Bool.false_eq_true, not_false_eq_true]))
    | dannBlatt => kopfwegH
    | dannLeer => kopfwegH
    | dannIteWahr => kopfwegH
    | dannIteFalsch => kopfwegH
    | dannOnOptionSome => kopfwegH
    | dannOnOptionNone => kopfwegH
    | dannOnTagSome => kopfwegH
    | dannOnTagNone => kopfwegH
    | dannOnGrund => kopfwegH
    | endeBind => kopfwegH
    | dannBind => kopfwegH
    | dannNarrowOk | dannNarrowRequired => kopfwegH
    | endeBindAxiom => kopfwegH
  | g2 hs =>
    cases hs with
    | dannNarrowElse => kopfwegH
    | dannPruefWahr => kopfwegH
    | dannPruefFalsch => kopfwegH
    | dannBreaking => kopfwegH
    | dannLocks => kopfwegH
    | freiGib => kopfwegH
    | schrumpfVergiss => kopfwegH
    | dannTrav => kopfwegH
    | travNext => kopfwegH
    | travFort => kopfwegH
    | travDone => kopfwegH
    | dannRetry => kopfwegH
    | wiederUeber => kopfwegH
    | wiederWeiter => kopfwegH
    | wiederSchritt => kopfwegH
    | wiederFort => kopfwegH
    | dannForever => kopfwegH
    | ewigWeiter => kopfwegH
    | ewigFort => kopfwegH
    | rufDann => kopfwegH
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk => kopfwegH
    | dannAxiomCallElseGrund => kopfwegH
    | dannCallInd => kopfwegH
    | rufCallInd => kopfwegH
    | dannBindCall => kopfwegH
    | dannBindCallInd => kopfwegH
    | dannBindCallElse => kopfwegH
    | dannBindCallIndElse => kopfwegH
    | dannCallIndElse => kopfwegH
    | rueckBind => kopfwegH
    | dannLeaveTrav => kopfwegH
    | dannNextTrav => kopfwegH
    | dannLeaveWieder => kopfwegH
    | dannNextWieder => kopfwegH
    | dannLeaveEwig => kopfwegH
  | g4 hs =>
    cases hs with
    | dannNextEwig => kopfwegH
    | peelDannLeave => kopfwegH
    | peelDannNext => kopfwegH
    | peelSchrumpfLeave => kopfwegH
    | peelSchrumpfNext => kopfwegH
    | peelFreiLeave => kopfwegH
    | peelFreiNext => kopfwegH
    | peelAbbruchLeave => kopfwegH
    | peelAbbruchNext => kopfwegH
    | dannRet => kopfwegH
    | rueckCons => kopfwegH
    | dannRetBind => kopfwegH
    | rueckConsBind => kopfwegH
    | rueckGrund => kopfwegH
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt => kopfwegH
    | dannBindAxiomOptElseOk => kopfwegH
    | dannBindAxiomOptElseGrund => kopfwegH
    | dannRegLies => kopfwegH
    | dannRegLiesElseWahr => kopfwegH
    | dannRegLiesElseFalsch => kopfwegH
    | dannAwaits => kopfwegH
    | dannExchange => kopfwegH
    | dannGleit => kopfwegH
    | dannGleitLit => kopfwegH
    | dannGleitVon => kopfwegH
    | dannGleitNarrowOk => kopfwegH
    | dannGleitNarrowElse => kopfwegH
    | dannBindAxiom => kopfwegH
    | dannBindAxiomElseOk => kopfwegH
    | dannBindAxiomElseGrund => kopfwegH
    | rueckConsGrund => kopfwegH
    | dannRetGrund => kopfwegH
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk => kopfwegH
    | endeBindAxiomOptElseGrund => kopfwegH
    | endeBindAxiomElseOk => kopfwegH
    | endeBindAxiomElseGrund => kopfwegH
    | endeGleit => kopfwegH
    | endeGleitLit => kopfwegH
    | endeGleitVon => kopfwegH
    | endeGleitNarrowOk => kopfwegH
    | endeGleitNarrowElse => kopfwegH
  | g7 hs =>
    cases hs with
    | dannVerbrauch => kopfwegH
    | verbrauchWeiter => kopfwegH
    | verbrauchLeer => kopfwegH
    | verbrauchFort => kopfwegH
    | dannLeaveVerbrauch => kopfwegH
    | dannNextVerbrauch => kopfwegH
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> kopfwegH
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> kopfwegH
    | rueckFreigabe => kopfwegH
    | rueckFreigabeLetzte => kopfwegH

theorem ruf_fortsetzung :
    (M7G.faeden 0).kopf = callerFrameG ∧
    callerFrameG.rest = ⟨false, rufDF.params rufCallerF, nach rufDF rufIncF [], rhoCallerF,
      .ende callerRestG⟩ ∧
    (M7G.faeden 0).log = [RufEreignisF.rueck rufIncF rufRhoF vF (M0G.weltVon 0) s1G,
      RufEreignisF.eintritt rufIncF rufRhoF (M0G.weltVon 0),
      RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] ∧
    ∀ M8 : RufMaschineG rufDF, RufSchrittG gP rufOF 0 M7G 0 M8 →
      (M8.faeden 0).log = (M7G.faeden 0).log := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro M8 hs
  obtain ⟨sp, e⟩ := ret_leer_schritt hs _ rfl rfl _ _ _ rfl
  rw [e]

/-! ## CUTS:
  What is proved: TARGET A (`rufG_adaequat`, and `rufG_adaequat_R` for any
  call handler) and TARGET B (`rufG_adaequat_umkehr`) for the covered
  fragment `EndG`/`StmtG`/`BlockG`/`ArmsG`/`GrundArmsG`, each with a joint
  witness on a `locks { if { write } }; return` body; the two former
  FINDINGS against G's step rules, now repaired, as agreement theorems
  (`trav_falsch_steht`, `trav_einig`, `ruf_fortsetzung`). TARGET A (and
  `rufG_adaequat_R`) carry the premise `hnw : caller.wartend = false`
  since the verbatim pops were repaired (2026-09-13): a premise about the
  concrete caller frame (no waiting residue), true for every caller whose
  frame the machine did not push with a bind-call; the witness's caller
  satisfies it by `rfl`. What is NOT proved here:

  - Calls of every form (`call`, `callInd`, `callIndElse`, `bindCall`,
    `bindCallInd`, `bindCallElse`, `bindCallIndElse`): direct calls and
    bind-calls are covered in
    `RufAdaequatRufG.lean` (TARGET 4, any nesting depth), after the repair
    of `ruf`/`rufCallInd` (they pushed the caller frame with its unchanged
    residue, so after `rueck` the caller repeated the call). The indirect
    else forms are not simulated yet.
  - `traverse`: after the repair (`dannTrav` reads nothing, `travNext`/
    `travDone`/`dannLeaveTrav` read exactly where `traverseLauf` does, a
    false read fires no rule) the rules agree with `traverseLauf`
    (`trav_falsch_steht`); the loop is simulated in `RufAdaequatRufG.lean`
    (`travOkR`/`travRetR`, with bounded `retry`: `retryOkR`/`retryRetR`),
    not in this file's fragment.
  - `forever`, `leave`, `next`: the peel rules and the abrupt-exit shims
    are not simulated (no RufRest invariant for `ewigRest`, no abrupt-exit
    simulation). Not a finding; not done. (The former gap "a `sonst` ending
    in `ret` inside a loop body stalls" is closed: `rueck` and `rueckCons`
    now accept any loop level.)
  - `retGrund`, `Endblock.retGrund`, `Endblock.leave`/`next`, and every
    `sonst` branch that does not end in `ret` at loop level `false`
    (machine has no grund rule; `leave`/`next` at `ende` are G's CUTS).
  - `axiomCall`, `bindAxiom`: the oracle may answer with any world, the
    machine step demands a trace that extends the old one without `nimmt`
    (`hneu`/`hkein_nimmt`); a premise on the oracle would close it, none
    is taken.
  - A `ret` under a `locks` body (the `mr = false` flag): `dannRet` pops
    without the `gibt` that `execStmt`'s `locks` appends to the return
    world, so the logged world would differ in the trace. Such a `ret` is
    untypable in a function body (`V.ende` names only entry locks, the
    `locks` rank rule excludes them), so nothing real is lost.
  - TARGET B needs `ohneOrakel` (no `regLies`/`regLiesElse`/`awaits`): the
    machine's bare `nimmt`/`gibt` steps let a thread take and release a
    free lock at any time; that changes only its trace, but those three
    forms hand the whole world, trace included, to the oracle, so a
    trace-reading oracle can then answer differently. TARGET A covers
    them (its run has no bare lock steps). B relates the logged world to
    `execEnd`'s world in MEMORY only (`σ'.speicher = s1'.speicher`), since
    bare lock steps added trace events (they are gone from G since
    2026-09-13; B is kept in its weaker form); A states full equality
    `s1 = σ'`.
  - Only single-thread runs (`RufLaufG` = steps of thread `f`); no
    statement about interleavings with other threads beyond the
    lock-freedom premise of A (`hfrei`, on the locks the body may take).
  - No contract discharge: `requires`/`ensures`/invariants are not checked
    by the machine and not related to `rueck` events here.
-/

#print axioms Gabbro.Grammatik.rufG_adaequat
#print axioms Gabbro.Grammatik.rufG_adaequat_R
#print axioms Gabbro.Grammatik.rufG_adaequat_R_zeuge
#print axioms Gabbro.Grammatik.rufG_adaequat_zeuge
#print axioms Gabbro.Grammatik.rufG_adaequat_umkehr
#print axioms Gabbro.Grammatik.rufG_adaequat_umkehr_zeuge
#print axioms Gabbro.Grammatik.trav_falsch_steht
#print axioms Gabbro.Grammatik.trav_einig
#print axioms Gabbro.Grammatik.ruf_fortsetzung
#print axioms Gabbro.Grammatik.schrittErhalt
#print axioms Gabbro.Grammatik.blockOk
#print axioms Gabbro.Grammatik.endRet


end Gabbro.Grammatik
