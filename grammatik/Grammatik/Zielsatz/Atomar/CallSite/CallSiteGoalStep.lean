/- C08 R3b: the step of a thread whose head is a top-level foreign binder `let x = g(…); rest`.

   `bindAxiom_ende_schritt` (the twin of `ret_leer_schritt`, RufAdaequatG/T12.lean): every step of
   that thread is the rule `endeBindAxiom`; it keeps the stack, frame function, arguments, entry
   world and log, and leaves the residue `rest` with the answer bound. The call-site witness
   (`CallSiteGoalSites`) follows the heads of a run with it. -/
module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T12

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- At a head `ende (let x = g(…); rest)` every step of the thread binds an answer and runs on
    as `ende rest`. -/
theorem bindAxiom_ende_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → (vertragVon D z.kopf.f).schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → (vertragVon D z.kopf.f).gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest0 : Endblock D (vertragVon D z.kopf.f) l (τ :: Γ) Λ) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiom a args he hw hg hd hgd rest0)⟩) :
    ∃ (w : Wert D τ) (sp : List (Ereignis D)), M'.faeden f =
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, τ :: Γ, Λ, .cons w ρ, .ende rest0⟩⟩,
        sp, z.log⟩ := by
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
    | endeBindAxiom =>
      have hhead := ‹(M.faeden f).kopf.rest = _›
      rw [hR] at hhead
      cases hhead
      exact ⟨_, _, rufUpdateG_self _ _ _⟩
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


end Gabbro.Grammatik
