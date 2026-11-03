module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeBalanceReplayShapes

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

open ScopeBalanceReplay

set_option maxHeartbeats 4000000 in
/-- Dispatch by stack shape. Only the selected head equation is rewritten;
    neither the dependent sigma nor foreign signatures enter global simp. -/
private theorem stepReplay {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M') :
    Step (M.faeden t) (M'.faeden t) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact statementChain s hk
    | endeEntf l Γ Λ Λ' s =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact statementChain s hk
    | endeForm l Γ Λ e =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · exact formChain e
    | ruf l Γ Λ g =>
      simp only [rufUpdateG_self]
      apply enterHeadStep (P := P)
      · assumption
      · intro hk
        exact signatureChain (D.signatur g) hk
    | rueck =>
      simp only [rufUpdateG_self]
      apply popStep
      · assumption
      · exact fun h => h
    | endeBindAxiomOpt l Γ Λ e a =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · exact signatureChain (D.asignatur a)
    | dannBlatt | dannLeer | dannIteWahr | dannIteFalsch
    | dannOnOptionSome | dannOnOptionNone | dannOnTagSome | dannOnTagNone
    | dannOnGrund | endeBind | endeBindAxiom | dannBind | dannNarrowOk =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain, scopeChain_weiterOpt] using hk
  | g2 hs =>
    cases hs with
    | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact branchChain sonst rest _ hk
    | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact branchChain sonst rest _ hk
    | rufDann =>
      simp only [rufUpdateG_self]
      apply enterHeadStep (P := P)
      · assumption
      · exact fun h => h
    | dannPruefWahr | dannBreaking | dannLocks | freiGib | schrumpfVergiss
    | dannTrav | travNext | travFort | travDone | dannRetry | wiederUeber
    | wiederWeiter | wiederSchritt | wiederFort | dannForever | ewigWeiter | ewigFort =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain] using hk
  | g3 hs =>
    cases hs with
    | rufCallInd l Γ Λ n =>
      simp only [rufUpdateG_self]
      apply enterHeadStep (P := P)
      · assumption
      · intro hk
        exact signatureChain (D.sigNr n) hk
    | dannCallInd | dannBindCall | dannBindCallInd | dannBindCallElse
    | dannBindCallIndElse | dannCallIndElse =>
      simp only [rufUpdateG_self]
      apply enterHeadStep (P := P)
      · assumption
      · exact fun h => h
    | rueckBind =>
      simp only [rufUpdateG_self]
      apply waitingStep <;> assumption
    | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact branchChain err rest _ hk
    | dannLeaveTrav | dannNextTrav | dannLeaveWieder | dannNextWieder
    | dannLeaveEwig | dannAxiomCallElseOk =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain] using hk
  | g4 hs =>
    cases hs with
    | dannRet | rueckCons =>
      simp only [rufUpdateG_self]
      apply popStep
      · assumption
      · exact fun h => h
    | dannRetBind | rueckConsBind =>
      simp only [rufUpdateG_self]
      apply waitingStep <;> assumption
    | rueckGrund =>
      simp only [rufUpdateG_self]
      apply reasonStep <;> assumption
    | peelAbbruchLeave | peelAbbruchNext =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact hk.2
    | dannNextEwig | peelDannLeave | peelDannNext | peelSchrumpfLeave | peelSchrumpfNext
    | peelFreiLeave | peelFreiNext =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain] using hk
  | g5 hs =>
    cases hs with
    | rueckConsGrund | dannRetGrund =>
      simp only [rufUpdateG_self]
      apply reasonStep <;> assumption
    | dannRegLiesElseFalsch _ _ l Γ Λ Λ' r hr zusage sonst rest
    | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact branchChain sonst rest _ hk
    | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest
    | dannBindAxiomOptElseGrund _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        exact branchChain err rest _ hk
    | dannRegLies | dannRegLiesElseWahr | dannAwaits | dannExchange
    | dannGleit | dannGleitLit | dannGleitVon | dannGleitNarrowOk
    | dannBindAxiom | dannBindAxiomElseOk | dannBindAxiomOpt | dannBindAxiomOptElseOk =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain, scopeChain_weiterOpt] using hk
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk l Γ Λ e a
    | endeBindAxiomOptElseGrund l Γ Λ e a =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · exact signatureChain (D.asignatur a)
    | endeBindAxiomElseOk | endeBindAxiomElseGrund =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · exact fun h => h
  | g7 hs =>
    cases hs with
    | rueckFreigabeLetzte _ _ _ _ z ha
    | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
    | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
      simp only [rufUpdateG_self]
      exact answerStep ha
    | rueckScopedWert | rueckScopedGrund | rueckFreigabe =>
      simp only [rufUpdateG_self]
      apply localStep
      exact fun _ => trivial
    | dannVerbrauch | verbrauchWeiter | verbrauchLeer | verbrauchFort
    | dannLeaveVerbrauch | dannNextVerbrauch =>
      simp only [rufUpdateG_self]
      apply headStep
      · assumption
      · intro hk
        simpa only [GRest.scopeChain] using hk

/-- G preserves scope provenance separately for each surviving frame. -/
theorem rufSchrittG_scopeMove {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M') :
    ScopeBalanceMove (M.faeden t) (M'.faeden t) :=
  (stepReplay hs).move

/-- Counted scope provenance is preserved by G, independently of memory,
    oracle answers, and the checker's separate rank/floor scope facts. -/
theorem fadenScopeBalanceG_schritt {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M')
    (h : FadenScopeBalanceG (M.faeden t)) : FadenScopeBalanceG (M'.faeden t) :=
  (stepReplay hs).preserves h

/-- The initial residue has no local acquisitions or pending releases. -/
theorem fadenScopeBalanceG_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    FadenScopeBalanceG ((RufStartG P sp init).faeden t) := by
  dsimp only [RufStartG]
  cases init t with
  | mk g rho => exact ⟨GRest.scopeChain_eintritt (P := P) g, by simp⟩

/-- No new acceptance or goal premise: typed frame entry and preservation
    supply balance at every reachable thread. -/
theorem fadenScopeBalanceG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, FadenScopeBalanceG (M.faeden t) := by
  induction hr with
  | start => exact fadenScopeBalanceG_start P sp init
  | schritt N N' u hn hs ih =>
      intro t
      by_cases htu : t = u
      · subst t
        exact fadenScopeBalanceG_schritt hs (ih u)
      · rw [rufSchrittG_passt_anders P O pa N N' u t htu hs]
        exact ih t

end Gabbro.Grammatik
