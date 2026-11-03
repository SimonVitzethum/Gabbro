module

public import Grammatik.Logik.Fortschritt.Fortschritt.T1
public import Grammatik.Logik.Fortschritt.Fortschritt.T2.Teil1
public import Grammatik.Logik.Fortschritt.Fortschritt.T2.ScopeReplay
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T5.AntwortPosition

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Fort
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A `dann` head**: every block form fires, waits for a lock, or stops
    at its hardware answer; `leave`/`next` find an absorbing continuation
    (`fOk`). An empty answer type stops the head only at an axiom `-> never`
    (`nieZurueck`): the head's answer sites are admissible (`hAnt`, from the
    checker's `antworten` through `kopf_ants`; round-6 finding W1). -/
theorem fort_dann (hO : GutO O) {w0 : D.Fn} {M : RufMaschineG D} {t : Faden}
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) (hP : PrueftG O passes M t)
    (hB : BereichG M t)
    (hR : RangInvG w0 (M.faeden t))
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ')
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩) (hnimmt : k.nimmtAb = true)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur)) (hAnt : b.ants.all (stelleC D) = true)
    (hScope : b.scopesOk (vertragVon D (M.faeden t).kopf.f).haelt
      (vertragVon D (M.faeden t).kopf.f).boden = true) :
    FortFaden P O passes M t := by
  cases b with
  | nil => exact fort_schritt (w_dannLeer rfl k ρ hx)
  | bind e rest => exact fort_schritt (w_dannBind rfl e rest k ρ hx hΛ)
  | bindCall g args he hp hr rest => exact fort_schritt (w_bindCall rfl g args he hp hr rest k ρ hx hΛ)
  | bindCallInd p args he hp hr rest =>
      obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
      exact fort_schritt' ⟨_, RufSchrittG.dannBindCallInd M t l Γ Λ _ Λ _ _ p args he hp hr rest k
        ρ hx hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
          ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
  | bindCallIndElse p args he hp hr err rest =>
      obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
      exact fort_schritt' ⟨_, RufSchrittG.dannBindCallIndElse M t l Γ Λ _ Λ _ _ p args he hp hr err rest k
        ρ hx hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
          ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
  | bindCallElse g args he hp hr err rest =>
      exact fort_schritt (w_bindCallElse rfl g args he hp hr err rest k ρ hx hΛ)
  | bindAxiom a args he hw hg hd hgd rest =>
      rcases hax : axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v⟩
      · by_cases hleer : AntwortLeer D (D.aerg a)
        · -- the checker admits an empty answer type at an axiom only for `-> never` (W1)
          simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
          exact fort_nie ⟨l, Γ, Λ, ρ, _, hx,
            (stelleC_iff.mp hAnt.1).resolve_right fun h => h hleer⟩
        refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, ?_, hleer⟩
        show (axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ)).2
            = none
        rw [hax]
      · have hσ : (O.wirkt a (((M.weltVon t).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte)
              ρ)).1 = σ₂ := by
          have := congrArg Prod.fst hax
          simpa [axiomAntwort] using this
        have hh : HeldIn Λ ((M.weltVon t).lese Λ args.orte).haelt := by
          show HeldIn Λ (offen _)
          rw [(Erw.lese (M.weltVon t) Λ args.orte).offen]
          exact hΛ
        have herw := ((Erw.lese (M.weltVon t) Λ args.orte).trans (Erw.fragt _ (.inl a))).trans
          (axiom_erw hO a _ (evalArgs ((M.weltVon t).lese Λ args.orte) args
            ((M.weltVon t).lese Λ args.orte) ρ) hd hgd hh)
        rw [hσ] at herw
        obtain ⟨neu, hneu, -⟩ := herw
        exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiom M t l Γ Λ _ _ a args he hw hg hd hgd rest
          k ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      rcases hax : axiomAntwortSonst O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v | r⟩
      · refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, ?_⟩
        show (axiomAntwortSonst O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ)).2
            = none
        rw [hax]
      all_goals
        have hσ : (O.wirkt a (((M.weltVon t).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte)
              ρ)).1 = σ₂ := by
          have := congrArg Prod.fst hax
          simpa [axiomAntwortSonst] using this
        have hh : HeldIn Λ ((M.weltVon t).lese Λ args.orte).haelt := by
          show HeldIn Λ (offen _)
          rw [(Erw.lese (M.weltVon t) Λ args.orte).offen]
          exact hΛ
        have herw := ((Erw.lese (M.weltVon t) Λ args.orte).trans (Erw.fragt _ (.inl a))).trans
          (axiom_erw hO a _ (evalArgs ((M.weltVon t).lese Λ args.orte) args
            ((M.weltVon t).lese Λ args.orte) ρ) hd hgd hh)
        rw [hσ] at herw
        obtain ⟨neu, hneu, -⟩ := herw
      · exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiomElseOk M t l Γ Λ _ _ a args he hr hw hg hd hgd err rest
          k ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
      · exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiomElseGrund M t l Γ Λ _ _ a args he hr hw hg hd hgd err rest
          k ρ hx _ rfl σ₂ r hax neu hneu hΛ⟩
  | bindAxiomOpt e a args he hp hd hgd rest =>
      rcases hax : axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v⟩
      · by_cases hleer : AntwortLeer D (D.aerg a)
        · simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
          exact fort_nie ⟨l, Γ, Λ, ρ, _, hx,
            (stelleC_iff.mp hAnt.1).resolve_right fun h => h hleer⟩
        refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, ?_, hleer⟩
        show (axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ)).2
            = none
        rw [hax]
      · have hσ : (O.wirkt a (((M.weltVon t).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte)
              ρ)).1 = σ₂ := by
          have := congrArg Prod.fst hax
          simpa [axiomAntwort] using this
        have hh : HeldIn Λ ((M.weltVon t).lese Λ args.orte).haelt := by
          show HeldIn Λ (offen _)
          rw [(Erw.lese (M.weltVon t) Λ args.orte).offen]
          exact hΛ
        have herw := ((Erw.lese (M.weltVon t) Λ args.orte).trans (Erw.fragt _ (.inl a))).trans
          (axiom_erw hO a _ (evalArgs ((M.weltVon t).lese Λ args.orte) args
            ((M.weltVon t).lese Λ args.orte) ρ) hd hgd hh)
        rw [hσ] at herw
        obtain ⟨neu, hneu, -⟩ := herw
        exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiomOpt M t l Γ Λ _ _ e a args he hp hd hgd rest
          k ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
  | bindAxiomOptElse e a args he hp hd hgd hr err rest =>
      rcases hax : axiomAntwortSonst O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v | r⟩
      · refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, ?_⟩
        show (axiomAntwortSonst O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ)).2
            = none
        rw [hax]
      all_goals
        have hσ : (O.wirkt a (((M.weltVon t).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte)
              ρ)).1 = σ₂ := by
          have := congrArg Prod.fst hax
          simpa [axiomAntwortSonst] using this
        have hh : HeldIn Λ ((M.weltVon t).lese Λ args.orte).haelt := by
          show HeldIn Λ (offen _)
          rw [(Erw.lese (M.weltVon t) Λ args.orte).offen]
          exact hΛ
        have herw := ((Erw.lese (M.weltVon t) Λ args.orte).trans (Erw.fragt _ (.inl a))).trans
          (axiom_erw hO a _ (evalArgs ((M.weltVon t).lese Λ args.orte) args
            ((M.weltVon t).lese Λ args.orte) ρ) hd hgd hh)
        rw [hσ] at herw
        obtain ⟨neu, hneu, -⟩ := herw
      · exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiomOptElseOk M t l Γ Λ _ _ e a args he hr hp hd hgd err rest
          k ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
      · exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiomOptElseGrund M t l Γ Λ _ _ e a args he hr hp hd hgd err rest
          k ρ hx _ rfl σ₂ r hax neu hneu hΛ⟩
  | regRead r hk rest =>
      by_cases hex : ∃ v, einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon t).fragt (.inr (.inl r)))) = some v ∧
          D.rzusage r v = true
      · obtain ⟨v, hv, hz⟩ := hex
        exact fort_schritt (w_regLies rfl r hk rest k ρ hx v hv hz hΛ)
      · by_cases hleer : AntwortLeer D (some (D.rtyp r))
        · -- the checker refuses a register with an empty type (W1)
          simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
          exact absurd hleer (stelleC_iff.mp hAnt.1)
        refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, fun v hv => ?_, hleer⟩
        cases hz : D.rzusage r v
        · rfl
        · exact absurd ⟨v, hv, hz⟩ hex
  | regReadElse r hk zusage sonst rest =>
      cases hv : einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon t).fragt (.inr (.inl r)))) with
      | none =>
          by_cases hleer : AntwortLeer D (some (D.rtyp r))
          · simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
            exact absurd hleer (stelleC_iff.mp hAnt.1)
          · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hv, hleer⟩
      | some v =>
          cases hw : wahr? (eval (((M.weltVon t).fragt (.inr (.inl r))).lese Λ zusage.orte) zusage
              (((M.weltVon t).fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) with
          | true => exact fort_schritt (w_regLiesElseWahr rfl r hk zusage sonst rest k ρ hx v hv hw hΛ)
          | false =>
              exact fort_schritt (w_regLiesElseFalsch rfl r hk zusage sonst rest k ρ hx v hv hw hΛ)
  | awaits g payload hp hL hat rest =>
      cases hvis : O.sichtbar g ((M.weltVon t).fragt (.inr (.inr g))) with
      | false => exact fort_flagge ⟨l, Γ, Λ, ρ, _, hx, hvis⟩
      | true => exact fort_schritt (w_awaits rfl g payload hp hL hat rest k ρ hx hvis hΛ)
  | exchange g neuE hw hL rest => exact fort_schritt (w_exchange rfl g neuE hw hL rest k ρ hx hΛ)
  | narrow e lo' hi' sonst rest =>
      by_cases h : lo' ≤ (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ∧
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ≤ hi'
      · exact fort_schritt (w_narrowOk rfl lo' hi' e sonst rest k ρ hx rfl h hΛ)
      · exact fort_schritt (w_narrowElse rfl lo' hi' e sonst rest k ρ hx h hΛ)
  | check c sonst rest =>
      cases hw : wahr? (eval ((M.weltVon t).lese Λ c.orte) c ((M.weltVon t).lese Λ c.orte) ρ) with
      | true => exact fort_schritt (w_pruefWahr rfl c sonst rest k ρ hx hw hΛ)
      | false => exact fort_schritt (w_pruefFalsch rfl c sonst rest k ρ hx hw hΛ)
  | float op a b lo hi rest =>
      cases hv : gleitPasst lo hi (gleitRechne op
          (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) a
            ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x
          (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) b
            ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact absurd hv (hB.1 l Γ Λ _ ρ op _ _ _ _ lo hi a b rest k hx)
      | some v => exact fort_schritt (w_gleit rfl op a b lo hi rest k ρ hx v hv hΛ)
  | floatLit q lo hi rest =>
      cases hv : gleitPasst lo hi (bruch q) with
      | none => exact absurd hv (hB.2.1 l Γ Λ _ ρ q lo hi rest k hx)
      | some v => exact fort_schritt (w_gleitLit rfl q lo hi rest k ρ hx v hv)
  | floatOf e lo hi rest =>
      cases hv : gleitPasst lo hi (gleitAusInt
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n) with
      | none => exact absurd hv (hB.2.2 l Γ Λ _ ρ _ _ e lo hi rest k hx)
      | some v => exact fort_schritt (w_gleitVon rfl e lo hi rest k ρ hx v hv hΛ)
  | floatNarrow e lo hi sonst rest =>
      cases hv : gleitPasst lo hi
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).x with
      | none => exact fort_schritt (w_gleitNarrowElse rfl e lo hi sonst rest k ρ hx hv hΛ)
      | some v => exact fort_schritt (w_gleitNarrowOk rfl e lo hi sonst rest k ρ hx v hv hΛ)
  | cons s rest =>
      by_cases hbl : s.istBlatt = true ∧ s.istAbschluss = false
      · rcases blatt_fall hO passes s hbl.1 hbl.2 (M.weltVon t) ρ hΛ with
          ⟨σ', ρ', hst, herw⟩ | ⟨h, hh⟩ | ⟨e, he⟩
        · exact fort_schritt (w_dannBlatt rfl s rest k ρ hbl.1 hx hΛ σ' ρ' hst herw)
        · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hbl.1, h, hh⟩
        · exact absurd he (hP.2.2.2.2.1 l Γ Λ _ _ ρ s rest k hbl.1 hx e)
      · cases s with
        | ite c tb eb =>
            cases hw : wahr? (eval ((M.weltVon t).lese Λ c.orte) c ((M.weltVon t).lese Λ c.orte) ρ) with
            | true => exact fort_schritt (w_iteWahr rfl c tb eb rest k ρ hx hw hΛ)
            | false => exact fort_schritt (w_iteFalsch rfl c tb eb rest k ρ hx hw hΛ)
        | onOption o p a =>
            cases hv : eval ((M.weltVon t).lese Λ o.orte) o ((M.weltVon t).lese Λ o.orte) ρ with
            | none => exact fort_schritt (w_optNone rfl o p a rest k ρ hx hv hΛ)
            | some v => exact fort_schritt (w_optSome rfl o p a rest k ρ hx v hv hΛ)
        | onTag v arms =>
            match hw : armWahlG arms (eval ((M.weltVon t).lese Λ v.orte) v
                ((M.weltVon t).lese Λ v.orte) ρ) with
            | ⟨none, b', nutz⟩ => exact fort_schritt (w_tagNone rfl v arms rest k ρ hx b' nutz hw hΛ)
            | ⟨some τ, b', nutz⟩ =>
                exact fort_schritt (w_tagSome rfl v arms rest k ρ hx τ b' nutz hw hΛ)
        | onWhy r arms => exact fort_schritt (w_grund rfl r arms rest k ρ hx hΛ)
        | call g args hp hr => exact fort_schritt (w_rufDann rfl g args hp hr rest k ρ hx hΛ)
        | callInd p args hp hr =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.dannCallInd M t l Γ Λ Λ _ _ p args hp hr rest k ρ hx
              hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
                ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
        | callIndElse p args he hp hr err =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.dannCallIndElse M t l Γ Λ Λ _ _ _ p args he hp hr err
              rest k ρ hx hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
                ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
        | locks L hr body =>
            have hA : AnSperre M t L := ⟨l, Γ, Λ, _, ρ, hr, body, rest, k, hx⟩
            by_cases hfrei : RufFreiG M t L
            · exact fort_schritt' (schritt_an_sperre hR hA hfrei)
            · refine Or.inr (Or.inl ⟨⟨L, hA⟩, fun L' hA' => ?_⟩)
              have e1 := anSperre_kopf hA'
              rw [hx] at e1
              have hLL : L = L' := by
                simpa [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon] using e1
              subst hLL
              exact Classical.byContradiction fun hno => hfrei fun g hg hLg => hno ⟨g, hg, hLg⟩
        | breaking i body => exact fort_schritt (w_breaking rfl i body rest k ρ hx)
        | traverse tb inv body => exact fort_schritt (w_dannTrav rfl tb inv body rest k ρ hx)
        | consumeTraverse tb member edge inv bound mass body =>
            exact fort_schritt' ⟨_, RufSchrittG.dannVerbrauch M t l Γ Λ _ tb member edge inv
              bound mass body rest k ρ hx⟩
        | retry n bis body ueber => exact fort_schritt (w_dannRetry rfl n bis body ueber rest k ρ hx)
        | forever a inv body => exact fort_schritt (w_dannForever rfl a inv body rest k ρ hx)
        | ret e hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨ziel, hart⟩ := popArt_von hst hkt
                exact fort_schritt (w_dannRetP rfl caller rst hst hart e hp rest k ρ hx hΛ)
        | retWhy r hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
                exact fort_schritt (w_dannRetGrundP rfl caller rst hst hart r hp rest k ρ hx hΛ)
        | retScoped e R =>
            exact fort_schritt' (w_scopedWert ρ _ e R hx rfl
              (Bool.and_eq_true.mp hScope).1 hΛ hkt)
        | retWhyScoped grund R =>
            exact fort_schritt' (w_scopedGrund ρ _ grund R hx rfl
              (Bool.and_eq_true.mp hScope).1 hΛ hkt)
        | leave h =>
            subst h
            have habs : k.absorb = true := by simpa [GRest.nimmtAb] using hnimmt
            exact fort_schritt' (fort_abb hP true ρ rest k hx habs hΛ)
        | next h =>
            subst h
            have habs : k.absorb = true := by simpa [GRest.nimmtAb] using hnimmt
            exact fort_schritt' (fort_abb hP false ρ rest k hx habs hΛ)
        | _ => exact absurd ⟨rfl, rfl⟩ hbl

/-- **The progress case analysis for one thread**: finished, waiting for a
    lock another thread holds, at a named hardware stop, or it can step. -/
theorem fortschritt_faden (hO : GutO O) {w0 : D.Fn} {M : RufMaschineG D} {t : Faden}
    (hI : FortInvG (M.faeden t)) (hnw : (M.faeden t).kopf.wartend = false)
    (hH : HeldIn (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hP : PrueftG O passes M t) (hB : BereichG M t) (hR : RangInvG w0 (M.faeden t))
    (hA : (M.faeden t).kopf.rest.2.2.2.2.aR (stelleC D))
    (hScope : (M.faeden t).kopf.rest.2.2.2.2.scopesGut)
    (hPosition : AntwortPositionG (M.faeden t)) :
    FortFaden P O passes M t := by
  obtain ⟨hk, hb, _, hkt⟩ := hI
  have hnw' : (M.faeden t).kopf.rest.2.2.2.2.wartend = false := hnw
  have hPosition' := hPosition.1
  change (M.faeden t).kopf.rest.2.2.2.2.antwortPosition ((M.faeden t).stapel = []) at hPosition'
  generalize hx : (M.faeden t).kopf.rest = x at hk hb hH hnw' hA hScope hPosition'
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  have hΛ : HeldIn Λ (offen (M.faeden t).spur) := hH
  cases r with
  | ende e =>
      have hl : l = false := by simpa [GRest.fOk] using hk
      exact fort_ende hO hkt hP ρ e hx hl hΛ hA hScope
  | dann b k =>
      have hn : k.nimmtAb = true := by
        revert hk
        simp only [GRest.fOk, Bool.and_eq_true]
        intro hk
        exact hk.1.2
      exact fort_dann hO hkt hP hB hR ρ b k hx hn hΛ hA.1 hScope.1
  | schrumpf k =>
      cases ρ with
      | cons v ρ₀ => exact fort_schritt (w_schrumpf rfl k v ρ₀ hx)
  | frei L k => exact fort_schritt (w_freiGib rfl L k ρ hx)
  | trav tb inv body ks k =>
      have hw := hP.1 l Γ Λ ρ tb inv body ks k hx
      cases ks with
      | nil => exact fort_schritt (w_travDone rfl tb inv body k ρ hx hw hΛ)
      | cons i is => exact fort_schritt (w_travNext rfl tb inv body i is k ρ hx hw hΛ)
  | travRest tb inv body is k =>
      cases ρ with
      | cons i ρ₀ => exact fort_schritt (w_travFort rfl tb inv body is k i ρ₀ hx)
  | verbrauch tb member edge inv bound mass body nr k =>
      have hp := hP.2.2.2.2.2.1 l Γ Λ ρ tb member edge inv bound mass body nr k hx
      cases nr with
      | zero =>
          have : 0 < 0 := hp.1
          omega
      | succ nr =>
          let σ₁ := (M.weltVon t).lese Λ inv.orte
          let σ₂ := σ₁.lese Λ (member.orte ++ edge.orte)
          cases hsel : verbrauchWahl (alleIndizes (D.count tb))
              (fun i => wahr? (eval σ₂ member σ₂ (.cons i ρ)))
              (fun i j => wahr? (eval σ₂ edge σ₂ (.cons i (.cons j ρ))))
              (fun i j => decide (i.n = j.n)) with
          | none =>
              obtain ⟨neu, hneu, _⟩ := (Erw.lese (M.weltVon t) Λ inv.orte).trans
                (Erw.lese σ₁ Λ (member.orte ++ edge.orte))
              exact fort_schritt' ⟨_, RufSchrittG.verbrauchLeer M t l Γ Λ tb member edge inv bound mass
                body nr k ρ hx σ₁ rfl hp.2.1 σ₂ rfl hsel (hp.2.2 hsel) neu hneu hΛ⟩
          | some i =>
              obtain ⟨neu, hneu, _⟩ := ((Erw.lese (M.weltVon t) Λ inv.orte).trans
                (Erw.lese σ₁ Λ (member.orte ++ edge.orte))).trans (Erw.lese σ₂ Λ mass.orte)
              exact fort_schritt' ⟨_, RufSchrittG.verbrauchWeiter M t l Γ Λ tb member edge inv bound mass
                body nr k ρ hx σ₁ rfl hp.2.1 σ₂ rfl i hsel _ rfl _ rfl neu hneu hΛ⟩
  | verbrauchRest tb member edge inv bound mass body nr vor k =>
      cases ρ with
      | cons i ρ₀ =>
          have hp := hP.2.2.2.2.2.2.1 _ _ Λ ρ₀ tb member edge inv bound mass body nr vor k i hx
          obtain ⟨neu, hneu, _⟩ := Erw.lese (M.weltVon t) Λ mass.orte
          exact fort_schritt' ⟨_, RufSchrittG.verbrauchFort M t _ _ Λ tb member edge inv bound mass
            body nr vor k i ρ₀ hx _ rfl _ rfl hp neu hneu hΛ⟩
  | wieder n bis body ueber k =>
      cases n with
      | zero => exact fort_schritt (w_wiederUeber rfl bis body ueber k ρ hx)
      | succ n =>
          cases hw : wahr? (eval ((M.weltVon t).lese Λ bis.orte) bis
              ((M.weltVon t).lese Λ bis.orte) ρ) with
          | true => exact fort_schritt (w_wiederWeiter rfl n bis body ueber k ρ hx hw hΛ)
          | false => exact fort_schritt (w_wiederSchritt rfl n bis body ueber k ρ hx hw hΛ)
  | wiederRest n bis body ueber k => exact fort_schritt (w_wiederFort rfl n bis body ueber k ρ hx)
  | ewig a n inv body k =>
      cases n with
      | zero => exact fort_budget ⟨l, Γ, Λ, ρ, _, hx, trivial⟩
      | succ n =>
          exact fort_schritt (w_ewigWeiter rfl a n inv body k ρ hx
            (hP.2.1 l Γ Λ ρ a n inv body k hx) hΛ)
  | ewigRest a n inv body k => exact fort_schritt (w_ewigFort rfl a n inv body k ρ hx)
  | wartet rest k => simp only [GRest.wartend, Bool.true_eq_false] at hnw'
  | wartetSonst n err rest k => simp only [GRest.wartend, Bool.true_eq_false] at hnw'
  | aufraeumen a remaining => exact fort_schritt' (w_aufraeumen ρ a remaining hPosition' hx hkt)
  | zurueckgekehrt a =>
      have hroot : (M.faeden t).stapel = [] := hPosition'
      exact Or.inl ⟨hroot, by rw [hx]; rfl⟩
  | rueckBereit => simp only [GRest.fOk, Bool.false_eq_true] at hk
  | abbruch k => simp only [GRest.blockiert, Bool.true_eq_false] at hb
  | leer => simp only [GRest.blockiert, Bool.true_eq_false] at hb

end Fort
/-! ## 6. The float range checks pass (verdict F1) -/


end Gabbro.Grammatik
