module

public import Grammatik.Logik.Fortschritt.Fortschritt.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Fort

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- What progress says about one thread. -/
def FortFaden (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) :
    Prop :=
  FertigG M t ∨ WartetG M t ∨ Zielsatz.HaltBenannt O passes M .flagge t ∨
    Zielsatz.HaltBenannt O passes M .budget t ∨ Zielsatz.HaltBenannt O passes M .hardware t ∨
    Zielsatz.HaltBenannt O passes M .nieZurueck t ∨ ∃ M', RufSchrittG P O passes M t M'

theorem fort_hw {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .hardware t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem fort_flagge {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .flagge t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inl h))

theorem fort_budget {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .budget t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem fort_schritt {M : RufMaschineG D} {t : Faden} {X : RufMaschineG D → Prop}
    (h : ∃ M', RufSchrittG P O passes M t M' ∧ X M') : FortFaden P O passes M t := by
  obtain ⟨M', hs, _⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨M', hs⟩)))))

theorem fort_schritt' {M : RufMaschineG D} {t : Faden}
    (h : ∃ M', RufSchrittG P O passes M t M') : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem fort_nie {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .nieZurueck t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- **The caller receives a value** (`FormG`, the invariant of the pop). -/
theorem popArt_von {M : RufMaschineG D} {t : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hst : (M.faeden t).stapel = caller :: rst)
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) :
    ∃ ziel, PopArt (M.faeden t).kopf.f caller ziel := by
  rw [hst] at hkt
  rcases hkt.1 with ⟨hnw, _⟩ | ⟨_, _, _, _, _, restb, k, ρc, hc, he, _⟩ |
      ⟨_, _, _, _, _, n, err, restb, k, ρc, hc, he, _⟩
  · exact ⟨_, PopArt.wie hnw⟩
  · exact ⟨_, PopArt.bind restb k ρc hc he⟩
  · exact ⟨_, PopArt.bindSonst n err restb k ρc hc he⟩

/-- **The caller receives a reason** (`FormG`): only a caller in `let … else`
    can be below a frame that has a reason to answer. -/
theorem popGrund_von {M : RufMaschineG D} {t : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hst : (M.faeden t).stapel = caller :: rst)
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel)
    (r : Fin (vertragVon D (M.faeden t).kopf.f).gruende) :
    ∃ zielG, PopGrund (M.faeden t).kopf.f caller zielG := by
  rw [hst] at hkt
  have hr : r.val < D.gruende (M.faeden t).kopf.f := r.2
  rcases hkt.1 with ⟨_, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h0⟩ |
      ⟨_, _, _, _, _, n, err, restb, k, ρc, hc, _, hn⟩
  · omega
  · omega
  · subst hn
    exact ⟨_, PopGrund.sonst err restb k ρc hc⟩

/-- **`leave`/`next` at a loop-flagged head** whose continuation absorbs:
    a loop shim fires, or a layer is peeled. -/
theorem fort_abb {M : RufMaschineG D} {t : Faden} (hP : PrueftG O passes M t) (w : Bool)
    {Γ : Ctx} {Λ Λ1 : List (Res D)} (ρ : Env D Γ)
    (rest : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ1)
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) true Γ Λ1)
    (hx : (M.faeden t).kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) rest) k⟩)
    (habs : k.absorb = true) (hΛ : HeldIn Λ (offen (M.faeden t).spur)) :
    ∃ M', RufSchrittG P O passes M t M' := by
  cases k with
  | travRest tb inv body is k' =>
      cases ρ with
      | cons i ρ₀ =>
          cases w with
          | true =>
              have hw := hP.2.2.1 _ _ _ _ ρ₀ tb inv body is k' rest rfl i hx
              obtain ⟨M', hs, _⟩ := w_leaveTrav (P := P) rfl tb inv body is k' rest i ρ₀ hx hw hΛ
              exact ⟨M', hs⟩
          | false =>
              obtain ⟨M', hs, _⟩ := w_nextTrav (P := P) (O := O) (passes := passes) rfl tb inv body
                is k' rest i ρ₀ hx hΛ
              exact ⟨M', hs⟩
  | wiederRest n bis body ueber k' =>
      obtain ⟨M', hs, _⟩ := w_abbWieder (P := P) (O := O) (passes := passes) rfl w n bis body ueber
        k' rest ρ hx hΛ
      exact ⟨M', hs⟩
  | ewigRest a n inv body k' =>
      obtain ⟨M', hs, _⟩ := w_abbEwig (P := P) (O := O) (passes := passes) rfl w a n inv body k'
        rest ρ hx hΛ
      exact ⟨M', hs⟩
  | dann b k' =>
      obtain ⟨M', hs, _⟩ := w_peelDann (P := P) (O := O) (passes := passes) rfl w rest b k' ρ hx
      exact ⟨M', hs⟩
  | schrumpf k' =>
      cases ρ with
      | cons v ρ₀ =>
          obtain ⟨M', hs, _⟩ := w_peelSchrumpf (P := P) (O := O) (passes := passes) rfl w rest k' v
            ρ₀ hx
          exact ⟨M', hs⟩
  | frei L k' =>
      obtain ⟨M', hs, _⟩ := w_peelFrei (P := P) (O := O) (passes := passes) rfl w L rest k' ρ hx
      exact ⟨M', hs⟩
  | abbruch k' =>
      obtain ⟨M', hs, _⟩ := w_peelAbbruch (P := P) (O := O) (passes := passes) rfl w rest k' ρ hx
      exact ⟨M', hs⟩
  | _ => simp only [GRest.absorb, Bool.false_eq_true] at habs

/-- **An `ende` head**: a leaf, an unfold, a call, a pop, or a finished
    thread; `leave`/`next` cannot stand there (`fOk`: no `ende` node in a
    loop). -/
theorem fort_ende (hO : GutO O) {M : RufMaschineG D} {t : Faden}
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) (hP : PrueftG O passes M t)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (e : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende e⟩) (hl : l = false)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur)) (hAnt : e.ants.all (stelleC D) = true) :
    FortFaden P O passes M t := by
  cases e with
  | ret e hp =>
      cases hst : (M.faeden t).stapel with
      | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
      | cons caller rst =>
          obtain ⟨ziel, hart⟩ := popArt_von hst hkt
          exact fort_schritt (w_rueckP rfl caller rst hst hart e hp ρ hx hΛ)
  | retWhy r hp =>
      cases hst : (M.faeden t).stapel with
      | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
      | cons caller rst =>
          obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
          exact fort_schritt (w_rueckGrundP rfl caller rst hst hart r hp ρ hx hΛ)
  | leave h => exact absurd (hl.symm.trans h) Bool.false_ne_true
  | next h => exact absurd (hl.symm.trans h) Bool.false_ne_true
  | bind e rest => exact fort_schritt (w_endeBind rfl e rest ρ hx hΛ)
  | bindCall g args he hp hr rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | bindCallElse g args he hp hr err rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | regRead r hk rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | regReadElse r hk z sonst rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | awaits g pl hp hL hat rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | bindCallInd p args he hp hr rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | bindCallIndElse p args he hp hr err rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | narrow e lo' hi' sonst rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | exchange g neu hw hL rest =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | ite c t' e =>
      exact fort_schritt' ⟨_, RufSchrittG.endeForm M t l Γ Λ _ ρ hl rfl hx⟩
  | bindAxiom a args he hw hg hd hgd rest =>
      rcases hax : axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v⟩
      · by_cases hleer : AntwortLeer D (D.aerg a)
        · simp only [Endblock.ants, List.all_cons, Bool.and_eq_true] at hAnt
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
        exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiom M t l Γ Λ _ a args he hw hg hd hgd rest
          ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
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
      · exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiomElseOk M t l Γ Λ _ a args he hr hw hg hd hgd err rest
          ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
      · exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiomElseGrund M t l Γ Λ _ a args he hr hw hg hd hgd err rest
          ρ hx _ rfl σ₂ r hax neu hneu hΛ⟩
  | bindAxiomOpt e a args he hp hd hgd rest =>
      rcases hax : axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v⟩
      · by_cases hleer : AntwortLeer D (D.aerg a)
        · simp only [Endblock.ants, List.all_cons, Bool.and_eq_true] at hAnt
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
        exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiomOpt M t l Γ Λ e a args he hp hd hgd rest
          ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
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
      · exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiomOptElseOk M t l Γ Λ e a args he hr hp hd hgd err rest
          ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
      · exact fort_schritt' ⟨_, RufSchrittG.endeBindAxiomOptElseGrund M t l Γ Λ e a args he hr hp hd hgd err rest
          ρ hx _ rfl σ₂ r hax neu hneu hΛ⟩
  | cons s rest =>
      by_cases hbl : s.istBlatt = true ∧ s.istAbschluss = false
      · rcases blatt_fall hO passes s hbl.1 hbl.2 (M.weltVon t) ρ hΛ with
          ⟨σ', ρ', hst, herw⟩ | ⟨h, hh⟩ | ⟨e, he⟩
        · exact fort_schritt (w_blatt rfl s rest ρ hbl.1 hx hΛ σ' ρ' hst herw)
        · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hbl.1, h, hh⟩
        · exact absurd he (hP.2.2.2.1 l Γ Λ _ ρ s rest hbl.1 hx e)
      · cases s with
        | call g args hp hr => exact fort_schritt (w_rufEnde rfl g args hp hr rest ρ hx hΛ)
        | callInd p args hp hr =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.rufCallInd M t l Γ Λ _ p args hp hr rest ρ hx hΛ
              _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
                ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
        | ret e hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨ziel, hart⟩ := popArt_von hst hkt
                exact fort_schritt (w_rueckConsP rfl caller rst hst hart e hp rest ρ hx hΛ)
        | retWhy r hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
                exact fort_schritt (w_rueckConsGrundP rfl caller rst hst hart r hp rest ρ hx hΛ)
        | leave h => exact absurd (hl.symm.trans h) Bool.false_ne_true
        | next h => exact absurd (hl.symm.trans h) Bool.false_ne_true
        | _ =>
            first
            | exact absurd ⟨rfl, rfl⟩ hbl
            | exact fort_schritt (w_endeEntf rfl _ rest ρ rfl hx)

end Fort
end Gabbro.Grammatik
