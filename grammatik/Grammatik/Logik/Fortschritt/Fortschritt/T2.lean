/- Part 2 of 3 of `Fortschritt` (split by instrumente/teile/lean-teilen.py; the umbrella `Fortschritt.lean` imports all parts). -/
import Grammatik.Logik.Fortschritt.Fortschritt.T1

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
  | _ => simp [GRest.absorb] at habs

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
    (hΛ : HeldIn Λ (offen (M.faeden t).spur)) (hAnt : b.ants.all (stelleC D) = true) :
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
        · exact absurd he (hP.2.2.2.2 l Γ Λ _ _ ρ s rest k hbl.1 hx e)
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
            | ⟨some (lo, hi), b', nutz⟩ =>
                exact fort_schritt (w_tagSome rfl v arms rest k ρ hx lo hi b' nutz hw hΛ)
        | onWhy r arms => exact fort_schritt (w_grund rfl r arms rest k ρ hx hΛ)
        | call g args hp hr => exact fort_schritt (w_rufDann rfl g args hp hr rest k ρ hx hΛ)
        | callInd p args hp hr =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.dannCallInd M t l Γ Λ Λ _ _ p args hp hr rest k ρ hx
              hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
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
    (hA : (M.faeden t).kopf.rest.2.2.2.2.aR (stelleC D)) :
    FortFaden P O passes M t := by
  obtain ⟨hk, hb, _, hkt⟩ := hI
  have hnw' : (M.faeden t).kopf.rest.2.2.2.2.wartend = false := hnw
  generalize hx : (M.faeden t).kopf.rest = x at hk hb hH hnw' hA
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  have hΛ : HeldIn Λ (offen (M.faeden t).spur) := hH
  cases r with
  | ende e =>
      have hl : l = false := by simpa [GRest.fOk] using hk
      exact fort_ende hO hkt hP ρ e hx hl hΛ hA
  | dann b k =>
      have hn : k.nimmtAb = true := by
        revert hk
        simp only [GRest.fOk, Bool.and_eq_true]
        intro hk
        exact hk.1.2
      exact fort_dann hO hkt hP hB hR ρ b k hx hn hΛ hA.1
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
  | wartet rest k => simp [GRest.wartend] at hnw'
  | wartetSonst n err rest k => simp [GRest.wartend] at hnw'
  | abbruch k => simp [GRest.blockiert] at hb
  | leer => simp [GRest.blockiert] at hb

end Fort
/-! ## 6. The float range checks pass (verdict F1) -/


end Gabbro.Grammatik
