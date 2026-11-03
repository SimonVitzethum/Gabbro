module

public import Grammatik.Nichtinterferenz.Lokal
public import Grammatik.Nichtinterferenz.LokalSchritt.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritt
variable {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}
variable (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
  (P : Programm D) (O : Orakel D) (passes : Nat)
  (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D))
  {sp₁ sp₂ : Speicher D}
include hST

include hAx in
theorem kDann_rel (hO : OrakelTreu T AxT O) (hRL : RegLokal O) (hsp : SpeicherGleich T sp₁ sp₂)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D f) l Γ Λ Λ') (k : GRest D (vertragVon D f) l Γ Λ')
    (hb : nB S Ax b = true) (hk : k.nR S Ax) :
    KRel T (kDann P O passes st f rho spur sp₁ ρ b k) (kDann P O passes st f rho spur sp₂ ρ b k) := by
  have hW := WRel.welt hsp spur
  cases b with
  | nil => exact KRel.lokal _ _ _ _ _ rfl hsp
  | cons s rest =>
      simp only [nB, Bool.and_eq_true] at hb
      exact kDannCons_rel hST hAx P O passes st f rho spur hO hsp ρ s rest k hb.1 hk
  | bind e rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1) ρ]
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | bindCall g args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hb.1) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindCallInd p args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      have h1 := hW.lese Λ (p.orte ++ args.orte)
      rw [h1.eval p (alle_von hST hb.1.1) ρ, h1.evalArgs args (alle_von hST hb.1.2) ρ]
      generalize eval _ p _ ρ = x
      obtain ⟨g, hg⟩ := x
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindCallIndElse p args he hp hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      have h1 := hW.lese Λ (p.orte ++ args.orte)
      rw [h1.eval p (alle_von hST hb.1.1.1) ρ, h1.evalArgs args (alle_von hST hb.1.1.2) ρ]
      generalize eval _ p _ ρ = x
      obtain ⟨g, hg⟩ := x
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindCallElse g args he hp hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hb.1.1) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindAxiom a args he hw hg hd hgd rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a hb.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kDann]
      rw [h1.evalArgs args (alle_von hST hb.1.2) ρ]
      revert e1 e2
      generalize axiomAntwort O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwort O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      cases r1 with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | bindAxiomOpt e a args he hp hd hgd rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a hb.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kDann]
      rw [h1.evalArgs args (alle_von hST hb.1.2) ρ]
      revert e1 e2
      generalize axiomAntwort O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwort O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      cases r1 with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | bindAxiomElse a args he' hr hw hg hd hgd err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwortSonst_rel O hO (hAx a hb.1.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kDann]
      rw [h1.evalArgs args (alle_von hST hb.1.1.2) ρ]
      revert e1 e2
      generalize axiomAntwortSonst O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwortSonst O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      rcases r1 with _ | v | r
      · exact KRel.none_l _
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | bindAxiomOptElse e a args he' hp hd hgd hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwortSonst_rel O hO (hAx a hb.1.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kDann]
      rw [h1.evalArgs args (alle_von hST hb.1.1.2) ρ]
      revert e1 e2
      generalize axiomAntwortSonst O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwortSonst O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      rcases r1 with _ | v | r
      · exact KRel.none_l _
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | regRead r hk' rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.1 r _ _ (gleichAuf_von_sg (σ := (sp₁.welt spur).fragt (.inr (.inl r))) (τ := (sp₂.welt spur).fragt (.inr (.inl r))) hsp
        (alle_von hST hb.1))]
      generalize einpassen _ (D.rtyp r) _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | regReadElse r hk' zusage sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.1 r _ _ (gleichAuf_von_sg (σ := (sp₁.welt spur).fragt (.inr (.inl r))) (τ := (sp₂.welt spur).fragt (.inr (.inl r))) hsp
        (alle_von hST hb.1.1.1))]
      generalize einpassen _ (D.rtyp r) _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v =>
          simp only
          rw [((hW.fragt (.inr (.inl r))).lese Λ zusage.orte).eval zusage (alle_von hST hb.1.1.2) (.cons v ρ)]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
            (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | awaits g payload hp hL hat rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.2 g _ _ (gleichAuf_von_sg (σ := (sp₁.welt spur).fragt (.inr (.inr g))) (τ := (sp₂.welt spur).fragt (.inr (.inr g))) hsp
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hST _ hb.1]))]
      have hg : (((sp₁.welt spur).fragt (.inr (.inr g))).lese Λ [.inr g]).globs g =
          (((sp₂.welt spur).fragt (.inr (.inr g))).lese Λ [.inr g]).globs g := hsp (.inr g) (hST _ hb.1)
      rw [hg]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | exchange g neuE hw hL rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ (.inr g :: neuE.orte)
      have hg : ((sp₁.welt spur).lese Λ (.inr g :: neuE.orte)).globs g =
          ((sp₂.welt spur).lese Λ (.inr g :: neuE.orte)).globs g := hsp (.inr g) (hST _ hb.1.1)
      simp only [kDann]
      rw [hg, h1.eval neuE (alle_von hST hb.1.2) _]
      exact KRel.lokal _ _ _ _ _ (h1.schreibGlob g Λ _).1 (h1.schreibGlob g Λ _).2
  | narrow e lo' hi' sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have he' := (hW.lese Λ e.orte).eval e (alle_von hST hb.1.1) ρ
      have hn := congrArg Zahl.n he'
      simp only [kDann]
      refine KRel.dite' (by rw [hn]) (fun h₁ h₂ => KRel.lokalEnv _ _ _ ?_ _ rfl hsp)
        (fun _ _ => KRel.lokal _ _ _ _ _ rfl hsp)
      congr 1
      exact zahl_ext hn
  | narrowRequired e lo' hi' rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have hn := congrArg Zahl.n ((hW.lese Λ e.orte).eval e (alle_von hST hb.1) ρ)
      simp only [kDann]
      refine KRel.dite' (by rw [hn]) (fun h₁ h₂ => KRel.lokalEnv _ _ _ ?_ _ rfl hsp)
        (fun _ _ => KRel.none_l _)
      congr 1
      exact zahl_ext hn
  | check c sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ c.orte).eval c (alle_von hST hb.1.1) ρ]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
        (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | float op a b lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      have h1 := hW.lese Λ (a.orte ++ b.orte)
      rw [h1.eval a (alle_von hST hb.1.1) ρ, h1.eval b (alle_von hST hb.1.2) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | floatLit q lo hi rest =>
      simp only [kDann]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | floatOf e lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | floatNarrow e lo hi sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1.1) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.lokal _ _ _ _ _ rfl hsp
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp

include hAx in
theorem kr_rel (hO : OrakelTreu T AxT O) (hRL : RegLokal O) (hsp : SpeicherGleich T sp₁ sp₂)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D f) l Γ Λ) (hr : r.nR S Ax) :
    KRel T (kr P O passes st f rho spur sp₁ ρ r) (kr P O passes st f rho spur sp₂ ρ r) := by
  have hW := WRel.welt hsp spur
  cases r with
  | ende e => exact kEnde_rel hST hAx P O passes st f rho spur hO hsp ρ e hr
  | dann b k => exact kDann_rel hST hAx P O passes st f rho spur hO hRL hsp ρ b k hr.1 hr.2
  | schrumpf k =>
      cases ρ
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | frei L k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | trav t inv body ks k =>
      simp only [GRest.nR] at hr
      cases ks with
      | nil =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
      | cons i is =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | travRest t inv body is k =>
      cases ρ
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | wieder n bis body ueber k =>
      simp only [GRest.nR] at hr
      cases n with
      | zero => exact KRel.lokal _ _ _ _ _ rfl hsp
      | succ n =>
          simp only [kr]
          rw [(hW.lese Λ bis.orte).eval bis (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
            (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | wiederRest n bis body ueber k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | ewig a n inv body k =>
      simp only [GRest.nR] at hr
      cases n with
      | zero => exact KRel.none_l _
      | succ n =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | ewigRest a n inv body k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | verbrauch t member edge inv bound mass body rest k =>
      cases rest with
      | zero => exact KRel.none_l _
      | succ rest =>
          simp only [GRest.nR] at hr
          obtain ⟨hmemS, hedgeS, hinvS, hmassS, -, -⟩ := hr
          have h1 := hW.lese Λ inv.orte
          have h2 := h1.lese Λ (member.orte ++ edge.orte)
          have e1 : (fun (i : Wert D (.index (D.count t))) => wahr?
              (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                member
                (((sp₁.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                (.cons i ρ))) =
              (fun (i : Wert D (.index (D.count t))) => wahr?
              (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                member
                (((sp₂.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                (.cons i ρ))) :=
            funext fun i => congrArg wahr?
              (h2.eval member (alle_von hST hmemS) (.cons i ρ))
          have e2 : (fun (i : Wert D (.index (D.count t)))
              (j : Wert D (.index (D.count t))) => wahr?
              (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                edge
                (((sp₁.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                (.cons i (.cons j ρ)))) =
              (fun (i : Wert D (.index (D.count t)))
              (j : Wert D (.index (D.count t))) => wahr?
              (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                edge
                (((sp₂.welt spur).lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))
                (.cons i (.cons j ρ)))) :=
            funext fun i => funext fun j => congrArg wahr?
              (h2.eval edge (alle_von hST hedgeS) (.cons i (.cons j ρ)))
          have hscr : verbrauchWahl (alleIndizes (D.count t))
              (fun (i : Wert D (.index (D.count t))) => wahr?
                (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) member
                  (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i ρ)))
              (fun (i : Wert D (.index (D.count t)))
                (j : Wert D (.index (D.count t))) => wahr?
                (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) edge
                  (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i (.cons j ρ))))
              (fun i j => decide (i.n = j.n)) =
            verbrauchWahl (alleIndizes (D.count t))
              (fun (i : Wert D (.index (D.count t))) => wahr?
                (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) member
                  (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i ρ)))
              (fun (i : Wert D (.index (D.count t)))
                (j : Wert D (.index (D.count t))) => wahr?
                (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) edge
                  (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i (.cons j ρ))))
              (fun i j => decide (i.n = j.n)) := by
            rw [e1, e2]
          have hsome : ∀ v : Wert D (.index (D.count t)),
              KRel T
                (kLokal st f rho (.cons v ρ)
                  (.dann body (.verbrauchRest t member edge inv bound mass body rest
                    (eval ((((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte) mass
                      ((((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte) ρ).n k))
                  (((((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte).spur) sp₁)
                (kLokal st f rho (.cons v ρ)
                  (.dann body (.verbrauchRest t member edge inv bound mass body rest
                    (eval ((((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte) mass
                      ((((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte) ρ).n k))
                  (((((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).lese Λ mass.orte).spur) sp₂) := by
            intro v
            have hma : WRel T
                (((((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)).lese Λ mass.orte))
                (((((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)).lese Λ mass.orte)) :=
              h2.lese Λ mass.orte
            rw [hma.eval mass (alle_von hST hmassS) ρ]
            exact KRel.lokal _ _ _ _ _ hma.1 hsp
          have hnone :
              KRel T
                (if ((alleIndizes (D.count t)).all fun i =>
                    !(wahr? (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)) member
                      (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)) (.cons i ρ)))) = true then
                  kLokal st f rho ρ k
                    ((((sp₁.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).spur) sp₁
                else none)
                (if ((alleIndizes (D.count t)).all fun i =>
                    !(wahr? (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)) member
                      (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)) (.cons i ρ)))) = true then
                  kLokal st f rho ρ k
                    ((((sp₂.welt spur).lese Λ inv.orte).lese Λ
                      (member.orte ++ edge.orte)).spur) sp₂
                else none) := by
            have hmem : ∀ i : Wert D (.index (D.count t)),
                wahr? (eval (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) member
                  (((sp₁.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i ρ)) =
                wahr? (eval (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) member
                  (((sp₂.welt spur).lese Λ inv.orte).lese Λ
                  (member.orte ++ edge.orte)) (.cons i ρ)) :=
              fun i => congrArg wahr?
                (h2.eval member (alle_von hST hmemS) (.cons i ρ))
            simp only [hmem]
            exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ h2.1 hsp)
              (fun _ => KRel.none_l _)
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hinvS) ρ]
          refine KRel.ite (fun _ => ?_) (fun _ => KRel.none_l _)
          exact KRel.opt hscr hsome hnone
  | verbrauchRest t member edge inv bound mass body rest vor k =>
      cases ρ with
      | cons _ ρ =>
          simp only [GRest.nR] at hr
          obtain ⟨-, -, -, hmassS, -, -⟩ := hr
          simp only [kr]
          rw [(hW.lese Λ mass.orte).eval mass (alle_von hST hmassS) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ (hW.lese _ _).1 hsp)
            (fun _ => KRel.none_l _)
  | wartet b k => exact KRel.none_l _
  | wartetSonst n err b k => exact KRel.none_l _
  | abbruch k => exact KRel.none_l _
  | rueckBereit => exact KRel.none_l _
  | leer => exact KRel.none_l _

end Schritt

/-- **Step consistency for one thread, over the ghost-free state
    (`schrittK_rel`).** The head residue of `k` passes the flow check for
    `S` and `Ax`; `S ⊆ T`, `Ax ⊆ AxT`, the oracle is faithful on `T` for
    `AxT`, registers are local. Two memories that agree on `T`: the two
    steps, if both exist, give the same ghost-free state and memories that
    agree on `T`. -/
theorem schrittK_rel {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}
    (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : OrakelTreu T AxT O) (hRL : RegLokal O)
    (k : KFaden D) (hk : k.kopf.rest.2.2.2.2.nR S Ax) {sp₁ sp₂ : Speicher D}
    (hsp : SpeicherGleich T sp₁ sp₂) :
    KRel T (kSchrittK P O passes k sp₁) (kSchrittK P O passes k sp₂) :=
  kr_rel hST hAx P O passes k.stapel k.kopf.f k.kopf.rho k.spur hO hRL hsp _ _ hk

end Gabbro.Grammatik
