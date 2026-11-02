module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen.AkteurRFaelle.B.Teil17

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurR_dannRegLiesElseFalsch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hK : ∀ (f : D.Fn), KoerperGutRQ P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenR P O passes Q (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapel P M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (zusage : Expr D (D.rtyp r :: Γ) Λ Ty.bool)
  (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regReadElse r hk zusage sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon u).fragt (Sum.inr (Sum.inl r)))) = some v) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon u).fragt (Sum.inr (Sum.inl r))).lese Λ zusage.orte)
  (hw : wahr? (eval σ₁ zusage σ₁ (Env.cons v ρ)) = false) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenR P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenR_lokalQ hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrk⟩ := hok
  have hgq : GleichAuf _ (σ.fragt (.inr (.inl r))) ((M.weltVon u).fragt (.inr (.inl r))) := hg
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP, List.append_subset] at hss
  obtain ⟨⟨hzS, hsS⟩, _⟩ := hss
  have hw' : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) =
      false := by
    rw [eval_gleichAuf zusage (fun _ h => hzS h) (hgq.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
    exact hw
  refine ⟨(σ.fragt (.inr (.inl r))).lese Λ zusage.orte, Nat.le_trans (Nat.le_succ _) (lese_laenge (σ.fragt _) _ _), hg,
    okG_alsBlock sonst k rest.held_iff hks.2.1 hsS hrk, fun R O' hQ => ?_⟩
  have hrl : O'.regLies r (σ.fragt (.inr (.inl r))) = O.regLies r ((M.weltVon u).fragt (.inr (.inl r))) :=
    regLies_gleich hRL hQ r (regP_ok hks.1) hg
  exact semV_regLiesElseFalsch O' passes R r hk zusage sonst rest k σ ρ v
    (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw'

set_option maxHeartbeats 4000000 in
theorem akteurR_dannAwaits {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hK : ∀ (f : D.Fn), KoerperGutRQ P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenR P O passes Q (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapel P M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hLg : gdarf D g Λ)
  (hat : D.atomar g = true) (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.awaits g payload hp hLg hat rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hvis : O.sichtbar g ((M.weltVon u).fragt (Sum.inr (Sum.inr g))) = true) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon u).fragt (Sum.inr (Sum.inr g))).lese Λ [Sum.inr g]) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenR P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.gtyp g :: Γ,
                                (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.gtyp g :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.gtyp g :: Γ,
                                (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.gtyp g :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨D.gtyp g :: Γ,
                                  (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (D.gtyp g :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenR_lokalQ hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [Block.gOk] at hks
  simp only [blockOrteP, List.cons_subset] at hss
  have hglob : ((σ.fragt (.inr (.inr g))).lese Λ [.inr g]).globs g = σ₁.globs g := by
    rw [hs₁]
    exact hg.2 g hss.1
  refine ⟨(σ.fragt (.inr (.inr g))).lese Λ [.inr g], Nat.le_trans (Nat.le_succ _) (lese_laenge (σ.fragt _) _ _), hg, ⟨hks, hss.2, hrest⟩, fun R O' hQ => ?_⟩
  have hsv : O'.sichtbar g (σ.fragt (.inr (.inr g))) = true := by
    rw [sichtbar_gleich (σ := σ.fragt (.inr (.inr g))) (W := (M.weltVon u).fragt (.inr (.inr g))) hRL hQ g hss.1 hg]
    exact hvis
  have h1 := semV_awaits O' passes R g payload hp hLg hat rest k σ ρ hsv
  rw [hglob] at h1
  exact ZErg.folgt_of_eq h1


end Gabbro.Grammatik
