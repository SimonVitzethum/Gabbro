module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.AkteurGFaelle.Tail.Teil16

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurG_rueckConsBind {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (lk : Bool) (Γk : Ctx) (Λk : List (Res D))
  (e : ErgExpr D Γk Λk (vertragVon D (M.faeden u).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden u).kopf.f)))
  (restk : Endblock D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk) (ρ : Env D Γk)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.ende (Endblock.cons (Stmt.ret e hperm) restk))⟩ :
                (Λ : List (Res D)) × Env D Γk × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γk Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden u).stapel = caller :: rst) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (τ : Ty) (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
  (hcaller :
    caller.rest =
        (⟨l,
            (⟨Γ,
                (⟨Λ, (ρc, GRest.wartet restb k)⟩ :
                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
          (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) ∨
      ∃ n err,
        caller.rest =
          (⟨l,
              (⟨Γ,
                  (⟨Λ, (ρc, GRest.wartetSonst n err restb k)⟩ :
                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
            (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ))
  (hΛ : HeldIn Λk (offen (M.faeden u).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon u).lese Λk e.orte) (g : D.Fn)
  (hfg : (M.faeden u).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden u).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden u).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (he : D.erg g = some τ) (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden u).spur) :
  FadenG P O passes
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst,
                  kopf :=
                    { f := caller.f, rho := caller.rho, s0 := caller.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                  (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst,
                  kopf :=
                    { f := caller.f, rho := caller.rho, s0 := caller.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                  (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := s1.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := rst,
                    kopf :=
                      { f := caller.f, rho := caller.rho, s0 := caller.s0,
                        rest :=
                          (⟨l,
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  subst hfg hs0 hs1 hv
  subst hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  have hok := okG_ende_cons (kopfG_okG hF.1 hhead)
  have hens := popG_ens hO hRL hK hF.1 hhead e hok.2.1
    (fun O' R σ => semV_rueckCons O' passes R e hperm restk σ ρ)
  have hSt := hF.2
  rw [hpop] at hSt
  obtain ⟨hWc, hSt'⟩ := hSt
  refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
    (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
    (fun hokc => by
      rcases hcaller with hc | ⟨n, err, hc⟩
      · have h' := rest_okG hc hokc
        exact ⟨h'.1, h'.2.1, h'.2.2⟩
      · have h' := rest_okG hc hokc
        exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
    (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
    logOk_rueck hL hens⟩

set_option maxHeartbeats 4000000 in
theorem akteurG_dannRegLies {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (r : D.Reg)
  (hk : (D.rklasse r).lesbar = true) (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regRead r hk rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon u).fragt (Sum.inr (Sum.inl r)))) = some v)
  (hz : D.rzusage r v = true) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenG P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.rtyp r :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.rtyp r :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden u).spur, log := (M.faeden u).log :
                  RufFadenG D },
            lauf := M.lauf ++ rufEigenG u [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start :
            RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.rtyp r :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.rtyp r :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden u).spur, log := (M.faeden u).log :
                  RufFadenG D },
            lauf := M.lauf ++ rufEigenG u [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start :
            RufMaschineG D }.weltVon
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
                              (⟨D.rtyp r :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (D.rtyp r :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden u).spur, log := (M.faeden u).log :
                    RufFadenG D },
              lauf := M.lauf ++ rufEigenG u [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start :
              RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenG_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP] at hss
  refine ⟨σ.fragt (.inr (.inl r)), Nat.le_succ _, hg, ⟨hks.2, hss, hrest⟩, fun R O' hQ => ?_⟩
  have hrl : O'.regLies r (σ.fragt (.inr (.inl r))) = O.regLies r ((M.weltVon u).fragt (.inr (.inl r))) :=
    regLies_gleich hRL hQ r (regP_ok hks.1) hg
  exact ZErg.folgt_of_eq
    (semV_regLies O' passes R r hk rest k σ ρ v (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hz)

set_option maxHeartbeats 4000000 in
theorem akteurG_dannRegLiesElseWahr {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (r : D.Reg)
  (hk : (D.rklasse r).lesbar = true) (zusage : Expr D (D.rtyp r :: Γ) Λ Ty.bool)
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
  (hw : wahr? (eval σ₁ zusage σ₁ (Env.cons v ρ)) = true) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenG P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.rtyp r :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.rtyp r :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
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
                            (⟨D.rtyp r :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.rtyp r :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
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
                              (⟨D.rtyp r :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (D.rtyp r :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
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
  refine ⟨fadenG_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  have hgq : GleichAuf _ (σ.fragt (.inr (.inl r))) ((M.weltVon u).fragt (.inr (.inl r))) := hg
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP, List.append_subset] at hss
  obtain ⟨⟨hzS, _⟩, hrS⟩ := hss
  have hw' : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) =
      true := by
    rw [eval_gleichAuf zusage (fun _ h => hzS h) (hgq.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
    exact hw
  refine ⟨(σ.fragt (.inr (.inl r))).lese Λ zusage.orte, Nat.le_trans (Nat.le_succ _) (lese_laenge (σ.fragt _) _ _), hg, ⟨hks.2.2, hrS, hrest⟩,
    fun R O' hQ => ?_⟩
  have hrl : O'.regLies r (σ.fragt (.inr (.inl r))) = O.regLies r ((M.weltVon u).fragt (.inr (.inl r))) :=
    regLies_gleich hRL hQ r (regP_ok hks.1) hg
  exact ZErg.folgt_of_eq (semV_regLiesElseWahr O' passes R r hk zusage sonst rest k σ ρ v
    (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw')

end Gabbro.Grammatik
