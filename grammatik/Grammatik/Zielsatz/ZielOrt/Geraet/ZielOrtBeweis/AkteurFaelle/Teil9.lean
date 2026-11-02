module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1a
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil8

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteur_dannRetBind {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (lk : Bool) (Γk : Ctx) (Λk Λk'' : List (Res D)) (e : ErgExpr D Γk Λk (vertragVon D (M.faeden u).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden u).kopf.f)))
  (restk : Block D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk Λk'')
  (kk : GRest D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk'') (ρ : Env D Γk)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.dann (Block.cons (Stmt.ret e hperm) restk) kk)⟩ :
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
  FadenOk P O passes
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
  have hok := okZ_dann_cons (kopf_okZ hF.1 hhead)
  have hens := pop_ens hK hF.1 hhead e hok.2.1
    (fun R σ => semZ_dannRet O passes R e hperm restk kk σ ρ)
  have hSt := hF.2
  rw [hpop] at hSt
  obtain ⟨hWc, hSt'⟩ := hSt
  have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
    rcases hcaller with h | ⟨n, err, h⟩
    · exact h
    · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
      rw [h] at hokc
      exact hokc.elim
  refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
    (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
    (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
    logOk_rueck hL hens⟩

set_option maxHeartbeats 4000000 in
theorem akteur_rueckConsBind {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (lk : Bool) (Γk : Ctx) (Λk : List (Res D)) (e : ErgExpr D Γk Λk (vertragVon D (M.faeden u).kopf.f).erg)
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
  FadenOk P O passes
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
  have hok := okZ_ende_cons (kopf_okZ hF.1 hhead)
  have hens := pop_ens hK hF.1 hhead e hok.2.1
    (fun R σ => semZ_rueckCons O passes R e hperm restk σ ρ)
  have hSt := hF.2
  rw [hpop] at hSt
  obtain ⟨hWc, hSt'⟩ := hSt
  have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
    rcases hcaller with h | ⟨n, err, h⟩
    · exact h
    · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
      rw [h] at hokc
      exact hokc.elim
  refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
    (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
    (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
    logOk_rueck hL hens⟩

end Gabbro.Grammatik
