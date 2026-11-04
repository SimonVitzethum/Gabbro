module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil2EndFloat
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil6
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil6
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil6Basis
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil6Basis

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1a
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil5

@[expose] public section

namespace Gabbro.Grammatik

theorem akteur_endeGleitLit {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (q lo hi : Int × Int)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)
   (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.floatLit q lo hi rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (Ty.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :

  let N : RufMaschineG D := { speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.fl lo hi :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }
  FadenOk P O passes
      (N.faeden
        u)
      (N.weltVon
        u) ∧
    LogOk P
      (N.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.ende rest) (M.faeden u).spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss⟩ := hok
  exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss⟩,
    fun R => ZErg.gleich_of_eq (semZ_endeGleitLit O passes R q lo hi rest σ ρ v hv)⟩


theorem akteur_endeGleitVon {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (l₁ h₁ : Int) (e : Expr D Γ Λ (Ty.int l₁ h₁)) (lo hi : Int × Int)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)
   (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.floatOf e lo hi rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) = some v) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :

  let N : RufMaschineG D := { speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.fl lo hi :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }
  FadenOk P O passes
      (N.faeden
        u)
      (N.weltVon
        u) ∧
    LogOk P
      (N.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.ende rest) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss⟩ := hok
  simp only [endblockOrteP, List.append_subset] at hss
  have hv' : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v := by
    rw [eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2⟩,
    fun R => ZErg.gleich_of_eq (semZ_endeGleitVon O passes R e lo hi rest σ ρ v hv')⟩


end Gabbro.Grammatik
