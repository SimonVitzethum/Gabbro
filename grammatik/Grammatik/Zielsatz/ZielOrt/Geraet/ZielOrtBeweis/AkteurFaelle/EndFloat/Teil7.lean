module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil2EndFloat
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil7
import all Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil7

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1a
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil6

@[expose] public section

namespace Gabbro.Grammatik

theorem akteur_endeGleitNarrowOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (l₁ h₁ : Int × Int) (e : Expr D Γ Λ (Ty.fl l₁ h₁)) (lo hi : Int × Int)
  (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)
   (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.floatNarrow e lo hi sonst rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = some v) (neu : List (Ereignis D))
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
  obtain ⟨_, hkr⟩ := and_teile hks
  obtain ⟨hes, _, hrS⟩ := teile2 hss
  have hv' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v := by
    rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS⟩,
    fun R => ZErg.gleich_of_eq (semZ_endeGleitNarrowOk O passes R e lo hi sonst rest σ ρ v hv')⟩


theorem akteur_endeGleitNarrowElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (l₁ h₁ : Int × Int) (e : Expr D Γ Λ (Ty.fl l₁ h₁)) (lo hi : Int × Int)
  (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ)
   (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.floatNarrow e lo hi sonst rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (hn : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = none)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :

  let N : RufMaschineG D := { speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.ende sonst)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
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
  refine ⟨fadenOk_lokal hF hhead ρ (.ende sonst) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss⟩ := hok
  obtain ⟨hkS, _⟩ := and_teile hks
  obtain ⟨hes, hsS, _⟩ := teile2 hss
  have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
    rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg,
    ⟨hkS, hsS⟩,
    fun R => ZErg.gleich_of_eq (semZ_endeGleitNarrowElse O passes R e lo hi sonst rest σ ρ hn')⟩


end Gabbro.Grammatik
