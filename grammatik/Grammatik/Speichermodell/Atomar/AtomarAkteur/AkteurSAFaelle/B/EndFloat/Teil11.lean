module
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil2aEndFloat
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil11
import all Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil11

public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil11Basis
public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil10

@[expose] public section

namespace Gabbro.Grammatik
theorem akteurSA_endeGleitNarrowOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
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
  FadenSA P O passes Q S lok Tg m zyk
      (N.faeden
        u)
      (N.weltVon
        u) ∧
    LogOk P
      (N.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  subst hs₁
  refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.ende rest) _ Λ e.orte
    (fun hok => by
      obtain ⟨_, hss⟩ := hok
      obtain ⟨hes, _, _⟩ := teile2 hss
      exact expr_stabilX (hFS _) e hes)
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss⟩ := hok
  obtain ⟨_, hkr⟩ := and_teile hks
  obtain ⟨_, _, hrS⟩ := teile2 hss
  have hv' : gleitPasst lo hi (eval σ e σ ρ).x = some v := by
    rw [eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ]; exact hv
  exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
    ⟨hkr, hrS⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
      rw [semHA_endeGleitNarrowOk S O' U A passes R e lo hi sonst rest σ0 ρ v
        (by rw [hσ0]; exact hv'), hσ0])⟩


theorem akteurSA_endeGleitNarrowElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
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
  FadenSA P O passes Q S lok Tg m zyk
      (N.faeden
        u)
      (N.weltVon
        u) ∧
    LogOk P
      (N.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  subst hs₁
  refine ⟨fadenSA_lese hF hhead ρ (.ende sonst) _ Λ e.orte
    (fun hok => by
      obtain ⟨_, hss⟩ := hok
      obtain ⟨hes, _, _⟩ := teile2 hss
      exact expr_stabilX (hFS _) e hes)
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss⟩ := hok
  obtain ⟨hkS, _⟩ := and_teile hks
  obtain ⟨_, hsS, _⟩ := teile2 hss
  have hn' : gleitPasst lo hi (eval σ e σ ρ).x = none := by
    rw [eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ]; exact hn
  refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
    ⟨hkS, hsS⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
  have h1 := semHA_endeGleitNarrowElse S O' U A passes R e lo hi sonst rest σ0 ρ
    (by rw [hσ0]; exact hn')
  rw [hσ0] at h1
  exact h1


end Gabbro.Grammatik
