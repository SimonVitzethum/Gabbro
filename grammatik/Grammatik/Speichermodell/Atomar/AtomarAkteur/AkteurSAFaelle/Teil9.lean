module

public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Teil8

@[expose] public section

namespace Gabbro.Grammatik

section VerbrauchTransport

variable {D : Deklaration} {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
  {Tg : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} {Λ : List (Res D)}

/-- **Two sequential atomic reads through one record extension.** After
    reading `X₁` then `X₂` (both answered with the machine memory `s`),
    every environment repeating the record answers the nested reads with
    the mixed worlds. This is the transport of the two G7 read premises
    (`verbrauchWahl` at the plain `member`/`edge` world, like
    `akteurSA_travNext`'s single `hσ0` rewrite but for the second read). -/
theorem lese2_schritt {HX : List (XEintrag D)} (hf : FunkX HX)
    {σ : World D} (hk : KurzX σ.spur.length HX) (Λr : List (Res D))
    (X₁ X₂ : List (D.Tab ⊕ D.Glob)) (s : Speicher D) :
    ∃ HX' : List (XEintrag D), FunkX HX' ∧
      KurzX ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂).spur.length HX' ∧
      (∀ e ∈ HX, e ∈ HX') ∧
      (∀ A : AUmwelt D, PasstX Tg A HX' → HavocA Tg A →
        leseA A σ Λr X₁ = mischT Tg X₁ (σ.lese Λr X₁) s ∧
        leseA A (mischT Tg X₁ (σ.lese Λr X₁) s) Λr X₂ =
          mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s) := by
  obtain ⟨HX₁, hfx₁, hkx₁, hsub₁, hrec₁⟩ := lese_schritt Tg hf hk Λr X₁ s
  have hk₁ : KurzX (mischT Tg X₁ (σ.lese Λr X₁) s).spur.length HX₁ := by
    rw [mischT_spur]; exact hkx₁
  obtain ⟨HX₂, hfx₂, hkx₂, hsub₂, hrec₂⟩ := lese_schritt Tg hfx₁ hk₁ Λr X₂ s
  refine ⟨HX₂, hfx₂, hkx₂, fun e he => hsub₂ _ (hsub₁ _ he), fun A hPX hHA => ⟨?_, ?_⟩⟩
  · exact hrec₁ A (passtX_teil (fun e he => hsub₂ _ he) hPX) hHA
  · exact hrec₂ A hPX hHA

/-- **Three sequential atomic reads through one record extension**: the
    invariant read, the `member`/`edge` selection read and the measure
    read of a consuming step (`verbrauchWeiter`). -/
theorem lese3_schritt {HX : List (XEintrag D)} (hf : FunkX HX)
    {σ : World D} (hk : KurzX σ.spur.length HX) (Λr : List (Res D))
    (X₁ X₂ X₃ : List (D.Tab ⊕ D.Glob)) (s : Speicher D) :
    ∃ HX' : List (XEintrag D), FunkX HX' ∧
      KurzX ((mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s).lese Λr X₃).spur.length HX' ∧
      (∀ e ∈ HX, e ∈ HX') ∧
      (∀ A : AUmwelt D, PasstX Tg A HX' → HavocA Tg A →
        leseA A σ Λr X₁ = mischT Tg X₁ (σ.lese Λr X₁) s ∧
        leseA A (mischT Tg X₁ (σ.lese Λr X₁) s) Λr X₂ =
          mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s ∧
        leseA A (mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s) Λr X₃ =
          mischT Tg X₃ ((mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s).lese Λr X₃) s) := by
  obtain ⟨HX₂, hfx₂, hkx₂, hsub₂, hrec₂⟩ := lese2_schritt hf hk Λr X₁ X₂ s
  have hk₂ : KurzX (mischT Tg X₂ ((mischT Tg X₁ (σ.lese Λr X₁) s).lese Λr X₂) s).spur.length HX₂ := by
    rw [mischT_spur]; exact hkx₂
  obtain ⟨HX₃, hfx₃, hkx₃, hsub₃, hrec₃⟩ := lese_schritt Tg hfx₂ hk₂ Λr X₃ s
  refine ⟨HX₃, hfx₃, hkx₃, fun e he => hsub₃ _ (hsub₂ _ he), fun A hPX hHA => ⟨?_, ?_, ?_⟩⟩
  · exact (hrec₂ A (passtX_teil (fun e he => hsub₃ _ he) hPX) hHA).1
  · exact (hrec₂ A (passtX_teil (fun e he => hsub₃ _ he) hPX) hHA).2
  · exact hrec₃ A hPX hHA

end VerbrauchTransport

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.consumeTraverse t member edge inv bound mass body) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body
                                  ((D.count t).toNat + bound.toNat + 1) (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
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
                                (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body
                                  ((D.count t).toNat + bound.toNat + 1) (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.weltVon
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
                                  (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body
                                    ((D.count t).toNat + bound.toNat + 1) (GRest.dann rest k))⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenSA_lokal hF hhead ρ (.verbrauch t member edge inv bound mass body
    ((D.count t).toNat + bound.toNat + 1) (.dann rest k))
    (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
  simp only [stmtOrteP, List.append_subset] at hss
  exact ⟨rfl, hg, ⟨hss.1, hss.2.1, hss.2.2.1, hss.2.2.2.1, hks, hss.2.2.2.2, hrest⟩,
    fun R O' U A => ZErgG.folgt_of_eq
      (semHA_dannVerbrauch S O' U A passes R t member edge inv bound mass body rest k σ ρ)⟩

end Gabbro.Grammatik
