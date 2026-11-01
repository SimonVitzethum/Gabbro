module

public import Grammatik.Nichtinterferenz.Schritt

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem schrittK_von_blatt {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)
  {M : RufMaschineG D} {f : Faden} (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ') (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
  (ρ : Env D Γ) (hleaf : s.istBlatt = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons s rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
  (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = Ausgang.ok σ' ρ') (hneu : σ'.spur = neu ++ (M.faeden f).spur)
  (hk : ∀ (L : D.Lock) (h : List D.Lock), ¬Ereignis.nimmt L h ∈ neu) :
  kSchrittK P O passes (M.faeden f).kern M.speicher =
    some
      (({ speicher := σ'.speicher,
                faeden :=
                  rufUpdateG M.faeden f
                    { stapel := (M.faeden f).stapel,
                      kopf :=
                        { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                          rest :=
                            (⟨l,
                                (⟨Γ,
                                    (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                      (Λ : List (Res D)) ×
                                        Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                                  (Γ : Ctx) ×
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                              (l : Bool) ×
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                          RufRahmenG D },
                      spur := σ'.spur, log := (M.faeden f).log : RufFadenG D },
                lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
            f).kern,
        { speicher := σ'.speicher,
            faeden :=
              rufUpdateG M.faeden f
                { stapel := (M.faeden f).stapel,
                  kopf :=
                    { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ'.spur, log := (M.faeden f).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.speicher) := by
    kstart
    simp only [kr, kEnde, kEndeCons, GEntfaltbar_blatt s hleaf, hleaf]
    simp only [RufMaschineG.weltVon] at hstep
    simp only [hstep, kAusEnde, kLokal, RufFadenG.kern, RufRahmenG.kern]
    rfl

end Gabbro.Grammatik
