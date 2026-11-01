module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAxBeweis
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Teil9

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurA_dannGleit {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) (hK : ∀ (f : D.Fn), KoerperGutA P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (l₁ h₁ l₂ h₂ : Int × Int) (op : GleitOp) (a : Expr D Γ Λ (Ty.fl l₁ h₁))
  (b : Expr D Γ Λ (Ty.fl l₂ h₂)) (lo hi : Int × Int)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.float op a b lo hi rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ (a.orte ++ b.orte)) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) = some v) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenA P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                              (⟨Ty.fl lo hi :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenA_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  obtain ⟨haS, hbS, hrS⟩ := teile2 hss
  have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
  have hv' : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v := by
    rw [eval_gleichAuf a (fun _ h => haS h) hgl ρ, eval_gleichAuf b (fun _ h => hbS h) hgl ρ,
      ← hs₁]
    exact hv
  exact ⟨σ.lese Λ (a.orte ++ b.orte), lese_laenge _ _ _, hg, ⟨hks, hrS, hrest⟩,
    fun R O' => ZErg.folgt_of_eq (semV_gleit O' passes R op a b lo hi rest k σ ρ v hv')⟩

set_option maxHeartbeats 4000000 in
theorem akteurA_dannGleitLit {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) (hK : ∀ (f : D.Fn), KoerperGutA P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (q lo hi : Int × Int)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.floatLit q lo hi rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (Ty.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
  FadenA P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                              (⟨Ty.fl lo hi :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
              lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenA_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
    fun R O' => ZErg.folgt_of_eq (semV_gleitLit O' passes R q lo hi rest k σ ρ v hv)⟩

set_option maxHeartbeats 4000000 in
theorem akteurA_dannGleitVon {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) (hK : ∀ (f : D.Fn), KoerperGutA P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (l₁ h₁ : Int) (e : Expr D Γ Λ (Ty.int l₁ h₁)) (lo hi : Int × Int)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.floatOf e lo hi rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) = some v) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenA P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                              (⟨Ty.fl lo hi :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenA_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [blockOrteP, List.append_subset] at hss
  have hv' : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v := by
    rw [eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩,
    fun R O' => ZErg.folgt_of_eq (semV_gleitVon O' passes R e lo hi rest k σ ρ v hv')⟩

set_option maxHeartbeats 4000000 in
theorem akteurA_dannGleitNarrowOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) (hK : ∀ (f : D.Fn), KoerperGutA P passes Q f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (l₁ h₁ : Int × Int) (e : Expr D Γ Λ (Ty.fl l₁ h₁)) (lo hi : Int × Int)
  (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.floatNarrow e lo hi sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = some v) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenA P O passes Q
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                            (⟨Ty.fl lo hi :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
                              (⟨Ty.fl lo hi :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
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
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenA_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  obtain ⟨_, hkr⟩ := and_teile hks
  obtain ⟨hes, _, hrS⟩ := teile2 hss
  have hv' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v := by
    rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
    fun R O' => ZErg.folgt_of_eq (semV_gleitNarrowOk O' passes R e lo hi sonst rest k σ ρ v hv')⟩

end Gabbro.Grammatik
