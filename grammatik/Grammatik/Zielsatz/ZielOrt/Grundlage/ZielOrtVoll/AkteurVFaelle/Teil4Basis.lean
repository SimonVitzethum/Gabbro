module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Teil3

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_dannBind {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bind e rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (eval σ₁ e σ₁ ρ) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (eval σ₁ e σ₁ ρ) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (eval σ₁ e σ₁ ρ) ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
  refine ⟨fadenV_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [blockOrteP, List.append_subset] at hss
  have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
    rw [hs₁]; exact eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ
  refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R O' => ?_⟩
  have h1 := semV_dannBind O' passes R e rest k σ ρ
  rw [he'] at h1
  exact ZErg.folgt_of_eq h1

set_option maxHeartbeats 4000000 in
theorem akteurV_dannNarrowOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int) (e : Expr D Γ Λ (Ty.int lo hi))
  (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo' hi' :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.narrow e lo' hi' sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.int lo' hi' :: Γ,
                                (⟨Λ,
                                    (Env.cons
                                        { n := (eval σ₁ e σ₁ ρ).n, lo_le := h.left, le_hi := h.right : Zahl lo' hi' } ρ,
                                      GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.int lo' hi' :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo' hi' :: Γ) Λ)⟩ :
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
                            (⟨Ty.int lo' hi' :: Γ,
                                (⟨Λ,
                                    (Env.cons
                                        { n := (eval σ₁ e σ₁ ρ).n, lo_le := h.left, le_hi := h.right : Zahl lo' hi' } ρ,
                                      GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.int lo' hi' :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo' hi' :: Γ) Λ)⟩ :
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
                              (⟨Ty.int lo' hi' :: Γ,
                                  (⟨Λ,
                                      (Env.cons
                                          { n := (eval σ₁ e σ₁ ρ).n, lo_le := h.left, le_hi := h.right : Zahl lo' hi' }
                                          ρ,
                                        GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (Ty.int lo' hi' :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo' hi' :: Γ) Λ)⟩ :
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
  refine ⟨fadenV_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  obtain ⟨_, hkr⟩ := and_teile hks
  obtain ⟨hes, _, hrS⟩ := teile2 hss
  have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
    rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
  have h' : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by rw [he']; exact h
  refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩, fun R O' => ?_⟩
  have h1 := semV_narrowOk O' passes R e lo' hi' sonst rest k σ ρ h'
  have hz : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ :
      Wert D (.int lo' hi')) = ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ := by
    simp only [he']
  rw [hz] at h1
  exact ZErg.folgt_of_eq h1


set_option maxHeartbeats 4000000 in
theorem akteurV_dannNarrowRequired {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (lo hi lo' hi' : Int)
  (e : Expr D Γ Λ (.int lo hi))
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrowRequired e lo' hi' rest) k⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte)
  (h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur)
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  let next : RufMaschineG D :=
    { speicher := M.speicher,
      faeden := rufUpdateG M.faeden u
        { stapel := (M.faeden u).stapel,
          kopf := { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho,
            s0 := (M.faeden u).kopf.s0,
            rest := ⟨l, .int lo' hi' :: Γ, Λ,
              .cons ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ ρ, .dann rest (.schrumpf k)⟩ },
          spur := σ₁.spur, log := (M.faeden u).log },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start }
  FadenV P O passes (next.faeden u) (next.weltVon u) ∧ LogOk P (next.faeden u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenV_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [blockOrteP, List.append_subset] at hss
  obtain ⟨hes, hrS⟩ := hss
  have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
    rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
  have h' : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by rw [he']; exact h
  refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hrS, hrest⟩, fun R O' => ?_⟩
  have h1 : semV O' passes R (.dann (.narrowRequired e lo' hi' rest) k) σ ρ =
      semV O' passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ ρ) := by
    rw [semV_dann]
    simp only [execBlock]
    rw [dif_pos h']
    rfl
  have hz : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ :
      Wert D (.int lo' hi')) = ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ := by
    simp only [he']
  rw [hz] at h1
  exact ZErg.folgt_of_eq h1



end Gabbro.Grammatik
