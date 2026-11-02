module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Teil1

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteur_dannIteFalsch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (c : Expr D Γ Λ Ty.bool)
  (t e : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.ite c t e) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ c.orte) (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenOk P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann e (GRest.dann rest k))⟩ :
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
                                (⟨Λ, (ρ, GRest.dann e (GRest.dann rest k))⟩ :
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
                                  (⟨Λ, (ρ, GRest.dann e (GRest.dann rest k))⟩ :
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
  refine ⟨fadenOk_lokal hF hhead ρ (.dann e (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
  obtain ⟨_, he⟩ := and_teile hks
  obtain ⟨hc, _, heS⟩ := teile2 hss
  have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
    rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
  exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨he, heS, hrest⟩,
    fun R => ZErg.gleich_of_eq (semZ_iteFalsch O passes R c t e rest k σ ρ hw')⟩

set_option maxHeartbeats 4000000 in
theorem akteur_dannOnOptionSome {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int) (o : Expr D Γ Λ (Ty.opt n))
  (p : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ Λ')
  (a : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onOption o p a) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ o.orte) (v : Wert D (Ty.index n)) (hv : eval σ₁ o σ₁ ρ = some v)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenOk P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Ty.index n :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann p (GRest.dann rest k).schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.index n :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ)⟩ :
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
                            (⟨Ty.index n :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann p (GRest.dann rest k).schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.index n :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ)⟩ :
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
                              (⟨Ty.index n :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann p (GRest.dann rest k).schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (Ty.index n :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ)⟩ :
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
  refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
  obtain ⟨hp, _⟩ := and_teile hks
  obtain ⟨hc, hpS, _⟩ := teile2 hss
  have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v := by
    rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨hp, hpS, hrest⟩,
    fun R => ZErg.gleich_of_eq (semZ_optSome O passes R o p a rest k σ ρ v hv')⟩

set_option maxHeartbeats 4000000 in
theorem akteur_dannOnOptionNone {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int) (o : Expr D Γ Λ (Ty.opt n))
  (p : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ Λ')
  (a : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onOption o p a) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ o.orte) (hv : eval σ₁ o σ₁ ρ = none) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenOk P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
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
                                (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
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
                                  (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
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
  refine ⟨fadenOk_lokal hF hhead ρ (.dann a (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
  obtain ⟨_, ha⟩ := and_teile hks
  obtain ⟨hc, _, haS⟩ := teile2 hss
  have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none := by
    rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
  exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨ha, haS, hrest⟩,
    fun R => ZErg.gleich_of_eq (semZ_optNone O passes R o p a rest k σ ρ hv')⟩

set_option maxHeartbeats 4000000 in
theorem akteur_dannOnTagSome {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hK : ∀ (f : D.Fn), KoerperGut P O passes f) (hFrag : ∀ (f : D.Fn), (P.rumpf f).kOk = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (cs : List (Option Ty)) (v : Expr D Γ Λ (Ty.sum cs))
  (arms : Arms D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ' cs)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onTag v arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ v.orte) (τ : Ty)
  (b : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
  (hw :
    armWahlG arms (eval σ₁ v σ₁ ρ) =
      (⟨some τ, (b, nutz)⟩ :
        (c : Option Ty) × Block D (vertragVon D (M.faeden u).kopf.f) l (ArmCtx Γ c) Λ Λ' × Nutzlast D.Fn D.passt c))
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenOk P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
                                (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
                                  (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
  refine ⟨fadenOk_lokal hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
  simp only [stmtOrteP, List.append_subset] at hss
  have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩ := by
    rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
  exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
    ⟨armWahlG_kOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
    fun R => ZErg.gleich_of_eq (semZ_tagSome O passes R v arms rest k σ ρ τ b nutz hw')⟩

end Gabbro.Grammatik
