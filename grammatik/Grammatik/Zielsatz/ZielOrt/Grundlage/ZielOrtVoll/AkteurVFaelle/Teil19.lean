module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Teil18

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_dannVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O)
  (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (t : D.Tab)
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
  FadenV P O passes
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
  refine ⟨fadenV_lokal hF hhead ρ (.verbrauch t member edge inv bound mass body
    ((D.count t).toNat + bound.toNat + 1) (.dann rest k))
    (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
  simp only [stmtOrteP, List.append_subset] at hss
  exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hss.2.1, hss.2.2.1, hss.2.2.2.1, hks, hss.2.2.2.2, hrest⟩,
    fun R O' => ZErg.folgt_of_eq
      (semV_dannVerbrauch O' passes R t member edge inv bound mass body rest k σ ρ)⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_verbrauchWeiter {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O)
  (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ inv.orte) (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
  (v : Wert D (.index (D.count t)))
  (hv : verbrauchWahl (alleIndizes (D.count t))
    (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ)))
    (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))))
    (fun j k => decide (j.n = k.n)) = some v)
  (σ₃ : World D) (hs₃ : σ₃ = σ₂.lese Λ mass.orte)
  (m : Int) (hm : m = (eval σ₃ mass σ₃ ρ).n)
  (neu : List (Ereignis D)) (hneu : σ₃.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨true,
                            (⟨Ty.index (D.count t) :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann body (GRest.verbrauchRest t member edge inv bound mass
                                  body rest m k))⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.index (D.count t) :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₃.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨true,
                            (⟨Ty.index (D.count t) :: Γ,
                                (⟨Λ, (Env.cons v ρ, GRest.dann body (GRest.verbrauchRest t member edge inv bound mass
                                  body rest m k))⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (Ty.index (D.count t) :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₃.spur, log := (M.faeden u).log : RufFadenG D },
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
                          (⟨true,
                              (⟨Ty.index (D.count t) :: Γ,
                                  (⟨Λ, (Env.cons v ρ, GRest.dann body (GRest.verbrauchRest t member edge inv bound mass
                                    body rest m k))⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (Ty.index (D.count t) :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ)
                                          Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₃.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann body (.verbrauchRest t member edge inv bound mass body rest m k))
    σ₃.spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hok
  have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
    rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
    exact hw
  have hg1 : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ inv.orte) σ₁ := by
    rw [hs₁]; exact hg.lese Λ Λ inv.orte inv.orte
  have hg2 : GleichAuf (fussOrte P (M.faeden u).kopf.f)
      ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) σ₂ := by
    rw [hs₂]; exact hg1.lese Λ Λ (member.orte ++ edge.orte) (member.orte ++ edge.orte)
  have eM : ∀ k, wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ)) =
      wahr? (eval σ₂ member σ₂ (.cons k ρ)) := by
    intro k
    rw [eval_gleichAuf member (fun _ h => hmem h) hg2 (.cons k ρ)]
  have eE : ∀ j k, wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) edge
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons j (.cons k ρ))) =
      wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))) := by
    intro j k
    rw [eval_gleichAuf edge (fun _ h => hedge h) hg2 (.cons j (.cons k ρ))]
  have hW : (fun k => wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ))) =
      (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ))) := funext eM
  have hE : (fun j k => wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) edge
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons j (.cons k ρ)))) =
      (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ)))) :=
    funext fun j => funext fun k => eE j k
  have hm' : (eval ((((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))).lese Λ mass.orte) mass
      ((((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))).lese Λ mass.orte) ρ).n = m := by
    have hg3 : GleichAuf (fussOrte P (M.faeden u).kopf.f)
        ((((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))).lese Λ mass.orte) σ₃ := by
      rw [hs₃]; exact hg2.lese Λ Λ mass.orte mass.orte
    rw [eval_gleichAuf mass (fun _ h => hmass h) hg3 ρ]
    exact hm.symm
  obtain ⟨b, hsel⟩ : ∃ b, verbrauchSel t member edge (σ.lese Λ inv.orte) ρ =
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)), some v, b) := by
    refine ⟨_, ?_⟩
    simp only [verbrauchSel]
    refine ⟨rfl, ?_, rfl⟩
    rw [hW, hE]
    exact hv
  exact ⟨((((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))).lese Λ mass.orte),
    Nat.le_trans (Nat.le_trans (lese_laenge _ _ _) (lese_laenge _ _ _)) (lese_laenge _ _ _), hg,
    ⟨hb, hbS, hmem, hedge, hinv, hmass, hb, hbS, hk⟩,
    fun R O' => ZErg.folgt_of_eq (semV_verbrauchWeiter O' passes R t member edge inv bound mass body rest k
      σ ρ hw' _ v b m hsel hm')⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_verbrauchLeer {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O)
  (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ inv.orte) (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
  (hleer : verbrauchWahl (alleIndizes (D.count t))
    (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ)))
    (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))))
    (fun j k => decide (j.n = k.n)) = none)
  (hkein : ((alleIndizes (D.count t)).all fun k =>
    !(wahr? (eval σ₂ member σ₂ (.cons k ρ)))) = true)
  (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
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
                                (⟨Λ, (ρ, k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
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
                                  (⟨Λ, (ρ, k)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenV_lokal hF hhead ρ k σ₂.spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hok
  have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
    rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
    exact hw
  have hg2 : GleichAuf (fussOrte P (M.faeden u).kopf.f)
      ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) σ₂ := by
    have hg1 : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ inv.orte) σ₁ := by
      rw [hs₁]; exact hg.lese Λ Λ inv.orte inv.orte
    rw [hs₂]; exact hg1.lese Λ Λ (member.orte ++ edge.orte) (member.orte ++ edge.orte)
  have eM : ∀ k, wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ)) =
      wahr? (eval σ₂ member σ₂ (.cons k ρ)) := by
    intro k
    rw [eval_gleichAuf member (fun _ h => hmem h) hg2 (.cons k ρ)]
  have eE : ∀ j k, wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) edge
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons j (.cons k ρ))) =
      wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))) := by
    intro j k
    rw [eval_gleichAuf edge (fun _ h => hedge h) hg2 (.cons j (.cons k ρ))]
  have hW : (fun k => wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ))) =
      (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ))) := funext eM
  have hE : (fun j k => wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) edge
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons j (.cons k ρ)))) =
      (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ)))) :=
    funext fun j => funext fun k => eE j k
  have hall : ((alleIndizes (D.count t)).all fun k =>
      !(wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
        (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ)))) = true := by
    have heq : (fun k => !(wahr? (eval ((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)) member
        (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte))) (.cons k ρ)))) =
        (fun k => !(wahr? (eval σ₂ member σ₂ (.cons k ρ)))) :=
      funext fun k => by rw [eM k]
    rw [heq]; exact hkein
  have hsel : verbrauchSel t member edge (σ.lese Λ inv.orte) ρ =
      (((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)), none, false) := by
    simp only [verbrauchSel]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hW, hE]; exact hleer
    · rw [hall]
  exact ⟨((σ.lese Λ inv.orte).lese Λ (member.orte ++ edge.orte)),
    Nat.le_trans (lese_laenge _ _ _) (lese_laenge _ _ _), hg, hk,
    fun R O' => ZErg.folgt_of_eq (semV_verbrauchLeer O' passes R t member edge inv bound mass body rest k
      σ ρ hw' _ hsel)⟩

end Gabbro.Grammatik
