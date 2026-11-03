module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Tail.Teil19

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_verbrauchFort {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λ, (Env.cons i ρ, GRest.verbrauchRest t member edge inv bound mass body rest vor k)⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ mass.orte)
  (m' : Int) (hm' : m' = (eval σ₁ mass σ₁ ρ).n)
  (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
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
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
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
                                (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
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
                                  (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
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
  refine ⟨fadenV_lokal hF hhead ρ (.verbrauch t member edge inv bound mass body rest k) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hok
  have hm'' : (eval (σ.lese Λ mass.orte) mass (σ.lese Λ mass.orte) ρ).n = m' := by
    have hg1 : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ mass.orte) σ₁ := by
      rw [hs₁]; exact hg.lese Λ Λ mass.orte mass.orte
    rw [eval_gleichAuf mass (fun _ h => hmass h) hg1 ρ]
    exact hm'.symm
  exact ⟨σ.lese Λ mass.orte, lese_laenge _ _ _, hg,
    ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩,
    fun R O' => ZErg.folgt_of_eq (semV_verbrauchFort O' passes R t member edge inv bound mass body rest vor k
      i σ ρ (σ.lese Λ mass.orte) rfl m' hm'' hfall)⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_dannLeaveVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  {Λx : List (Res D)}
  (restb : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λx Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hleave : true = true)
  (hhead : (M.faeden u).kopf.rest =
    ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons ((.leave hleave) : Stmt D (vertragVon D (M.faeden u).kopf.f)
        true (.index (D.count t) :: Γ) Λx Λx) restb)
        (.verbrauchRest t member edge inv bound mass body rest vor k)⟩)
  (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
  (neu : List (Ereignis D))
  (hstep : (execStmt O passes keinRuf
      ((.leave hleave) : Stmt D (vertragVon D (M.faeden u).kopf.f)
        true (.index (D.count t) :: Γ) Λx Λx) (M.weltVon u)
      (.cons i ρ)) =
    Ausgang.leave (D := D) (V := vertragVon D (M.faeden u).kopf.f)
      hleave σ' ρ')
  (hneu : σ'.spur = neu ++ (M.faeden u).spur)
  (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
  (σm : World D) (hsm : σm = σ'.lese Λ mass.orte)
  (m' : Int) (hm' : m' = (eval σm mass σm ρ).n)
  (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
  (σ₁ : World D) (hs₁ : σ₁ = σm.lese Λ inv.orte)
  (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (neu₁ : List (Ereignis D))
  (hneu₁ : σ₁.spur = neu₁ ++ (M.faeden u).spur)
  (hΛ : HeldIn Λx (offen (M.faeden u).spur)) :
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
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u (neu ++ neu₁), start := M.start : RufMaschineG D }.faeden
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
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u (neu ++ neu₁), start := M.start : RufMaschineG D }.weltVon
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
                    spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u (neu ++ neu₁), start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  simp only [execStmt, Ausgang.leave.injEq] at hstep
  obtain ⟨hσ, hρ⟩ := hstep
  subst σ' ρ'
  subst σ₁
  refine ⟨fadenV_lokal hF hhead ρ k (σm.lese Λ inv.orte).spur (fun σ hg hok => ?_), hL⟩
  obtain ⟨_, _, hTR⟩ := hok
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hTR
  have hg1 : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ mass.orte) σm := by
    rw [hsm]; exact hg.lese Λ Λ mass.orte mass.orte
  have hm'' : (eval (σ.lese Λ mass.orte) mass (σ.lese Λ mass.orte) ρ).n = m' := by
    rw [eval_gleichAuf mass (fun _ h => hmass h) hg1 ρ]
    exact hm'.symm
  have hw'' : wahr? (eval ((σ.lese Λ mass.orte).lese Λ inv.orte) inv
      (((σ.lese Λ mass.orte).lese Λ inv.orte)) ρ) = true := by
    have hg2 : GleichAuf (fussOrte P (M.faeden u).kopf.f)
        ((σ.lese Λ mass.orte).lese Λ inv.orte) (σm.lese Λ inv.orte) :=
      hg1.lese Λ Λ inv.orte inv.orte
    rw [eval_gleichAuf inv (fun _ h => hinv h) hg2 ρ]
    exact hw
  exact ⟨((σ.lese Λ mass.orte).lese Λ inv.orte),
    Nat.le_trans (lese_laenge _ _ _) (lese_laenge _ _ _), hg, hk,
    fun R O' => ZErg.folgt_of_eq (semV_leaveVerbrauch O' passes R t member edge inv bound mass body rest vor k
      restb i σ ρ hleave (σ.lese Λ mass.orte) rfl m' hm'' hfall hw'')⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_dannNextVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
  (inv : Expr D Γ Λ .bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  {Λx : List (Res D)}
  (restb : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λx Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hnext : true = true)
  (hhead : (M.faeden u).kopf.rest =
    ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons ((.next hnext) : Stmt D (vertragVon D (M.faeden u).kopf.f)
        true (.index (D.count t) :: Γ) Λx Λx) restb)
        (.verbrauchRest t member edge inv bound mass body rest vor k)⟩)
  (σ' : World D) (ρ' : Env D (.index (D.count t) :: Γ))
  (neu : List (Ereignis D))
  (hstep : (execStmt O passes keinRuf
      ((.next hnext) : Stmt D (vertragVon D (M.faeden u).kopf.f)
        true (.index (D.count t) :: Γ) Λx Λx) (M.weltVon u)
      (.cons i ρ)) =
    Ausgang.next (D := D) (V := vertragVon D (M.faeden u).kopf.f)
      hnext σ' ρ')
  (hneu : σ'.spur = neu ++ (M.faeden u).spur)
  (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
  (σm : World D) (hsm : σm = σ'.lese Λ mass.orte)
  (m' : Int) (hm' : m' = (eval σm mass σm ρ'.tail).n)
  (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
  (neum : List (Ereignis D))
  (hneum : σm.spur = neum ++ (M.faeden u).spur)
  (hΛ : HeldIn Λx (offen (M.faeden u).spur)) :
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
                                (⟨Λ, (ρ'.tail, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σm.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u (neu ++ neum), start := M.start : RufMaschineG D }.faeden
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
                                (⟨Λ, (ρ'.tail, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σm.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u (neu ++ neum), start := M.start : RufMaschineG D }.weltVon
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
                                  (⟨Λ, (ρ'.tail, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σm.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u (neu ++ neum), start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  simp only [execStmt, Ausgang.next.injEq] at hstep
  obtain ⟨hσ, hρ⟩ := hstep
  subst σ' ρ'
  simp only [Env.tail] at hm' ⊢
  refine ⟨fadenV_lokal hF hhead ρ (.verbrauch t member edge inv bound mass body rest k) σm.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨_, _, hTR⟩ := hok
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := id hTR
  have hm'' : (eval (σ.lese Λ mass.orte) mass (σ.lese Λ mass.orte) ρ).n = m' := by
    have hg1 : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ mass.orte) σm := by
      rw [hsm]; exact hg.lese Λ Λ mass.orte mass.orte
    rw [eval_gleichAuf mass (fun _ h => hmass h) hg1 ρ]
    exact hm'.symm
  exact ⟨σ.lese Λ mass.orte, lese_laenge _ _ _, hg, hTR, fun R O' => ZErg.folgt_of_eq
    (semV_nextVerbrauch O' passes R t member edge inv bound mass body rest vor k restb i σ ρ hnext
      (σ.lese Λ mass.orte) rfl m' hm'' hfall)⟩

end Gabbro.Grammatik
