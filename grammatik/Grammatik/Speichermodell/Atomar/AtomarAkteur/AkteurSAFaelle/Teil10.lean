module

public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Teil9

@[expose] public section

namespace Gabbro.Grammatik

/-- Reading never touches the memory (local copy: the general lemma lives
    downstream of this module's import chain). -/
theorem lese_speicher_sa {D : Deklaration} (σ : World D) (Λ : List (Res D))
    (X : List (D.Tab ⊕ D.Glob)) : (σ.lese Λ X).speicher = σ.speicher := rfl

set_option maxHeartbeats 4000000 in
theorem akteurSA_verbrauchWeiter {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab)
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
  (mr : Int) (hm : mr = (eval σ₃ mass σ₃ ρ).n)
  (neu : List (Ereignis D)) (hneu : σ₃.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenSA P O passes Q S lok Tg m zyk
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
                                  body rest mr k))⟩ :
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
                                  body rest mr k))⟩ :
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
                                    body rest mr k))⟩ :
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
  refine ⟨fadenSA_lokalQ hF hhead (.cons v ρ)
    (.dann body (.verbrauchRest t member edge inv bound mass body rest mr k)) σ₃.spur
    fun σ HX hfx hkx hg hok => ?_, hL⟩
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hok
  have hX₁ : ∀ c ∈ inv.orte, c ∈ stabilS P S lok (M.faeden u).kopf.f Λ ∨ Tg c :=
    fun c hc => expr_stabilX (hFS _) inv hinv c hc
  have hX₂ : ∀ c ∈ member.orte ++ edge.orte, c ∈ stabilS P S lok (M.faeden u).kopf.f Λ ∨ Tg c := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact expr_stabilX (hFS _) member hmem c hc
    · exact expr_stabilX (hFS _) edge hedge c hc
  have hX₃ : ∀ c ∈ mass.orte, c ∈ stabilS P S lok (M.faeden u).kopf.f Λ ∨ Tg c :=
    fun c hc => expr_stabilX (hFS _) mass hmass c hc
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese3_schritt hfx hkx Λ inv.orte (member.orte ++ edge.orte)
    mass.orte (M.weltVon u).speicher
  have g₁ : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte)
      (mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher) ((M.weltVon u).lese Λ inv.orte) :=
    mischT_gleichAuf hg hX₁ Λ Λ
  have g₁W : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte)
      (mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher) (M.weltVon u) :=
    g₁.trans (GleichAuf.vonSpeicher (lese_speicher_sa _ _ _))
  have g₂ : GleichAuf ((stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte) ++ (member.orte ++ edge.orte))
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      ((M.weltVon u).lese Λ (member.orte ++ edge.orte)) :=
    mischT_gleichAuf g₁W
      (fun c hc => (hX₂ c hc).elim (fun h => Or.inl (List.mem_append_left _ h)) Or.inr) Λ Λ
  have g₂W : GleichAuf ((stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte) ++ (member.orte ++ edge.orte))
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      (M.weltVon u) :=
    g₂.trans (GleichAuf.vonSpeicher (lese_speicher_sa _ _ _))
  have g₃ : GleichAuf (((stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte) ++ (member.orte ++ edge.orte)) ++
        mass.orte)
      (mischT Tg mass.orte
        ((mischT Tg (member.orte ++ edge.orte)
          ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
          (M.weltVon u).speicher).lese Λ mass.orte)
        (M.weltVon u).speicher)
      ((M.weltVon u).lese Λ mass.orte) :=
    mischT_gleichAuf g₂W
      (fun c hc => (hX₃ c hc).elim
        (fun h => Or.inl (List.mem_append_left _ (List.mem_append_left _ h))) Or.inr) Λ Λ
  have g₁m : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte)
      (mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher) σ₁ :=
    g₁.trans (GleichAuf.vonSpeicher (by simp only [hs₁, lese_speicher_sa]))
  have g₂m : GleichAuf ((stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte) ++ (member.orte ++ edge.orte))
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      σ₂ :=
    g₂.trans (GleichAuf.vonSpeicher (by simp only [hs₂, hs₁, lese_speicher_sa]))
  have g₃m : GleichAuf (((stabilS P S lok (M.faeden u).kopf.f Λ ++ inv.orte) ++ (member.orte ++ edge.orte)) ++
        mass.orte)
      (mischT Tg mass.orte
        ((mischT Tg (member.orte ++ edge.orte)
          ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
          (M.weltVon u).speicher).lese Λ mass.orte)
        (M.weltVon u).speicher)
      σ₃ :=
    g₃.trans (GleichAuf.vonSpeicher (by simp only [hs₃, hs₂, hs₁, lese_speicher_sa]))
  have eM : ∀ k, wahr? (eval
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      member
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      (.cons k ρ)) =
      wahr? (eval σ₂ member σ₂ (.cons k ρ)) := by
    intro k
    rw [eval_gleichAuf member (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) g₂m
      (.cons k ρ)]
  have eE : ∀ j k, wahr? (eval
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      edge
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      (.cons j (.cons k ρ))) =
      wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ))) := by
    intro j k
    rw [eval_gleichAuf edge (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) g₂m
      (.cons j (.cons k ρ))]
  have hW : (fun k => wahr? (eval
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      member
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      (.cons k ρ))) =
      (fun k => wahr? (eval σ₂ member σ₂ (.cons k ρ))) := funext eM
  have hE : (fun j k => wahr? (eval
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      edge
      (mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher)
      (.cons j (.cons k ρ)))) =
      (fun j k => wahr? (eval σ₂ edge σ₂ (.cons j (.cons k ρ)))) :=
    funext fun j => funext fun k => eE j k
  refine ⟨mischT Tg mass.orte
      ((mischT Tg (member.orte ++ edge.orte)
        ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
        (M.weltVon u).speicher).lese Λ mass.orte)
      (M.weltVon u).speicher,
    HX', hfx', hkx',
    hsub,
    Nat.le_trans (mischT_laenge Tg inv.orte σ Λ (M.weltVon u).speicher)
      (Nat.le_trans
        (mischT_laenge Tg (member.orte ++ edge.orte)
          (mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher) Λ (M.weltVon u).speicher)
        (lese_laenge
          (mischT Tg (member.orte ++ edge.orte)
            ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ
              (member.orte ++ edge.orte))
            (M.weltVon u).speicher) Λ mass.orte)),
    GleichAuf.mono
      (fun _ h => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h)))
      (g₃.trans (GleichAuf.vonSpeicher rfl)),
    ⟨hb, hbS, hmem, hedge, hinv, hmass, hb, hbS, hk⟩,
    fun R O' U A hPX hHA hQ => ZErgG.folgt_of_eq (by
      obtain ⟨e₁, e₂, e₃⟩ := hrec A hPX hHA
      have hwA : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true := by
        rw [e₁, eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) g₁m ρ]
        exact hw
      obtain ⟨b, hsel⟩ : ∃ b, verbrauchSelA A t member edge (leseBA A inv σ ρ).1 ρ =
          (mischT Tg (member.orte ++ edge.orte)
            ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
            (M.weltVon u).speicher, some v, b) := by
        refine ⟨(verbrauchSelA A t member edge (leseBA A inv σ ρ).1 ρ).2.2, ?_⟩
        have h1 : (leseBA A inv σ ρ).1 =
            mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher := e₁
        rw [h1]
        simp only [verbrauchSelA]
        refine Prod.ext ?_ (Prod.ext ?_ rfl)
        · exact e₂
        · exact (congrArg (fun σr : World D =>
            verbrauchWahl (alleIndizes (D.count t))
              (fun k => wahr? (eval σr member σr (.cons k ρ)))
              (fun j k => wahr? (eval σr edge σr (.cons j (.cons k ρ))))
              (fun j k => decide (j.n = k.n))) e₂).trans
            ((congrFun
              (congr (congrArg (verbrauchWahl (alleIndizes (D.count t))) hW) hE)
              (fun j k => decide (j.n = k.n))).trans hv)
      have hmA : (eval
          (leseA A
            (mischT Tg (member.orte ++ edge.orte)
              ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
              (M.weltVon u).speicher) Λ mass.orte)
          mass
          (leseA A
            (mischT Tg (member.orte ++ edge.orte)
              ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
              (M.weltVon u).speicher) Λ mass.orte) ρ).n = mr := by
        rw [e₃, eval_gleichAuf mass (fun _ h => List.mem_append_right _ h) g₃m ρ]
        exact hm.symm
      have hsem := semHA_verbrauchWeiter S O' U A passes R t member edge inv bound mass body rest k σ ρ
        hwA
        (mischT Tg (member.orte ++ edge.orte)
          ((mischT Tg inv.orte (σ.lese Λ inv.orte) (M.weltVon u).speicher).lese Λ (member.orte ++ edge.orte))
          (M.weltVon u).speicher)
        v b mr hsel hmA
      rw [e₃] at hsem
      exact hsem)⟩

end Gabbro.Grammatik
