module

public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Teil11

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannLeaveVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
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
                                (⟨Λ, (ρ, k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (σm.lese Λ inv.orte).spur, log := (M.faeden u).log : RufFadenG D },
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
                  spur := (σm.lese Λ inv.orte).spur, log := (M.faeden u).log : RufFadenG D },
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
                    spur := (σm.lese Λ inv.orte).spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u (neu ++ neu₁), start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  simp only [execStmt, Ausgang.leave.injEq] at hstep
  obtain ⟨hσ, hρ⟩ := hstep
  subst σ' ρ'
  subst σ₁
  refine ⟨fadenSA_lokalQ hF hhead ρ k ((σm.lese Λ inv.orte)).spur
    fun σ HX hfx hkx hg hok => ?_, hL⟩
  obtain ⟨_, _, hTR⟩ := hok
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hTR
  have hgΛ : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) :=
    gleichAuf_stabil_iff (fun L => restb.held_iff L) hg
  have hX₁ : ∀ c ∈ mass.orte, c ∈ stabilS P S lok (M.faeden u).kopf.f Λ ∨ Tg c :=
    fun c hc => expr_stabilX (hFS _) mass hmass c hc
  have hX₂ : ∀ c ∈ inv.orte, c ∈ stabilS P S lok (M.faeden u).kopf.f Λ ∨ Tg c :=
    fun c hc => expr_stabilX (hFS _) inv hinv c hc
  obtain ⟨HX', hfx', hkx', hsub, hrec⟩ := lese2_schritt hfx hkx Λ mass.orte inv.orte
    (M.weltVon u).speicher
  have g₁ : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++ mass.orte)
      (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) ((M.weltVon u).lese Λ mass.orte) :=
    mischT_gleichAuf hgΛ hX₁ Λ Λ
  have g₂ : GleichAuf ((stabilS P S lok (M.faeden u).kopf.f Λ ++ mass.orte) ++ inv.orte)
      (mischT Tg inv.orte
        ((mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher).lese Λ inv.orte)
        (M.weltVon u).speicher)
      ((M.weltVon u).lese Λ inv.orte) :=
    mischT_gleichAuf
      (g₁.trans (GleichAuf.vonSpeicher (lese_speicher_sa _ _ _)))
      (fun c hc => (hX₂ c hc).elim (fun h => Or.inl (List.mem_append_left _ h)) Or.inr) Λ Λ
  have g₁m : GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++ mass.orte)
      (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) σm :=
    g₁.trans (GleichAuf.vonSpeicher (by simp only [hsm, lese_speicher_sa]))
  have g₂m : GleichAuf ((stabilS P S lok (M.faeden u).kopf.f Λ ++ mass.orte) ++ inv.orte)
      (mischT Tg inv.orte
        ((mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher).lese Λ inv.orte)
        (M.weltVon u).speicher)
      (σm.lese Λ inv.orte) :=
    g₂.trans (GleichAuf.vonSpeicher (by simp only [hsm, lese_speicher_sa]))
  refine ⟨mischT Tg inv.orte
      ((mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher).lese Λ inv.orte)
      (M.weltVon u).speicher,
    HX', hfx', hkx',
    hsub,
    Nat.le_trans (mischT_laenge Tg mass.orte σ Λ (M.weltVon u).speicher)
      (lese_laenge (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) Λ inv.orte),
    GleichAuf.mono (fun _ h => List.mem_append_left _ (List.mem_append_left _ h))
      (g₂.trans (GleichAuf.vonSpeicher rfl)),
    hk,
    fun R O' U A hPX hHA hQ => ZErgG.folgt_of_eq (by
      obtain ⟨e₁, e₂⟩ := hrec A hPX hHA
      have hmA : (eval
          (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher)
          mass
          (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) ρ).n = m' := by
        rw [eval_gleichAuf mass (fun _ h => List.mem_append_right _ h) g₁m ρ]
        exact hm'.symm
      have hwA : wahr? (eval
          (leseA A
            (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) Λ inv.orte)
          inv
          (leseA A
            (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) Λ inv.orte) ρ) = true := by
        rw [e₂, eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) g₂m ρ]
        exact hw
      have hsem := semHA_leaveVerbrauch S O' U A passes R t member edge inv bound mass body rest vor k
        restb i σ ρ hleave
        (mischT Tg mass.orte (σ.lese Λ mass.orte) (M.weltVon u).speicher) e₁.symm m' hmA hfall hwA
      rw [e₂] at hsem
      exact hsem)⟩

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannNextVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
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
  refine ⟨fadenSA_lese hF hhead ρ (.verbrauch t member edge inv bound mass body rest k) _ Λ mass.orte
    (fun hok => by
      obtain ⟨_, _, hTR⟩ := hok
      intro c hc
      rcases expr_stabilX (hFS _) mass hTR.2.2.2.1 c hc with hc | hc
      · exact Or.inl (stabilS_mono (fun L hL => (restb.held_iff L).mp hL) hc)
      · exact Or.inr hc)
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨_, _, hTR⟩ := hok
  obtain ⟨hmem, hedge, hinv, hmass, hb, hbS, hk⟩ := hTR
  exact ⟨σ, Nat.le_refl _,
    GleichAuf.mono
      (fun _ h => List.mem_append_left _
        (stabilS_mono (fun L hL => (restb.held_iff L).mp hL) h)) hg,
    hTR,
    fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
      have hmA : (eval (leseA A σ0 Λ mass.orte) mass (leseA A σ0 Λ mass.orte) ρ).n = m' := by
        rw [hσ0, eval_gleichAuf mass (fun _ h => List.mem_append_right _ h) hg ρ, ← hsm]
        exact hm'.symm
      rw [semHA_nextVerbrauch S O' U A passes R t member edge inv bound mass body rest vor k restb i σ0 ρ
        hnext (leseA A σ0 Λ mass.orte) rfl m' hmA hfall, hσ0])⟩

end Gabbro.Grammatik
