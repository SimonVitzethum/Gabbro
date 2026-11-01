module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Teil10

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_dannGleitNarrowElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
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
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ e.orte) (hn : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = none)
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
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
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
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
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
                                  (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
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
  refine ⟨fadenV_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrk⟩ := hok
  obtain ⟨hkS, _⟩ := and_teile hks
  obtain ⟨hes, hsS, _⟩ := teile2 hss
  have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
    rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
  exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, okV_alsBlock sonst k rest.held_iff hkS hsS hrk,
    fun R O' => semV_gleitNarrowElse O' passes R e lo hi sonst rest k σ ρ hn'⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_dannBindAxiom {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
  (he : D.aerg a = some τ)
  (hw : ∀ (t : D.Tab), D.aschreibt a t = true → (vertragVon D (M.faeden u).kopf.f).schreibt t = true)
  (hg : ∀ (g : D.Glob), D.agschreibt a g = true → (vertragVon D (M.faeden u).kopf.f).gschreibt g = true)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindAxiom a args he hw hg hd hgd rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v)) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
      ({ speicher := σ₂.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
  have e2 : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwort] at this
    exact this.symm
  have hv : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).2 = some v := by
    have := congrArg Prod.snd hax
    simp only [axiomAntwort] at this
    exact this
  have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
  rw [← e2] at hfr
  subst hs₁
  refine ⟨fadenV_ax e0 hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur a args
    (fun hok => ⟨hok.1, by simpa [blockOrteP] using (teil_append hok.2.1).2, hok.2.2⟩)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  show weiterZ O' passes R k (execBlock O' passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
  simp only [execBlock, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv]
  rfl

set_option maxHeartbeats 4000000 in
theorem akteurV_endeBindAxiom {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
  (hw : ∀ (t : D.Tab), D.aschreibt a t = true → (vertragVon D (M.faeden u).kopf.f).schreibt t = true)
  (hg : ∀ (g : D.Glob), D.agschreibt a g = true → (vertragVon D (M.faeden u).kopf.f).gschreibt g = true)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.bindAxiom a args he hw hg hd hgd rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v)) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
      ({ speicher := σ₂.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.ende rest)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
  have e2 : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwort] at this
    exact this.symm
  have hv : einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).2 = some v := by
    have := congrArg Prod.snd hax
    simp only [axiomAntwort] at this
    exact this
  have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
  rw [← e2] at hfr
  subst hs₁
  refine ⟨fadenV_ax e0 hF hhead (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur a args
    (fun hok => ⟨hok.1, by simpa [endblockOrteP] using (teil_append hok.2).2⟩)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  show zErg (execEnd O' passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
  simp only [execEnd, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv]
  rw [zErg_schrumpf]
  rfl

set_option maxHeartbeats 4000000 in
theorem akteurV_dannBindAxiomElseOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
  (he : D.aerg a = some τ) (hr : 0 < D.agruende a)
  (hw : ∀ (t : D.Tab), D.aschreibt a t = true → (vertragVon D (M.faeden u).kopf.f).schreibt t = true)
  (hg : ∀ (g : D.Glob), D.agschreibt a g = true → (vertragVon D (M.faeden u).kopf.f).gschreibt g = true)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.why (D.agruende a) :: Γ) Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindAxiomElse a args he hr hw hg hd hgd err rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v))) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenV P O passes
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₂.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := σ₂.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
      ({ speicher := σ₂.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
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
  have e2 : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwortSonst] at this
    exact this.symm
  have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inl v) := by
    have := congrArg Prod.snd hax
    simp only [axiomAntwortSonst] at this
    exact this
  have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
  rw [← e2] at hfr
  subst hs₁
  refine ⟨fadenV_ax e0 hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur a args
    (fun hok => ⟨by have h1 := hok.1; simp only [Block.vOk, Bool.and_eq_true] at h1; exact h1.2,
      by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append h2).2, hok.2.2⟩)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  show weiterZ O' passes R k (execBlock O' passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) = _
  simp only [execBlock, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
  rfl

end Gabbro.Grammatik
