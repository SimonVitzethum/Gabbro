module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.AkteurGFaelle.Teil21

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurG_endeBindAxiomOpt {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOpt e a args he hp hd hgd rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden u).spur)
      (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
    let nextMachine : RufMaschineG D :=
      ⟨σ₂.speicher,
         rufUpdateG M.faeden u
           ⟨(M.faeden u).stapel,
            ⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0,
             ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenG P O passes (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
  dsimp only
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
  cases e with
  | none =>
    refine ⟨fadenG_ax e0 hF hhead ρ (.ende rest) σ₂.spur a args
      (fun hok => ⟨hok.1, by simpa [endblockOrteP] using (teil_append hok.2).2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hz hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show zErg (execEnd O' passes R (.bindAxiomOpt none a args he hp hd hgd rest) σ ρ) = _
    simp only [execEnd, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv, EndAusgang.weiterOpt]
    rfl
  | some τ =>
    refine ⟨fadenG_ax e0 hF hhead (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur a args
      (fun hok => ⟨hok.1, by simpa [endblockOrteP] using (teil_append hok.2).2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hz hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show zErg (execEnd O' passes R (.bindAxiomOpt (some τ) a args he hp hd hgd rest) σ ρ) = _
    simp only [execEnd, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv, EndAusgang.weiterOpt]
    simp only [zErg_schrumpf] <;> rfl

set_option maxHeartbeats 4000000 in
theorem akteurG_endeBindAxiomOptElseOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden u).spur)
      (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
    let nextMachine : RufMaschineG D :=
      ⟨σ₂.speicher,
         rufUpdateG M.faeden u
           ⟨(M.faeden u).stapel,
            ⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0,
             ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenG P O passes (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
  dsimp only
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
  cases e with
  | none =>
    refine ⟨fadenG_ax e0 hF hhead ρ (.ende rest) σ₂.spur a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Endblock.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2; simp only [endblockOrteP] at h2; exact (teil_append h2).2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hz hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show zErg (execEnd O' passes R (.bindAxiomOptElse none a args he hp hd hgd hr err rest) σ ρ) = _
    simp only [execEnd, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv, EndAusgang.weiterOpt]
    rfl
  | some τ =>
    refine ⟨fadenG_ax e0 hF hhead (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Endblock.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2; simp only [endblockOrteP] at h2; exact (teil_append h2).2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hz hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show zErg (execEnd O' passes R (.bindAxiomOptElse (some τ) a args he hp hd hgd hr err rest) σ ρ) = _
    simp only [execEnd, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv, EndAusgang.weiterOpt]
    simp only [zErg_schrumpf] <;> rfl

set_option maxHeartbeats 4000000 in
theorem akteurG_endeBindAxiomOptElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden u).spur)
      (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
    let nextMachine : RufMaschineG D :=
      ⟨σ₂.speicher,
         rufUpdateG M.faeden u
           ⟨(M.faeden u).stapel,
            ⟨(M.faeden u).kopf.f, (M.faeden u).kopf.rho, (M.faeden u).kopf.s0,
             ⟨l, reasonTy (D.agruende a) :: Γ, nachSig D (D.asignatur a) Λ,
              (Env.cons (τ := reasonTy (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenG P O passes (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
  dsimp only
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  have e2 : σ₂ = (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwortSonst] at this
    exact this.symm
  have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inr r) := by
    have := congrArg Prod.snd hax
    simp only [axiomAntwortSonst] at this
    exact this
  have hfr := (hO a (σ₁.fragt (.inl a)) (evalArgs σ₁ args σ₁ ρ)).1
  rw [← e2] at hfr
  subst hs₁
  refine ⟨fadenG_ax e0 hF hhead (Env.cons (τ := .why (D.agruende a)) r ρ) (.ende err) σ₂.spur a args
    (fun hok => ⟨by have h1 := hok.1; simp only [Endblock.gOk, Bool.and_eq_true] at h1; exact h1.1,
      by have h2 := hok.2; simp only [endblockOrteP] at h2; exact (teil_append (teil_append h2).1).2⟩)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  show zErg (execEnd O' passes R (.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ) = _
  simp only [execEnd, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
  simp only [zErg_schrumpf] <;> rfl

end Gabbro.Grammatik
