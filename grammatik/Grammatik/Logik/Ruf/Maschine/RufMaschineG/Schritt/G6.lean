module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Steps of `RufSchrittG`, group 6** (`endeBindAxiomElseOk` … `endeBindAxiomElseGrund`): the rules of the call machine G,
    verbatim; `RufSchrittG` (RufMaschineG/T2.lean) is the union of the 6 groups. -/
inductive RufSchrittG6 (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineG D → Faden → RufMaschineG D → Prop where
  /-- The same at the top level of a body: a value. -/
  | endeBindAxiomElseOk
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The same at the top level of a body: a reason. -/
  | endeBindAxiomElseGrund
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomElse a args he hr hw hg hd hgd err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The same at the top level of a body: an optional value («C08»). -/
  | endeBindAxiomOptElseOk
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (v : ErgVal D (D.aerg a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ, .ende rest⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  /-- The same at the top level of a body: a reason («C08»). -/
  | endeBindAxiomOptElseGrund
      (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte)
      (σ₂ : World D) (r : Fin (D.agruende a))
      (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r)))
      (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨σ₂.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, reasonTy (D.agruende a) :: Γ, nachSig D (D.asignatur a) Λ,
              (Env.cons (τ := reasonTy (D.agruende a)) r ρ), .ende err⟩⟩,
            σ₂.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩

  | endeGleit (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (l₁ h₁ l₂ h₂ : Int × Int)
      (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂))
      (lo hi : Int × Int)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ)

      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.float op a b lo hi rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ (a.orte ++ b.orte))
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi
        (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .ende rest⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | endeGleitLit (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (q lo hi : Int × Int)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ)

      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.floatLit q lo hi rest)⟩)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (bruch q) = some v) :
      RufSchrittG6 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .ende rest⟩⟩,
            (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf, M.start⟩
  | endeGleitVon (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (l₁ h₁ : Int)
      (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ)

      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.floatOf e lo hi rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .ende rest⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | endeGleitNarrowOk (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ)

      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.floatNarrow e lo hi sonst rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (v : Wert D (.fl lo hi))
      (hv : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = some v)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ,
              .ende rest⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩
  | endeGleitNarrowElse (M : RufMaschineG D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (l₁ h₁ : Int × Int)
      (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
      (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (.fl lo hi :: Γ) Λ)

      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .ende (.floatNarrow e lo hi sonst rest)⟩)
      (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
      (hn : gleitPasst lo hi (eval σ₁ e σ₁ ρ).x = none)
      (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
      (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
      RufSchrittG6 P O passes M f
        ⟨M.speicher,
         rufUpdateG M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ, ρ, .ende sonst⟩⟩,
            σ₁.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenG f neu, M.start⟩

end Gabbro.Grammatik
