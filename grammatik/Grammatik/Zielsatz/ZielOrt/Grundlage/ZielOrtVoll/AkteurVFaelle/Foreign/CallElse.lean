module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Tail.Teil20

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_dannAxiomCallElseOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (hr : 0 < D.agruende a)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : RufBlockG M u l Γ (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : RufDannHeadG M u (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k ρ)
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
             ⟨l, Γ, nachSig D (D.asignatur a) Λ, ρ, .dann rest k⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenV P O passes (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
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
  refine ⟨fadenV_ax e0 hF hhead ρ (.dann rest k) σ₂.spur a args
    (fun hok => (okV_dann_cons hok).2.2)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  rw [semV_dann_cons]
  simp only [execStmt, axiomAntwortSonst, hwk,
    (show O'.zeiger = O.zeiger from hz), hv]
  rfl

set_option maxHeartbeats 4000000 in
theorem akteurV_dannAxiomCallElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (hr : 0 < D.agruende a)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : RufBlockG M u l Γ (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : RufDannHeadG M u (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k ρ)
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
              (Env.cons (τ := reasonTy (D.agruende a)) r ρ),
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenV P O passes (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
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
  refine ⟨fadenV_ax e0 hF hhead (Env.cons (τ := .why (D.agruende a)) r ρ) (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σ₂.spur a args
    (fun hok => by
      have h := okV_dann_cons hok
      exact okV_alsBlock err (.schrumpf k) rest.held_iff h.1
        (by simpa [stmtOrteP] using (teil_append h.2.1).2) h.2.2.2.2)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun O' R σ hz hwk => ?_), hL⟩
  apply ZErg.folgt_of_eq
  rw [semV_dann_cons]
  simp only [execStmt, axiomAntwortSonst, hwk,
    (show O'.zeiger = O.zeiger from hz), hv]
  rw [semV_alsBlock_schrumpf]
  cases execEnd O' passes R err (axWelt e0 a ((σ.lese Λ args.orte).fragt (.inl a)) σ₂) (.cons r ρ) <;> rfl

end Gabbro.Grammatik
