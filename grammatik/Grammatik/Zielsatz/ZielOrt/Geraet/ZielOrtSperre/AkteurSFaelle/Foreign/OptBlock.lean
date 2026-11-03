module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.AkteurSFaelle.Teil19

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurS_dannBindAxiomOpt {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
  (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutS P passes Q S f)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussS P S lok f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOpt e a args he hp hd hgd rest) k⟩)
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
             ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
              .dann rest (GRest.weiterOpt (Λ := Λ') e k)⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenS P O passes Q S lok (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
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
    refine ⟨fadenS_ax hF hhead ρ (.dann rest k) σ₂.spur
      (fun L => held_nachSig_iff (D.asignatur a) Λ L) a args
      (fun hok => ⟨hok.1, (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomOpt none a args he hp hd hgd rest) σ ρ) = _
    simp only [execBlockH, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv, Ausgang.weiterOpt, ergEnv]
    rfl
  | some τ =>
    refine ⟨fadenS_ax hF hhead (ergEnv (some τ) (he ▸ v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun L => held_nachSig_iff (D.asignatur a) Λ L) a args
      (fun hok => ⟨hok.1, (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomOpt (some τ) a args he hp hd hgd rest) σ ρ) = _
    simp only [execBlockH, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv, Ausgang.weiterOpt, ergEnv]
    rfl

set_option maxHeartbeats 4000000 in
theorem akteurS_dannBindAxiomOptElseOk {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
  (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutS P passes Q S f)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussS P S lok f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOptElse e a args he hp hd hgd hr err rest) k⟩)
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
             ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
              .dann rest (GRest.weiterOpt (Λ := Λ') e k)⟩⟩,
            σ₂.spur, (M.faeden u).log⟩,
         M.lauf ++ rufEigenG u neu, M.start⟩
    FadenS P O passes Q S lok (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
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
    refine ⟨fadenS_ax hF hhead ρ (.dann rest k) σ₂.spur
      (fun L => held_nachSig_iff (D.asignatur a) Λ L) a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Block.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append h2).2, hok.2.2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomOptElse none a args he hp hd hgd hr err rest) σ ρ) = _
    simp only [execBlockH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv, Ausgang.weiterOpt, ergEnv]
    rfl
  | some τ =>
    refine ⟨fadenS_ax hF hhead (ergEnv (some τ) (he ▸ v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun L => held_nachSig_iff (D.asignatur a) Λ L) a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Block.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append h2).2, hok.2.2⟩)
      (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomOptElse (some τ) a args he hp hd hgd hr err rest) σ ρ) = _
    simp only [execBlockH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv, Ausgang.weiterOpt, ergEnv]
    rfl

set_option maxHeartbeats 4000000 in
theorem akteurS_dannBindAxiomOptElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
  (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutS P passes Q S f)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussS P S lok f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (e : Option Ty)
      (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
      (hr : 0 < D.agruende a)
      (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.asignatur a) Λ)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l
        (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
      (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (ErgCtx Γ e)
        (nachSig D (D.asignatur a) Λ) Λ')
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hhead : (M.faeden u).kopf.rest =
        ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOptElse e a args he hp hd hgd hr err rest) k⟩)
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
    FadenS P O passes Q S lok (nextMachine.faeden u) (nextMachine.weltVon u) ∧ LogOk P (nextMachine.faeden u).log := by
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
  refine ⟨fadenS_ax hF hhead (Env.cons (τ := .why (D.agruende a)) r ρ) (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σ₂.spur
    (fun L => held_nachSig_iff (D.asignatur a) Λ L) a args
    (fun hok => okS_alsBlock err (.schrumpf k) rest.held_iff
      (by have h1 := hok.1; simp only [Block.gOk, Bool.and_eq_true] at h1; exact h1.1)
      (by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append (teil_append h2).1).2) hok.2.2)
    (σ₂, (O.wirkt a (((M.weltVon u).lese Λ args.orte).fragt (.inl a))
      (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
    hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
    (fun O' R U σ hz hwk => ?_), hL⟩
  apply ZErgG.folgt_of_eq
  show weiterH S O' U passes R k
    (execBlockH S O' U passes R (.bindAxiomOptElse e a args he hp hd hgd hr err rest) σ ρ) = _
  simp only [execBlockH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
  exact (semH_alsBlock_schrumpf S O' U passes R err k _ _).symm

end Gabbro.Grammatik
