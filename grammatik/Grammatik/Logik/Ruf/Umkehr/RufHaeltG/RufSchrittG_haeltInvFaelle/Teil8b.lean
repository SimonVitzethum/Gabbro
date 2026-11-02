module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil8

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/- Part 8b of the held-invariant preservation for G-steps (C08): the case
   lemmas for `endeBindAxiomOptElse` (success and reason exits) and
   `dannAxiomCallElse`. -/

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeBindAxiomOptElseOk {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e) (hr : 0 < D.agruende a)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ))
  (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v))) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := σ₂.speicher,
        faeden :=
          rufUpdateG M.faeden f
            { stapel := (M.faeden f).stapel,
              kopf :=
                { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                  rest :=
                    ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ, .ende rest⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk L hL)
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hA ?_
  rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeBindAxiomOptElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e) (hr : 0 < D.agruende a)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ))
  (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOptElse e a args he hp hd hgd hr err rest)⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (r : Fin (D.agruende a))
  (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r))) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := σ₂.speicher,
        faeden :=
          rufUpdateG M.faeden f
            { stapel := (M.faeden f).stapel,
              kopf :=
                { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                  rest :=
                    ⟨l, reasonTy (D.agruende a) :: Γ, nachSig D (D.asignatur a) Λ,
                      (Env.cons (τ := reasonTy (D.agruende a)) r ρ), .ende err⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk L hL)
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hA ?_
  rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannAxiomCallElseOk {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.asignatur a) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest =
    ⟨l, Γ, Λ, ρ, .dann (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inl v))) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := σ₂.speicher,
        faeden :=
          rufUpdateG M.faeden f
            { stapel := (M.faeden f).stapel,
              kopf :=
                { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                  rest := ⟨l, Γ, nachSig D (D.asignatur a) Λ, ρ, .dann rest k⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk.1 L hL)
  have hkk : (GRest.dann rest k).kette (D.haelt (M.faeden f).kopf.f) :=
    ⟨hA, hk.2⟩
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hkk ?_
  rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannAxiomCallElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ) (hr : 0 < D.agruende a)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.asignatur a) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest =
    ⟨l, Γ, Λ, ρ, .dann (.cons (.axiomCallElse e a args he hp hd hgd hr err) rest) k⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (r : Fin (D.agruende a))
  (hax : axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some (Sum.inr r))) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := σ₂.speicher,
        faeden :=
          rufUpdateG M.faeden f
            { stapel := (M.faeden f).stapel,
              kopf :=
                { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                  rest := ⟨l, reasonTy (D.agruende a) :: Γ, nachSig D (D.asignatur a) Λ,
                    (Env.cons (τ := reasonTy (D.agruende a)) r ρ), .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk.1 L hL)
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
    (kette_abbruch err.alsBlock.2 hA (.schrumpf k) ⟨GRest.kette_top k hk.2, hk.2⟩
      (fun L hL => (Block.held_iff rest L).mp hL)) ?_
  rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh


end Gabbro.Grammatik
