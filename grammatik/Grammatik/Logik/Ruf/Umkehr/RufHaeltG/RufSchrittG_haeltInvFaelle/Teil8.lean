module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil7

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil5

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}
/- Part 8a of the held-invariant preservation for G-steps (C08): the case
   lemmas for `dannBindAxiomOpt`, `dannBindAxiomOptElse` (success and
   reason exits) and `endeBindAxiomOpt`. -/
set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindAxiomOpt {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOpt e a args he hp hd hgd rest) k⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v)) (neu : List (Ereignis D))
  (hneu : σ₂.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := σ₂.speicher,
        faeden :=
          rufUpdateG M.faeden f
            { stapel := (M.faeden f).stapel,
              kopf :=
                { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                  rest :=
                    ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
                      .dann rest (GRest.weiterOpt (Λ := Λ') e k)⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk.1 L hL)
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
    ⟨hA, GRest.kette_weiterOpt e k hk.2 (GRest.kette_top k hk.2)⟩ ?_
  rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindAxiomOptElseOk {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e) (hr : 0 < D.agruende a)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOptElse e a args he hp hd hgd hr err rest) k⟩)
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
                    ⟨l, ErgCtx Γ e, nachSig D (D.asignatur a) Λ, ergEnv e (he ▸ v) ρ,
                      .dann rest (GRest.weiterOpt (Λ := Λ') e k)⟩ },
              spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
        lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
    f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hA : ∀ L ∈ D.haelt (M.faeden f).kopf.f, Res.held L ∈ nachSig D (D.asignatur a) Λ :=
    fun L hL => (held_nachSig_iff (D.asignatur a) Λ L).mpr (hk.1 L hL)
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
    ⟨hA, GRest.kette_weiterOpt e k hk.2 (GRest.kette_top k hk.2)⟩ ?_
  rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindAxiomOptElseGrund {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e) (hr : 0 < D.agruende a)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindAxiomOptElse e a args he hp hd hgd hr err rest) k⟩)
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
                      (Env.cons (τ := reasonTy (D.agruende a)) r ρ),
                      .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩ },
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

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeBindAxiomOpt {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (e : Option Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = e)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.asignatur a) Λ)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (ErgCtx Γ e) (nachSig D (D.asignatur a) Λ))
  (ρ : Env D Γ)
  (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bindAxiomOpt e a args he hp hd hgd rest)⟩)
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ args.orte) (σ₂ : World D) (v : ErgVal D (D.aerg a))
  (hax : axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) = (σ₂, some v)) (neu : List (Ereignis D))
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
  rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]
  exact heldIn_nachSig _ _ hh




set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindCallIndElse {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
  (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (Ty.why (D.sigNr n).gruende :: Γ)
    (nachSig D (D.sigNr n) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCallIndElse p args he hp hr err rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden f).spur) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              {
                stapel :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden f).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
    (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
  rw [hs0, offen_lese]; exact callee_held (RufPasst.vonPasst (D.passt_sig hg) hp) hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannCallIndElse {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
  (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (Ty.why (D.sigNr n).gruende :: Γ)
    (nachSig D (D.sigNr n) Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.callIndElse p args he hp hr err) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon f).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden f).spur) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              {
                stapel :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
                                    (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden f).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, nach_nennt hk.1, hk.2⟩ (by fr_push)
    (callee_kette P g rho s0) rfl
    (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
  rw [hs0, offen_lese]; exact callee_held (RufPasst.vonPasst (D.passt_sig hg) hp) hh


end Gabbro.Grammatik
