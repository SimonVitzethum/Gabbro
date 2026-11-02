module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil1

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannOnTagSome {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (cs : List (Option Ty)) (v : Expr D Γ Λ (Ty.sum cs))
  (arms : Arms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' cs)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onTag v arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ v.orte) (τ : Ty)
  (b : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
  (hw :
    armWahlG arms (eval σ₁ v σ₁ ρ) =
      (⟨some τ, (b, nutz)⟩ :
        (c : Option Ty) × Block D (vertragVon D (M.faeden f).kopf.f) l (ArmCtx Γ c) Λ Λ' × Nutzlast D.Fn D.passt c))
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨τ :: Γ,
                              (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (τ :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₁.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, nennt_block b hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannOnTagNone {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (cs : List (Option Ty)) (v : Expr D Γ Λ (Ty.sum cs))
  (arms : Arms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' cs)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onTag v arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ v.orte) (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (nutz : Nutzlast D.Fn D.passt none)
  (hw :
    armWahlG arms (eval σ₁ v σ₁ ρ) =
      (⟨none, (b, nutz)⟩ :
        (c : Option Ty) × Block D (vertragVon D (M.faeden f).kopf.f) l (ArmCtx Γ c) Λ Λ' × Nutzlast D.Fn D.passt c))
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨Γ,
                              (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k))⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₁.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannOnGrund {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (n : Nat) (r : Expr D Γ Λ (Ty.why n))
  (arms : GrundArms D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ' n)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onWhy r arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ r.orte) (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (hw : grundWahlG arms (eval σ₁ r σ₁ ρ) = b) (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨Γ,
                              (⟨Λ, (ρ, GRest.dann b (GRest.dann rest k))⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₁.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeBind {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (τ : Ty) (e : Expr D Γ Λ τ) (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.bind e rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden f).spur) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨τ :: Γ,
                              (⟨Λ, (Env.cons (eval σ₁ e σ₁ ρ) ρ, GRest.ende rest)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₁.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeBindAxiom {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (τ : Ty) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
  (hw : ∀ (t : D.Tab), D.aschreibt a t = true → (vertragVon D (M.faeden f).kopf.f).schreibt t = true)
  (hg : ∀ (g : D.Glob), D.agschreibt a g = true → (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
  (hd : ∀ (t : D.Tab), D.aschreibt a t = true → darf D t Λ)
  (hgd : ∀ (g : D.Glob), D.agschreibt a g = true → gdarf D g Λ)
  (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.bindAxiom a args he hw hg hd hgd rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
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
                      (⟨l,
                          (⟨τ :: Γ,
                              (⟨Λ, (Env.cons (ergWert he v) ρ, GRest.ende rest)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₂.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
  rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh

end Gabbro.Grammatik
