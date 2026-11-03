module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil2

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannVerbrauch {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ'' : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.consumeTraverse t member edge inv bound mass body) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)) :
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
                              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body
                                ((D.count t).toNat + bound.toNat + 1) (GRest.dann rest k))⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := (M.faeden f).spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_verbrauchWeiter {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
  (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
  (v : Wert D (Ty.index (D.count t)))
  (σ₃ : World D) (hs₃ : σ₃ = σ₂.lese Λ mass.orte)
  (m : Int)
  (neu : List (Ereignis D)) (hneu : σ₃.spur = neu ++ (M.faeden f).spur)
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨true,
                          (⟨Ty.index (D.count t) :: Γ,
                              (⟨Λ, (Env.cons v ρ, GRest.dann body (GRest.verbrauchRest t member edge inv bound mass body
                                rest m k))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (Ty.index (D.count t) :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ₃.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have ho : offen σ₃.spur = offen (M.faeden f).spur := by
    rw [hs₃, offen_lese, hs₂, offen_lese, hs₁, offen_lese]
    rfl
  refine haeltInvG_kopf h (by intro K hK _; rw [ho]; exact hK)
    (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ ?_
  rw [ho]
  exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_verbrauchLeer {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body (rest + 1) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ inv.orte)
  (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (σ₂ : World D) (hs₂ : σ₂ = σ₁.lese Λ (member.orte ++ edge.orte))
  (neu : List (Ereignis D)) (hneu : σ₂.spur = neu ++ (M.faeden f).spur)
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
                              (⟨Λ, (ρ, k)⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
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
  have ho : offen σ₂.spur = offen (M.faeden f).spur := by
    rw [hs₂, offen_lese, hs₁, offen_lese]
    rfl
  refine haeltInvG_kopf h (by intro K hK _; rw [ho]; exact hK)
    (by fr_tac) hk.2 ?_
  rw [ho]
  exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_verbrauchFort {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ : List (Res D)) (t : D.Tab)
  (member : Expr D (.index (D.count t) :: Γ) Λ Ty.bool)
  (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ Ty.bool)
  (inv : Expr D Γ Λ Ty.bool) (bound : Int)
  (mass : Expr D Γ Λ (.int 0 bound))
  (body : Block D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Nat) (vor : Int)
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λ, (Env.cons i ρ, GRest.verbrauchRest t member edge inv bound mass body rest vor k)⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden f).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ mass.orte)
  (m' : Int) (hm' : (eval σ₁ mass σ₁ ρ).n = m')
  (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
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
                              (⟨Λ, (ρ, GRest.verbrauch t member edge inv bound mass body rest k)⟩ :
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
  have ho : offen σ₁.spur = offen (M.faeden f).spur := by
    rw [hs₁, offen_lese]
    rfl
  refine haeltInvG_kopf h (by intro K hK _; rw [ho]; exact hK)
    (by fr_tac) ⟨hk.1, hk.2⟩ ?_
  rw [ho]
  exact hh

end Gabbro.Grammatik
