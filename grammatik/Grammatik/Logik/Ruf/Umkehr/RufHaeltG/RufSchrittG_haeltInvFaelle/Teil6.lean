module
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil6Basis
import all Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil6Basis

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil8

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannRegLiesElseWahr {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (zusage : Expr D (D.rtyp r :: Γ) Λ Ty.bool)
  (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regReadElse r hk zusage sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (Sum.inr (Sum.inl r)))) = some v) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon f).fragt (Sum.inr (Sum.inl r))).lese Λ zusage.orte)
  (hw : wahr? (eval σ₁ zusage σ₁ (Env.cons v ρ)) = true) (neu : List (Ereignis D))
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
                          (⟨D.rtyp r :: Γ,
                              (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.rtyp r :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannRegLiesElseFalsch {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (zusage : Expr D (D.rtyp r :: Γ) Λ Ty.bool)
  (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regReadElse r hk zusage sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (Sum.inr (Sum.inl r)))) = some v) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon f).fragt (Sum.inr (Sum.inl r))).lese Λ zusage.orte)
  (hw : wahr? (eval σ₁ zusage σ₁ (Env.cons v ρ)) = false) (neu : List (Ereignis D))
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
                          (⟨Γ,
                              (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
    (kette_abbruch _ hk.1 k hk.2 (fun L hL => (Block.held_iff rest L).mp hL)) ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannExchange {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (g : D.Glob) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : (vertragVon D (M.faeden f).kopf.f).gschreibt g = true)
  (hL : gdarf D g Λ) (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.exchange g neuE hw hL rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ (Sum.inr g :: neuE.orte)) (σ₂ : World D)
  (hs₂ : σ₂ = σ₁.schreibGlob g Λ (eval σ₁ neuE σ₁ (Env.cons (σ₁.globs g) ρ))) (neu : List (Ereignis D))
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
                          (⟨D.gtyp g :: Γ,
                              (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.gtyp g :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
  rw [hs₂, offen_schreibGlob, hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannGleit {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (l₁ h₁ l₂ h₂ : Int × Int) (op : GleitOp) (a : Expr D Γ Λ (Ty.fl l₁ h₁)) (b : Expr D Γ Λ (Ty.fl l₂ h₂))
  (lo hi : Int × Int) (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.float op a b lo hi rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ (a.orte ++ b.orte)) (v : Wert D (Ty.fl lo hi))
  (hv : gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) = some v) (neu : List (Ereignis D))
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
                          (⟨Ty.fl lo hi :: Γ,
                              (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (Ty.fl lo hi :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (Ty.fl lo hi :: Γ) Λ)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannGleitLit {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (q lo hi : Int × Int) (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.fl lo hi :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.floatLit q lo hi rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (v : Wert D (Ty.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨Ty.fl lo hi :: Γ,
                              (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (Ty.fl lo hi :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (Ty.fl lo hi :: Γ) Λ)⟩ :
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
  exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh

end Gabbro.Grammatik
