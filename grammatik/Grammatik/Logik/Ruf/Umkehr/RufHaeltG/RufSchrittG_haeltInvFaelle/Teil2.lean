module
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil2Basis
import all Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil2Basis

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil1

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBind {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bind e rest) k)⟩ :
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
                              (⟨Λ, (Env.cons (eval σ₁ e σ₁ ρ) ρ, GRest.dann rest k.schrumpf)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannNarrowOk {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int) (e : Expr D Γ Λ (Ty.int lo hi))
  (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.int lo' hi' :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.narrow e lo' hi' sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte) (hn : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
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
                          (⟨Ty.int lo' hi' :: Γ,
                              (⟨Λ,
                                  (Env.cons
                                      { n := (eval σ₁ e σ₁ ρ).n, lo_le := hn.left, le_hi := hn.right : Zahl lo' hi' } ρ,
                                    GRest.dann rest k.schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (Ty.int lo' hi' :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (Ty.int lo' hi' :: Γ) Λ)⟩ :
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

/-- Required narrowing keeps the continuation's locks while binding the checked value. -/
theorem rufSchrittG_haeltInv_dannNarrowRequired {D : Deklaration}
    {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
    (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.2.2.2.2)
    (hh0 : HeldIn (M.faeden f).kopf.rest.2.2.1 (offen (M.faeden f).spur))
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (lo hi lo' hi' : Int)
    (e : Expr D Γ Λ (.int lo hi))
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrowRequired e lo' hi' rest) k⟩)
    (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte)
    (hn : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi')
    (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden f).spur)
    (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
    HaeltInvG ((⟨M.speicher, rufUpdateG M.faeden f
      ⟨(M.faeden f).stapel,
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
          ⟨l, .int lo' hi' :: Γ, Λ,
            .cons ⟨(eval σ₁ e σ₁ ρ).n, hn.1, hn.2⟩ ρ, .dann rest (.schrumpf k)⟩⟩,
        σ₁.spur, (M.faeden f).log⟩,
      M.lauf ++ rufEigenG f neu, M.start⟩ : RufMaschineG D).faeden f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannNarrowElse {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (lo hi lo' hi' : Int) (e : Expr D Γ Λ (Ty.int lo hi))
  (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.int lo' hi' :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.narrow e lo' hi' sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ e.orte) (hn : ¬(lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi'))
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
theorem rufSchrittG_haeltInv_dannPruefWahr {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (c : Expr D Γ Λ Ty.bool) (sonst : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ') (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.check c sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte) (hw : wahr? (eval σ₁ c σ₁ ρ) = true) (neu : List (Ereignis D))
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
                              (⟨Λ, (ρ, GRest.dann rest k)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
  rw [hs₁, offen_lese]; exact hh

end Gabbro.Grammatik
