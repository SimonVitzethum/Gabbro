module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil5

@[expose] public section


namespace Gabbro.Grammatik

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
                                  (ρ, GRest.wartetSonst (D.sigNr n).gruende err .nil
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
