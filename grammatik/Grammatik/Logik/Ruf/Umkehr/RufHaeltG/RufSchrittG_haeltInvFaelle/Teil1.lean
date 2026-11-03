module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Basis

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_blatt {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ') (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
  (ρ : Env D Γ) (hleaf : s.istBlatt = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons s rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
  (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = Ausgang.ok σ' ρ') (hneu : σ'.spur = neu ++ (M.faeden f).spur)
  (hkein : ∀ (L : D.Lock) (h : List D.Lock), ¬Ereignis.nimmt L h ∈ neu) :
  HaeltInvG
    ({ speicher := σ'.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨Γ,
                              (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ'.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hscope : s.ScopesOk :=
    Stmt.scopesOk_of_ok O passes keinRuf s hleaf (M.weltVon f) ρ σ' ρ' hstep
  have hG := (Stmt.gut_blatt O passes keinRuf hO s hleaf hscope (M.weltVon f) ρ hΛ) σ'
    (by rw [hstep]; rfl)
  rw [hstep] at hG
  have ho : offen σ'.spur = offen (M.faeden f).spur :=
    hG.2.1
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) (nennt_stmt s hk) ?_
  rw [ho]; exact heldIn_stmt s hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_ruf {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (g : D.Fn) (args : Args D Γ Λ (D.params g)) (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
  (hr : D.gruende g = 0) (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ)) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons (Stmt.call g args hp hr) rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
  (rho : Env D (D.params g)) (hrho : rho = evalArgs s0 args s0 ρ) (neu : List (Ereignis D))
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
                                (⟨nach D g Λ, (ρ, GRest.ende rest)⟩ :
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
  refine haeltInvG_push h _ _ _ _ rfl (nach_nennt hk) (by fr_push) (callee_kette P g rho s0) rfl
    (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
  rw [hs0, offen_lese]; exact callee_held hp hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_endeEntf {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ') (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
  (ρ : Env D Γ) (hent : GEntfaltbar s = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons s rest))⟩ :
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
                              (⟨Λ, (ρ, GRest.dann (Block.cons s Block.nil) (GRest.ende rest))⟩ :
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
  exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk, nennt_stmt s hk⟩ hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBlatt {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ) (hleaf : s.istBlatt = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons s rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
  (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = Ausgang.ok σ' ρ') (hneu : σ'.spur = neu ++ (M.faeden f).spur)
  (hkein : ∀ (L : D.Lock) (h : List D.Lock), ¬Ereignis.nimmt L h ∈ neu) :
  HaeltInvG
    ({ speicher := σ'.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨l,
                          (⟨Γ,
                              (⟨Λ', (ρ', GRest.dann rest k)⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := σ'.spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  have hscope : s.ScopesOk :=
    Stmt.scopesOk_of_ok O passes keinRuf s hleaf (M.weltVon f) ρ σ' ρ' hstep
  have hG := (Stmt.gut_blatt O passes keinRuf hO s hleaf hscope (M.weltVon f) ρ hΛ) σ'
    (by rw [hstep]; rfl)
  rw [hstep] at hG
  have ho : offen σ'.spur = offen (M.faeden f).spur :=
    hG.2.1
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨nennt_stmt s hk.1, hk.2⟩ ?_
  rw [ho]; exact heldIn_stmt s hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannLeer {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann Block.nil k)⟩ :
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
                              (⟨Λ, (ρ, k)⟩ :
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
  exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannIteWahr {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (c : Expr D Γ Λ Ty.bool) (t e : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.ite c t e) rest) k)⟩ :
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
                              (⟨Λ, (ρ, GRest.dann t (GRest.dann rest k))⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block t hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannIteFalsch {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (c : Expr D Γ Λ Ty.bool) (t e : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.ite c t e) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ c.orte) (hw : wahr? (eval σ₁ c σ₁ ρ) = false)
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
                              (⟨Λ, (ρ, GRest.dann e (GRest.dann rest k))⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block e hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannOnOptionSome {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (n : Int) (o : Expr D Γ Λ (Ty.opt n))
  (p : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.index n :: Γ) Λ Λ')
  (a : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onOption o p a) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ o.orte) (v : Wert D (Ty.index n)) (hv : eval σ₁ o σ₁ ρ = some v)
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
                          (⟨Ty.index n :: Γ,
                              (⟨Λ, (Env.cons v ρ, GRest.dann p (GRest.dann rest k).schrumpf)⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (Ty.index n :: Γ) ×
                                    GRest D (vertragVon D (M.faeden f).kopf.f) l (Ty.index n :: Γ) Λ)⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block p hk.1, nennt_block p hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannOnOptionNone {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (n : Int) (o : Expr D Γ Λ (Ty.opt n))
  (p : Block D (vertragVon D (M.faeden f).kopf.f) l (Ty.index n :: Γ) Λ Λ')
  (a : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onOption o p a) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon f).lese Λ o.orte) (hv : eval σ₁ o σ₁ ρ = none) (neu : List (Ereignis D))
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
                              (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
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
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block a hk.1, hk.2⟩ ?_
  rw [hs₁, offen_lese]; exact hh

end Gabbro.Grammatik
