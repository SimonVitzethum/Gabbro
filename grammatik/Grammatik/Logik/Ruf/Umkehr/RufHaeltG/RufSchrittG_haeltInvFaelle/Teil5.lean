module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil4

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannCallInd {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.callInd p args hp hr) rest) k)⟩ :
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
                                (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.dann rest k)⟩ :
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
theorem rufSchrittG_haeltInv_rufCallInd {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
  (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
  (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nachSig D (D.sigNr n) Λ)) (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons (Stmt.callInd p args hp hr) rest))⟩ :
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
                                (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.ende rest)⟩ :
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
  rw [hs0, offen_lese]; exact callee_held (RufPasst.vonPasst (D.passt_sig hg) hp) hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindCall {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCall g args he hp hr rest) k)⟩ :
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
                                (⟨nach D g Λ, (ρ, GRest.wartet rest k)⟩ :
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
  rw [hs0, offen_lese]; exact callee_held hp hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannBindCallInd {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
  (he : (D.sigNr n).erg = some τ) (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.sigNr n) Λ)
  (hr : (D.sigNr n).gruende = 0)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCallInd p args he hp hr rest) k)⟩ :
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
                                (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartet rest k)⟩ :
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
theorem rufSchrittG_haeltInv_dannBindCallElse {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ) (hr : 0 < D.gruende g)
  (err : Endblock D (vertragVon D (M.faeden f).kopf.f) l (Ty.why (D.gruende g) :: Γ) (nach D g Λ))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCallElse g args he hp hr err rest) k)⟩ :
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
                                (⟨nach D g Λ, (ρ, GRest.wartetSonst (D.gruende g) err rest k)⟩ :
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
  rw [hs0, offen_lese]; exact callee_held hp hh

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_peelAbbruchLeave {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λk) (ρ : Env D Γ) (hl : true = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨true,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.leave hl) rest) k.abbruch)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨true,
                          (⟨Γ,
                              (⟨Λk, (ρ, GRest.dann (Block.cons (Stmt.leave hl) Block.nil) k)⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := (M.faeden f).spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2.2, hk.2.2.2⟩ ?_
  exact fun L hL => heldIn_block rest hh L (hk.2.2.1 L hL)

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_peelAbbruchNext {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (Γ : Ctx) (Λ Λ1 Λk : List (Res D))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) true Γ Λ Λ1)
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λk) (ρ : Env D Γ) (hl : true = true)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨true,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.next hl) rest) k.abbruch)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)) :
  HaeltInvG
    ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := (M.faeden f).stapel,
                kopf :=
                  { f := (M.faeden f).kopf.f, rho := (M.faeden f).kopf.rho, s0 := (M.faeden f).kopf.s0,
                    rest :=
                      (⟨true,
                          (⟨Γ,
                              (⟨Λk, (ρ, GRest.dann (Block.cons (Stmt.next hl) Block.nil) k)⟩ :
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩ :
                        (l : Bool) ×
                          (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) :
                    RufRahmenG D },
                spur := (M.faeden f).spur, log := (M.faeden f).log : RufFadenG D },
          lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2.2, hk.2.2.2⟩ ?_
  exact fun L hL => heldIn_block rest hh L (hk.2.2.1 L hL)

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannRet {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx)
  (Λ Λ'' : List (Res D)) (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
  (hperm : Λ.Perm (Vertrag.ende D (vertragVon D (M.faeden f).kopf.f)))
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.ret e hperm) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden f).stapel = caller :: rst)
  (hΛ : HeldIn Λ (offen (M.faeden f).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon f).lese Λ e.orte) (g : D.Fn)
  (hfg : (M.faeden f).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden f).spur) (hnw : caller.wartend = false) :
  HaeltInvG
    ({ speicher := s1.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := rst, kopf := caller, spur := s1.spur,
                log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)

end Gabbro.Grammatik
