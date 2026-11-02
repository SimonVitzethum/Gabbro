module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.RufSchrittG_haeltInvFaelle.Teil5

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannRetBind {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (lk : Bool) (Γk : Ctx)
  (Λk Λk'' : List (Res D)) (e : ErgExpr D Γk Λk (vertragVon D (M.faeden f).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden f).kopf.f)))
  (restk : Block D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk Λk'')
  (kk : GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk'') (ρ : Env D Γk)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.dann (Block.cons (Stmt.ret e hperm) restk) kk)⟩ :
                (Λ : List (Res D)) × Env D Γk × GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) lk Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden f).stapel = caller :: rst) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (τ : Ty) (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
  (hcaller :
    caller.rest =
        (⟨l,
            (⟨Γ,
                (⟨Λ, (ρc, GRest.wartet restb k)⟩ :
                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
          (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) ∨
      ∃ n err,
        caller.rest =
          (⟨l,
              (⟨Γ,
                  (⟨Λ, (ρc, GRest.wartetSonst n err restb k)⟩ :
                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
            (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ))
  (hΛ : HeldIn Λk (offen (M.faeden f).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon f).lese Λk e.orte) (g : D.Fn)
  (hfg : (M.faeden f).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (he : D.erg g = some τ) (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden f).spur) :
  HaeltInvG
    ({ speicher := s1.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := rst,
                kopf :=
                  { f := caller.f, rho := caller.rho, s0 := caller.s0,
                    rest :=
                      (⟨l,
                          (⟨τ :: Γ,
                              (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                    RufRahmenG D },
                spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
    h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hck : (GRest.dann restb (.schrumpf k) :
      GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩
    · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
  refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
  intro L hL
  rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_rueckConsBind {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (lk : Bool) (Γk : Ctx) (Λk : List (Res D))
  (e : ErgExpr D Γk Λk (vertragVon D (M.faeden f).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden f).kopf.f)))
  (restk : Endblock D (vertragVon D (M.faeden f).kopf.f) lk Γk Λk) (ρ : Env D Γk)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.ende (Endblock.cons (Stmt.ret e hperm) restk))⟩ :
                (Λ : List (Res D)) × Env D Γk × GRest D (vertragVon D (M.faeden f).kopf.f) lk Γk Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) lk Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden f).stapel = caller :: rst) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (τ : Ty) (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
  (hcaller :
    caller.rest =
        (⟨l,
            (⟨Γ,
                (⟨Λ, (ρc, GRest.wartet restb k)⟩ :
                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
          (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) ∨
      ∃ n err,
        caller.rest =
          (⟨l,
              (⟨Γ,
                  (⟨Λ, (ρc, GRest.wartetSonst n err restb k)⟩ :
                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
            (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ))
  (hΛ : HeldIn Λk (offen (M.faeden f).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon f).lese Λk e.orte) (g : D.Fn)
  (hfg : (M.faeden f).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (he : D.erg g = some τ) (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden f).spur) :
  HaeltInvG
    ({ speicher := s1.speicher,
          faeden :=
            rufUpdateG M.faeden f
              { stapel := rst,
                kopf :=
                  { f := caller.f, rho := caller.rho, s0 := caller.s0,
                    rest :=
                      (⟨l,
                          (⟨τ :: Γ,
                              (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                    RufRahmenG D },
                spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG f neu, start := M.start : RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
    h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hck : (GRest.dann restb (.schrumpf k) :
      GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩
    · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
  refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
  intro L hL
  rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL

set_option maxHeartbeats 4000000 in
theorem rufSchrittG_haeltInv_dannRegLies {D : Deklaration} {P : Programm D} {O : Orakel D}
  {passes : Nat} (hO : GutO O) {M : RufMaschineG D} {f : Faden} (h : HaeltInvG (M.faeden f))
  (hk0 : GRest.kette (D.haelt (M.faeden f).kopf.f) (M.faeden f).kopf.rest.snd.snd.snd.snd)
  (hh0 : HeldIn (M.faeden f).kopf.rest.snd.snd.fst (offen (M.faeden f).spur)) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
  (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
  (rest : Block D (vertragVon D (M.faeden f).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden f).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regRead r hk rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (Sum.inr (Sum.inl r)))) = some v)
  (hz : D.rzusage r v = true) (hΛ : HeldIn Λ (offen (M.faeden f).spur)) :
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
                spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden f).spur, log := (M.faeden f).log :
                RufFadenG D },
          lauf := M.lauf ++ rufEigenG f [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start :
          RufMaschineG D }.faeden
      f) := by
  simp only [rufUpdateG_self]
  have hk := kette_von hhead hk0
  have hh := heldIn_von hhead hh0
  exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh


end Gabbro.Grammatik
