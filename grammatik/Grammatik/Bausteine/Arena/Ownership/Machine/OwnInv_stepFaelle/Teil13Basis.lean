module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil12

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

set_option maxHeartbeats 4000000 in
theorem ownInv_step_rueckConsBind {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} (hO : GutO O) (hc : Checked P A I)
  {M : RufMaschineG D} {u : Faden} (s : State) (hag : s.agrees A (M.speicher.welt []))
  (hfo : A.FreiOk (M.speicher.welt [])) (hd : s.Disciplined (depthOf M))
  (hth : ∀ (t : Faden), ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
  (hW : MetaSame A (M.speicher.welt []) (M.weltVon u)) (ha : s.agrees A (M.weltVon u)) (ho : A.FreiOk (M.weltVon u))
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (fin :
    ∀ {M' : RufMaschineG D} {σ' : World D}
      {x' : (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
      {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D} {spur' : List (Ereignis D)}
      {log' : List (RufEreignisF D)},
      Next A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) σ' (M.faeden u).kopf.f
          x' →
        M'.speicher = σ'.speicher →
          M'.faeden =
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf := { f := (M.faeden u).kopf.f, rho := rho', s0 := s0', rest := x' : RufRahmenG D },
                  spur := spur', log := log' : RufFadenG D } →
            (∀ (t : Faden),
                t ≠ u →
                  ∀ (g : D.Glob),
                    pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g →
                      M'.speicher.globs g = M.speicher.globs g) →
              OwnInv A I M')
  (lk : Bool) (Γk : Ctx) (Λk : List (Res D)) (e : ErgExpr D Γk Λk (vertragVon D (M.faeden u).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden u).kopf.f)))
  (restk : Endblock D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk) (ρ : Env D Γk)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.ende (Endblock.cons (Stmt.ret e hperm) restk))⟩ :
                (Λ : List (Res D)) × Env D Γk × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γk Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden u).stapel = caller :: rst) (l : Bool) (Γ : Ctx)
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
  (hΛ : HeldIn Λk (offen (M.faeden u).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon u).lese Λk e.orte) (g : D.Fn)
  (hfg : (M.faeden u).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden u).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden u).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (he : D.erg g = some τ) (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden u).spur)
  (hrely :
    ∀ (t : Faden),
      t ≠ u →
        ∀ (g_1 : D.Glob),
          pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g_1 →
            { speicher := s1.speicher,
                      faeden :=
                        rufUpdateG M.faeden u
                          { stapel := rst,
                            kopf :=
                              { f := caller.f, rho := caller.rho, s0 := caller.s0,
                                rest :=
                                  (⟨l,
                                      (⟨τ :: Γ,
                                          (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log :
                            RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.speicher.globs
                g_1 =
              M.speicher.globs g_1) :
  OwnInv A I
    { speicher := s1.speicher,
      faeden :=
        rufUpdateG M.faeden u
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
            spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
  obtain ⟨c2, hs, _⟩ := hor.stmtEnde
  have hcheck := os_top hs
  have hdu : depthOf M u = rst.length + 1 := by
    show (M.faeden u).stapel.length = _
    rw [hpop]; rfl
  have hsusp := caller_susp (hth u).2 hpop
  subst hfg
  subst hv
  have hres := ret_result hf hcheck s1 s1
  rw [show (M.faeden u).stapel.length = rst.length + 1 from hdu] at hres
  rcases hcaller with hc' | ⟨n, err, hc'⟩
  · rw [hc'] at hsusp
    exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
      (resume_bind hd hdu hsusp (Or.inl rfl) _ he hres)
  · rw [hc'] at hsusp
    exact ownInv_pop hag hfo hd hth hpop (by subst hs1; rfl) rfl rfl
      (resume_bind hd hdu hsusp (Or.inr ⟨n, err, rfl⟩) _ he hres)

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannRegLies {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} (hO : GutO O) (hc : Checked P A I)
  {M : RufMaschineG D} {u : Faden} (s : State) (hag : s.agrees A (M.speicher.welt []))
  (hfo : A.FreiOk (M.speicher.welt [])) (hd : s.Disciplined (depthOf M))
  (hth : ∀ (t : Faden), ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
  (hW : MetaSame A (M.speicher.welt []) (M.weltVon u)) (ha : s.agrees A (M.weltVon u)) (ho : A.FreiOk (M.weltVon u))
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (fin :
    ∀ {M' : RufMaschineG D} {σ' : World D}
      {x' : (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
      {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D} {spur' : List (Ereignis D)}
      {log' : List (RufEreignisF D)},
      Next A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) σ' (M.faeden u).kopf.f
          x' →
        M'.speicher = σ'.speicher →
          M'.faeden =
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf := { f := (M.faeden u).kopf.f, rho := rho', s0 := s0', rest := x' : RufRahmenG D },
                  spur := spur', log := log' : RufFadenG D } →
            (∀ (t : Faden),
                t ≠ u →
                  ∀ (g : D.Glob),
                    pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g →
                      M'.speicher.globs g = M.speicher.globs g) →
              OwnInv A I M')
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (r : D.Reg) (hk' : (D.rklasse r).lesbar = true)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regRead r hk' rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon u).fragt (Sum.inr (Sum.inl r)))) = some v)
  (hz : D.rzusage r v = true) (hΛ : HeldIn Λ (offen (M.faeden u).spur))
  (hrely :
    ∀ (t : Faden),
      t ≠ u →
        ∀ (g : D.Glob),
          pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g →
            { speicher := M.speicher,
                      faeden :=
                        rufUpdateG M.faeden u
                          { stapel := (M.faeden u).stapel,
                            kopf :=
                              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                                rest :=
                                  (⟨l,
                                      (⟨D.rtyp r :: Γ,
                                          (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D (D.rtyp r :: Γ) ×
                                                GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden u).spur, log := (M.faeden u).log :
                            RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start :
                      RufMaschineG D }.speicher.globs
                g =
              M.speicher.globs g) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          { stapel := (M.faeden u).stapel,
            kopf :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                rest :=
                  (⟨l,
                      (⟨D.rtyp r :: Γ,
                          (⟨Λ, (Env.cons v ρ, GRest.dann rest k.schrumpf)⟩ :
                            (Λ : List (Res D)) ×
                              Env D (D.rtyp r :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := Ereignis.fremd (Sum.inr (Sum.inl r)) :: (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u [Ereignis.fremd (Sum.inr (Sum.inl r))], start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_regRead hk hf ha ho hr v) rfl rfl hrely


end Gabbro.Grammatik.ArenaOwnership.Machine
