module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil5

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannLocks {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (L : D.Lock) (hrk : ∀ (M : D.Lock), Res.held M ∈ Λ → D.rang M < D.rang L)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.locks L hrk body) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hself : ¬L ∈ offen (M.faeden u).spur) (hrang : ∀ (K : D.Lock), K ∈ offen (M.faeden u).spur → D.rang K < D.rang L)
  (hfrei : RufFreiG M u L)
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
                                      (⟨Γ,
                                          (⟨Res.held L :: Λ, (ρ, GRest.dann body (GRest.frei L (GRest.dann rest k)))⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := Ereignis.nimmt L (offen (M.faeden u).spur) :: (M.faeden u).spur,
                            log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u [Ereignis.nimmt L (offen (M.faeden u).spur)], start := M.start :
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
                      (⟨Γ,
                          (⟨Res.held L :: Λ, (ρ, GRest.dann body (GRest.frei L (GRest.dann rest k)))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := Ereignis.nimmt L (offen (M.faeden u).spur) :: (M.faeden u).spur, log := (M.faeden u).log :
            RufFadenG D },
      lauf := M.lauf ++ rufEigenG u [Ereignis.nimmt L (offen (M.faeden u).spur)], start := M.start :
      RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_locks hk hf ha ho hr (MetaSame.refl A _)) rfl rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_freiGib {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (L : D.Lock) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Res.held L :: Λ, (ρ, GRest.frei L k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
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
                                      (⟨Γ,
                                          (⟨Λ, (ρ, k)⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := Ereignis.gibt L :: (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u [Ereignis.gibt L], start := M.start :
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
                      (⟨Γ,
                          (⟨Λ, (ρ, k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := Ereignis.gibt L :: (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u [Ereignis.gibt L], start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_frei hk hf ha ho hr) rfl rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_schrumpfVergiss {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (v : Wert D τ)
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨τ :: Γ,
              (⟨Λ, (Env.cons v ρ, k.schrumpf)⟩ :
                (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
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
                                      (⟨Γ,
                                          (⟨Λ, (ρ, k)⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf, start := M.start : RufMaschineG D }.speicher.globs
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
                      (⟨Γ,
                          (⟨Λ, (ρ, k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_schrumpf hf ha ho hr) rfl rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannTrav {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (t : D.Tab) (inv : Expr D Γ Λ Ty.bool)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.traverse t inv body) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hrely :
    ∀ (t_1 : Faden),
      t_1 ≠ u →
        ∀ (g : D.Glob),
          pendWord A (M.faeden t_1).kopf.rest.snd.snd.snd.snd = some g →
            { speicher := M.speicher,
                      faeden :=
                        rufUpdateG M.faeden u
                          { stapel := (M.faeden u).stapel,
                            kopf :=
                              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                                rest :=
                                  (⟨l,
                                      (⟨Γ,
                                          (⟨Λ,
                                              (ρ,
                                                GRest.trav t inv body (alleIndizes (D.count t)) (GRest.dann rest k))⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf, start := M.start : RufMaschineG D }.speicher.globs
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
                      (⟨Γ,
                          (⟨Λ, (ρ, GRest.trav t inv body (alleIndizes (D.count t)) (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_traverse hk hf ha ho hr _) rfl rfl hrely

end Gabbro.Grammatik.ArenaOwnership.Machine
