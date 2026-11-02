module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.A.Teil6

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

set_option maxHeartbeats 4000000 in
theorem ownInv_step_travNext {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab) (inv : Expr D Γ Λ Ty.bool)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (i : Wert D (Ty.index (D.count t))) (is : List (Wert D (Ty.index (D.count t))))
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.trav t inv body (i :: is) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ inv.orte) (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur))
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
                                  (⟨true,
                                      (⟨Ty.index (D.count t) :: Γ,
                                          (⟨Λ, (Env.cons i ρ, GRest.dann body (GRest.travRest t inv body is k))⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D (Ty.index (D.count t) :: Γ) ×
                                                GRest D (vertragVon D (M.faeden u).kopf.f) true
                                                  (Ty.index (D.count t) :: Γ) Λ)⟩ :
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) ×
                                        (Λ : List (Res D)) ×
                                          Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                                RufRahmenG D },
                            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.speicher.globs
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
                  (⟨true,
                      (⟨Ty.index (D.count t) :: Γ,
                          (⟨Λ, (Env.cons i ρ, GRest.dann body (GRest.travRest t inv body is k))⟩ :
                            (Λ : List (Res D)) ×
                              Env D (Ty.index (D.count t) :: Γ) ×
                                GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
                        (Γ : Ctx) ×
                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_travNext hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_travFort {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab) (inv : Expr D Γ Λ Ty.bool)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (is : List (Wert D (Ty.index (D.count t)))) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (i : Wert D (Ty.index (D.count t))) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨true,
          (⟨Ty.index (D.count t) :: Γ,
              (⟨Λ, (Env.cons i ρ, GRest.travRest t inv body is k)⟩ :
                (Λ : List (Res D)) ×
                  Env D (Ty.index (D.count t) :: Γ) ×
                    GRest D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ)⟩ :
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
                                          (⟨Λ, (ρ, GRest.trav t inv body is k)⟩ :
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
                          (⟨Λ, (ρ, GRest.trav t inv body is k)⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_travFort hf ha ho hr) rfl rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_travDone {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (t : D.Tab) (inv : Expr D Γ Λ Ty.bool)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true (Ty.index (D.count t) :: Γ) Λ Λ)
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.trav t inv body [] k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ inv.orte) (hw : wahr? (eval σ₁ inv σ₁ ρ) = true)
  (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur))
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
                            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.speicher.globs
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
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_travDone hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannRetry {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Nat) (bis : Expr D Γ Λ Ty.bool)
  (body : Block D (vertragVon D (M.faeden u).kopf.f) true Γ Λ Λ)
  (ueber : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.retry n bis body ueber) rest) k)⟩ :
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
                                          (⟨Λ, (ρ, GRest.wieder n bis body ueber (GRest.dann rest k))⟩ :
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
                          (⟨Λ, (ρ, GRest.wieder n bis body ueber (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_retry hk hf ha ho hr) rfl rfl hrely

end Gabbro.Grammatik.ArenaOwnership.Machine
