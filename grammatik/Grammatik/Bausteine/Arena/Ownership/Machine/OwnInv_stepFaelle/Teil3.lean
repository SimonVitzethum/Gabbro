module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil2

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannOnOptionNone {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Int) (o : Expr D Γ Λ (Ty.opt n))
  (p : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.index n :: Γ) Λ Λ')
  (a : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onOption o p a) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ o.orte) (hv : eval σ₁ o σ₁ ρ = none) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur))
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
                                          (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
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
                          (⟨Λ, (ρ, GRest.dann a (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_onOptionNone hk hf ha ho hr (meta_lese _ _ _ hs₁)) (by subst hs₁; rfl) rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannOnTagSome {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (cs : List (Option (Int × Int))) (v : Expr D Γ Λ (Ty.sum cs))
  (arms : Arms D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ' cs)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onTag v arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ v.orte) (lo hi : Int)
  (b : Block D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
  (hw :
    armWahlG arms (eval σ₁ v σ₁ ρ) =
      (⟨some (lo, hi), (b, nutz)⟩ :
        (c : Option (Int × Int)) × Block D (vertragVon D (M.faeden u).kopf.f) l (ArmCtx Γ c) Λ Λ' × Nutzlast c))
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
                                      (⟨Ty.int lo hi :: Γ,
                                          (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                                            (Λ : List (Res D)) ×
                                              Env D (Ty.int lo hi :: Γ) ×
                                                GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo hi :: Γ) Λ)⟩ :
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
                      (⟨Ty.int lo hi :: Γ,
                          (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k).schrumpf)⟩ :
                            (Λ : List (Res D)) ×
                              Env D (Ty.int lo hi :: Γ) ×
                                GRest D (vertragVon D (M.faeden u).kopf.f) l (Ty.int lo hi :: Γ) Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_onTagSome hk hf ha ho hr (meta_lese _ _ _ hs₁) _ hw) (by subst hs₁; rfl) rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannOnTagNone {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (cs : List (Option (Int × Int))) (v : Expr D Γ Λ (Ty.sum cs))
  (arms : Arms D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ' cs)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onTag v arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ v.orte) (b : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (nutz : Nutzlast none)
  (hw :
    armWahlG arms (eval σ₁ v σ₁ ρ) =
      (⟨none, (b, nutz)⟩ :
        (c : Option (Int × Int)) × Block D (vertragVon D (M.faeden u).kopf.f) l (ArmCtx Γ c) Λ Λ' × Nutzlast c))
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
                                          (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k))⟩ :
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
                          (⟨Λ, (armEnv nutz ρ, GRest.dann b (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  exact fin (run_onTagNone hk hf ha ho hr (meta_lese _ _ _ hs₁) _ hw) (by subst hs₁; rfl) rfl hrely

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannOnGrund {D : Deklaration} {P : Programm D}
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
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Nat) (r : Expr D Γ Λ (Ty.why n))
  (arms : GrundArms D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ' n)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.onWhy r arms) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (σ₁ : World D) (hs₁ : σ₁ = (M.weltVon u).lese Λ r.orte) (b : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (hw : grundWahlG arms (eval σ₁ r σ₁ ρ) = b) (neu : List (Ereignis D)) (hneu : σ₁.spur = neu ++ (M.faeden u).spur)
  (hΛ : HeldIn Λ (offen (M.faeden u).spur))
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
                                          (⟨Λ, (ρ, GRest.dann b (GRest.dann rest k))⟩ :
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
                          (⟨Λ, (ρ, GRest.dann b (GRest.dann rest k))⟩ :
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) ×
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                RufRahmenG D },
            spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, g, hk, hf, hr⟩ := head_run hH rfl
  subst hw
  exact fin (run_onWhy hk hf ha ho hr (meta_lese _ _ _ hs₁) _) (by subst hs₁; rfl) rfl hrely

end Gabbro.Grammatik.ArenaOwnership.Machine
