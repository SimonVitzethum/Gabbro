module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The atomic environment -/

/-- **An atomic environment**: the world a read of the list `X` continues from, as a function of
    `X` and the world after the read events. -/
abbrev AUmwelt (D : Deklaration) := List (D.Tab ⊕ D.Glob) → World D → World D

/-- **The class of atomic environments over the set `T`**: the trace stays, and only carriers
    that are READ (in `X`) AND in `T` may change. -/
def HavocA (T : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) : Prop :=
  ∀ X σ, (A X σ).spur = σ.spur ∧ ∀ c, ¬ (c ∈ X ∧ T c) → TraegerGleich (A X σ).speicher σ.speicher c

/-- A read through the atomic environment. -/
def leseA (A : AUmwelt D) (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    World D :=
  A X (σ.lese Λ X)

/-- The identity environment. -/
def idA : AUmwelt D := fun _ σ => σ

theorem havocA_id (T : D.Tab ⊕ D.Glob → Prop) : HavocA T (idA (D := D)) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

theorem havocA_mono {T T' : D.Tab ⊕ D.Glob → Prop} (h : ∀ c, T c → T' c) {A : AUmwelt D}
    (hA : HavocA T A) : HavocA T' A :=
  fun X σ => ⟨(hA X σ).1, fun c hc => (hA X σ).2 c fun ⟨h1, h2⟩ => hc ⟨h1, h (c) h2⟩⟩

/-- **A read of carriers outside `T` is no havoc.** -/
theorem leseA_frei {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A)
    {X : List (D.Tab ⊕ D.Glob)} (hX : ∀ c ∈ X, ¬ T c) (σ : World D) (Λ : List (Res D)) :
    leseA A σ Λ X = σ.lese Λ X :=
  world_ext (fun c => (hA X (σ.lese Λ X)).2 c fun ⟨h1, h2⟩ => hX c h1 h2) (hA X _).1

theorem leseA_id (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    leseA idA σ Λ X = σ.lese Λ X := by rfl

theorem leseA_spur (A : AUmwelt D) {T : D.Tab ⊕ D.Glob → Prop} (hA : HavocA T A) (σ : World D)
    (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) : (leseA A σ Λ X).spur = (σ.lese Λ X).spur :=
  (hA X _).1

/-! ## 2. Consuming selection through the atomic environment -/

/-- One consuming selection round through `A`: like `verbrauchSel`, with
    every read going through `leseA`. Off `T` (`leseA_frei`) this is
    `verbrauchSel`. -/
def verbrauchSelA {Γ : Ctx} {Λ : List (Res D)} (A : AUmwelt D)
    (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (σ : World D) (ρ : Env D Γ) :
    World D × Option (Wert D (.index (D.count t))) × Bool :=
  let σr := leseA A σ Λ (member.orte ++ edge.orte)
  (σr, verbrauchWahl (alleIndizes (D.count t))
    (fun k => wahr? (eval σr member σr (.cons k ρ)))
    (fun j k => wahr? (eval σr edge σr (.cons j (.cons k ρ))))
    (fun j k => decide (j.n = k.n)),
   !((alleIndizes (D.count t)).all fun k =>
      !(wahr? (eval σr member σr (.cons k ρ)))))

/-! ## 3. The semantics -/

end Gabbro.Grammatik
