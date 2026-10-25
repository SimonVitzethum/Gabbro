import Grammatik.Zielsatz.Einbettung.Werkzeug

/-!
  File:      Grammatik/Zielsatz/Einbettung/Simulation.lean
  Subject:   **A body of `D` runs beside its image in `D'`** (stage E2c, the simulation).

  For every statement, block, end block and arm list of `D`: from a pair of worlds under the keys
  and a pair of environments, there are more keys and ONE outcome of `D` such that the body, run
  against the handlers every map `Φ` that repeats the keys induces, ends in that outcome, and the
  outcome stands beside the outcome of the image run against the handlers of `D'` (`AusRel`,
  `EndRel`). By structural recursion over the syntax; reads go through `lese_eval'`, answers from
  outside through the keys, loops through `Schleifen.lean`.

  What the handlers of `D'` must give (`Bed`): the neutral trace piece, the atomic environment in
  its class with no more shared atomics on the image than `D` has, the lock moves in their class
  with the image lock protecting the images of the lock's carriers under the same invariant, and a
  call handler that blames, at an image function, only images (true of every handler the goal
  statement's obligation quantifies over: `torRuf` blames the callee it gates, and the others
  blame no caller).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Values that do not move -/

@[simp] theorem valE_int {a b : Int} (v : Wert D (.int a b)) : E.valE (.int a b) v = v := rfl
@[simp] theorem valE_bool (v : Wert D .bool) : E.valE .bool v = v := rfl
@[simp] theorem valE_opt {n : Int} (v : Wert D (.opt n)) : E.valE (.opt n) v = v := rfl
@[simp] theorem valE_sum {cs : List (Option (Int × Int))} (v : Wert D (.sum cs)) : E.valE (.sum cs) v = v := rfl
@[simp] theorem valE_why {n : Nat} (v : Wert D (.why n)) : E.valE (.why n) v = v := rfl
@[simp] theorem valE_fl {lo hi : Int × Int} (v : Wert D (.fl lo hi)) : E.valE (.fl lo hi) v = v := rfl

variable (hZ : ZeigerfreiD D) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)

/-- **What the run of an image needs of the handlers of `D'`.** -/
structure Bed : Prop where
  pad : PadOk pad
  havocA : HavocA T' A'
  atom : ∀ c, T' (E.ortE c) → T c
  havocU : HavocOk S' U'
  orte : ∀ L, S'.orte (E.lock L) = (S.orte L).map E.ortE
  inv : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')
  vorb : ∀ g σ ρ g', R' (E.fn g) σ ρ = .logik (.vorbedingung g') → ∃ g₀, g' = E.fn g₀

/-- An end block of `D` beside an end block of `D'`, for every map that repeats the keys. -/
def EndSim {V : Vertrag D} {l : Bool} {Δ Δ' : Ctx}
    (lauf : Phi D D' → World D → Env D Δ → EndAusgang V l Δ)
    (lauf' : World D' → Env D' Δ' → EndAusgang (E.vertragE V) l Δ') : Prop :=
  ∀ (M : Keys D D') (σ : World D) (σ' : World D') (ρ : Env D Δ) (ρ' : Env D' Δ'),
    E.Inv M σ σ' → E.EnvR ρ ρ' →
    ∃ (M₁ : Keys D D') (o : EndAusgang V l Δ), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → lauf Φ σ ρ = o) ∧ E.EndRel M₁ o (lauf' σ' ρ')

/-! ## Transports on the side of `D'` -/

section Um

variable {V : Vertrag D} {l : Bool} {Δ Δ₁ Δ₂ : Ctx}

theorem koerperSim_um (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → Ausgang V l Δ)
    (lauf' : World D' → Env D' Δ₁ → Ausgang (E.vertragE V) l Δ₁) (hs : E.KoerperSim lauf lauf') :
    E.KoerperSim lauf (fun σ' ρ' => castAus h (lauf' σ' (castE h.symm ρ'))) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um h.symm ρ ρ').mpr hρ)
  exact ⟨M₁, o, hs1, hΦ, (E.ausRel_um h o _).mpr hR⟩

theorem endSim_um (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → EndAusgang V l Δ)
    (lauf' : World D' → Env D' Δ₁ → EndAusgang (E.vertragE V) l Δ₁) (hs : E.EndSim lauf lauf') :
    E.EndSim lauf (fun σ' ρ' => castEnd h (lauf' σ' (castE h.symm ρ'))) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um h.symm ρ ρ').mpr hρ)
  exact ⟨M₁, o, hs1, hΦ, (E.endRel_um h o _).mpr hR⟩

end Um

/-! ## A read with the read list of the image as `D'` writes it -/

theorem lese_eval' {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') {T' : D'.Tab ⊕ D'.Glob → Prop} {A' : AUmwelt D'} (hA' : HavocA T' A')
    (hT : ∀ c, T' (E.ortE c) → T c) (Λ : List (Res D)) (Λ' : List (Res D'))
    (X : List (D.Tab ⊕ D.Glob)) (X' : List (D'.Tab ⊕ D'.Glob)) (hX : X.map E.ortE = X') :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → leseA (E.aumweltΦ hZ Φ T A') σ Λ X = σ₁) ∧
      E.Inv M₁ σ₁ (leseA A' σ' Λ' X') ∧
      ∀ {Γ : Ctx} {Λ₀ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ₀ τ) (ρ : Env D Γ),
        eval (leseA A' σ' Λ' X') (exE E e) (leseA A' σ' Λ' X') (E.envE ρ) =
          E.valE τ (eval σ₁ e σ₁ ρ) := by
  subst hX
  exact E.lese_eval hZ h T hA' hT Λ Λ' X

/-- **A boundary check beside its image.** -/
theorem pruef_sim {T' : D'.Tab ⊕ D'.Glob → Prop} {A' : AUmwelt D'} (hA' : HavocA T' A')
    (hT : ∀ c, T' (E.ortE c) → T c) {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) :
    E.PruefSim (fun Φ σ ρ => let σ := leseA (E.aumweltΦ hZ Φ T A') σ Λ c.orte; (σ, wahr? (eval σ c σ ρ)))
      (fun σ ρ => let σ := leseA A' σ (Λ.map E.resE) (exE E c).orte; (σ, wahr? (eval σ (exE E c) σ ρ))) := by
  intro M σ σ' ρ ρ' h hρ
  obtain rfl := E.envR_eq ρ ρ' hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T h hA' hT Λ (Λ.map E.resE) c.orte
    (exE E c).orte (E.orte_exE c).symm
  refine ⟨M₁, σ₁, wahr? (eval σ₁ c σ₁ ρ), hs, fun Φ hP => ?_, hI, ?_⟩
  · simp only [hΦ Φ hP]
  · simp only [hev]; rfl

end Einbettung

end Gabbro.Grammatik.Einbettung
