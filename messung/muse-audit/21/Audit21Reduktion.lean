/-
  Lane-21 audit probe 2: reduction wrappers restate `reduktion_seriell`.

  Claim under test: `reduktion_maschine` (§5), `gen_reduktion` (§11), and
  `pc_reduktion` (§12) look like new reduction results, but under unfolding
  each is `reduktion_seriell` applied to a `Gesittet` bundle assembled from
  the same premises. The HB disjunction is inherited, not derived: the proof
  term mentions no mover, no commutativity, no order construction of its own.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `reduktion_maschine` is `reduktion_seriell` over derived `Gesittet`. -/
theorem audit21_reduktion_is_seriell (M : MaschinenLauf (D := D))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.run j₁ j₂ ∨ HB M.run j₂ j₁ :=
  reduktion_seriell M.run (gesittet_aus_maschine M) t₀ g₁ g₂ hne
    j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

/-- The machine wrapper agrees with the direct bridge call, by `rfl`. -/
theorem audit21_reduktion_agrees (M : MaschinenLauf (D := D))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    reduktion_maschine M t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂ =
      audit21_reduktion_is_seriell M t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂ :=
  rfl

/-
CUTS:
- This probe covers only the §§1-5 wrapper (`reduktion_maschine`).
  `gen_reduktion` (§11) and `pc_reduktion` (§12) have the same proof shape
  (direct application of `reduktion_seriell` to a same-premise `Gesittet`)
  but need live `GenErreichbar`/`PCReach` witnesses to state; not
  demonstrated here, marked UNVERIFIED in the report.
- Whether wrapper-equality counts as "progress" is an audit judgement; the
  `rfl` above is the checked evidence for the §§1-5 case.
-/
#print axioms audit21_reduktion_is_seriell
#print axioms audit21_reduktion_agrees
