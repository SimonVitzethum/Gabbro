/-
  Audit probe F7: `envErhalt_refl/symm/trans`, `kette_erhaelt_env`,
  `fadenEnv_kette_erhaelt`, `fadenEnv_letzte_erhaelt` restate `Iff` / `kette_erhaelt`
  under a new name (pattern a); `envErhalt_aus_weltErhalt` assumes the very
  equivalence it "lifts".

  Demonstrations: each proof is `rfl`, `Iff.symm`, `Iff.trans`, or a direct
  application of `kette_erhaelt`. The `EnvErhalt` wrapper
  (`Q vor ρ ↔ Q nach ρ`) adds the environment `ρ` only to hold it fixed, so
  no environment reasoning happens. `envErhalt_aus_weltErhalt` takes
  `hQ : ∀ σ ρ, Q σ ρ ↔ P σ` -- i.e. "Q ignores the environment" -- as a
  premise and concludes environment preservation: the conclusion is the
  premise restricted to two worlds.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `envErhalt_refl` is `rfl` on the unfolded iff. -/
example (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    (σ : World D) (ρ : Env D Γ) : EnvErhalt Γ Q σ σ ρ :=
  Iff.rfl

/-- `envErhalt_symm` is `Iff.symm`. -/
example (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {vor nach : World D} {ρ : Env D Γ}
    (h : EnvErhalt Γ Q vor nach ρ) : EnvErhalt Γ Q nach vor ρ :=
  Iff.symm h

/-- `envErhalt_trans` is `Iff.trans`. -/
example (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {a b c : World D} {ρ : Env D Γ}
    (h1 : EnvErhalt Γ Q a b ρ) (h2 : EnvErhalt Γ Q b c ρ) :
    EnvErhalt Γ Q a c ρ :=
  Iff.trans h1 h2

/-- `kette_erhaelt_env` is `kette_erhaelt` with `ρ` fixed. -/
example (welten : List (World D)) (schrittFaden : List Faden)
    (hKette : welten.length = schrittFaden.length + 1)
    (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ) (ρ : Env D Γ)
    (hInit : ∀ σ₀ : World D, welten[0]? = some σ₀ → Q σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      schrittFaden[k]? = some g → welten[k]? = some vor →
        welten[k + 1]? = some nach → EnvErhalt Γ Q vor nach ρ) :
    ∀ (k : Nat) (σ : World D), welten[k]? = some σ → Q σ ρ :=
  kette_erhaelt welten schrittFaden hKette (fun σ => Q σ ρ) hInit hStep

/-- `envErhalt_aus_weltErhalt`: with `hQ` saying `Q` ignores `ρ`, the
    conclusion is `hQ vor ▸ hQ nach ▸ hP` -- no environment step is taken. -/
example (Γ : Ctx) (P : World D → Prop)
    (Q : EnvZusicherung (D := D) Γ)
    (hQ : ∀ (σ : World D) (ρ : Env D Γ), Q σ ρ ↔ P σ)
    {vor nach : World D} (hP : P vor ↔ P nach) (ρ : Env D Γ) :
    EnvErhalt Γ Q vor nach ρ := by
  unfold EnvErhalt
  rw [hQ vor ρ, hQ nach ρ]
  exact hP

/-
CUTS:
- Not claimed: the wrappers are false. Claimed: they are renamings whose
  proofs use no fact about environments, scopes, or threads (pattern a), and
  the one "lifting" lemma assumes environment-independence outright.
- `allgemeinStabil_env` inherits the `hInv`/`hDeck`-unused finding (F2);
  not re-proved here.
-/
#print axioms Gabbro.Grammatik.envErhalt_refl
#print axioms Gabbro.Grammatik.kette_erhaelt_env
#print axioms Gabbro.Grammatik.envErhalt_aus_weltErhalt
