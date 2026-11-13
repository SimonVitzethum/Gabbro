module

public import Grammatik.Logik.WP.Regeln2

public section

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- An invariant over passes left suffices. There is no progress assumption or
    decreasing user measure: the static bound pays for every body execution. -/
theorem while_regel (schritt : World D → Env D Γ → Ausgang V true Γ)
    (cond : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop)
    (hEnde : ∀ n σ ρ, I n σ ρ → (cond σ ρ).2 = false → Q (.ok (cond σ ρ).1 ρ))
    (hUeber : ∀ σ ρ, I 0 σ ρ → (cond σ ρ).2 = true → Q (ueberlauf (cond σ ρ).1 ρ))
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ → (cond σ ρ).2 = true →
      PassSchritt Q I n (schritt (cond σ ρ).1 ρ)) :
    ∀ n σ ρ, I n σ ρ → Q (whileLauf schritt cond ueberlauf n σ ρ) := by
  apply retry_regel schritt (fun σ ρ => ((cond σ ρ).1, !(cond σ ρ).2)) ueberlauf Q I
  · intro n σ ρ hi ht
    exact hEnde n σ ρ hi (by simpa using ht)
  · intro σ ρ hi ht
    exact hUeber σ ρ hi (by simpa using ht)
  · intro n σ ρ hi ht
    exact hSchritt n σ ρ hi (by simpa using ht)

/-- Completeness reuses retry's exact invariant, with the test polarity reversed. -/
theorem while_vollstaendig (schritt : World D → Env D Γ → Ausgang V true Γ)
    (cond : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) (Q : Ausgang V l Γ → Prop) :
    let I : Nat → World D → Env D Γ → Prop :=
      fun n σ ρ => Q (whileLauf schritt cond ueberlauf n σ ρ)
    (∀ n σ ρ, I n σ ρ → (cond σ ρ).2 = false → Q (.ok (cond σ ρ).1 ρ)) ∧
    (∀ σ ρ, I 0 σ ρ → (cond σ ρ).2 = true → Q (ueberlauf (cond σ ρ).1 ρ)) ∧
    (∀ n σ ρ, I (n + 1) σ ρ → (cond σ ρ).2 = true →
      PassSchritt Q I n (schritt (cond σ ρ).1 ρ)) := by
  obtain ⟨he, hu, hs⟩ := retry_vollstaendig schritt
    (fun σ ρ => ((cond σ ρ).1, !(cond σ ρ).2)) ueberlauf Q
  exact ⟨fun n σ ρ hi ht => he n σ ρ hi (by simpa using ht),
    fun σ ρ hi ht => hu σ ρ hi (by simpa using ht),
    fun n σ ρ hi ht => hs n σ ρ hi (by simpa using ht)⟩

/-- The statement-level rule reads the condition's footprint before testing it,
    including on exhaustion. Body and handler keep the same linear resources. -/
theorem wpS_wloop (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ : List (Res D)} (n : Nat) (c : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueberlauf : Block D V l Γ Λ Λ)
    (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop)
    (σ : World D) (ρ : Env D Γ) (hStart : I n σ ρ)
    (hEnde : ∀ n σ ρ, I n σ ρ →
      wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false →
      Q (.ok (σ.lese Λ c.orte) ρ))
    (hUeber : ∀ σ ρ, I 0 σ ρ →
      wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true →
      wpB O passes R ueberlauf Q (σ.lese Λ c.orte) ρ)
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ →
      wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true →
      wpB O passes R body (PassSchritt Q I n) (σ.lese Λ c.orte) ρ) :
    wpS O passes R (.wloop n c body ueberlauf) Q σ ρ := by
  unfold wpS
  rw [execStmt_wloop]
  exact while_regel _ _ _ Q I hEnde hUeber hSchritt n σ ρ hStart

end Gabbro.Grammatik.WP
