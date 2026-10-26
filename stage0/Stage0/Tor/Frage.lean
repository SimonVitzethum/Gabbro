/-
  File:      stage0/Stage0/Tor/Frage.lean
  Subject:   The question thread `f` asks outside in its next step, if it asks one: a foreign call at its head
             (`axiomCall`, `bindAxiom`, `bindAxiomElse`, at the head of an end block or of a `dann` block), with the
             world it asks in (`σ₁.fragt`, the reads of the arguments first) and the argument values -- exactly what
             `axiomAntwort`/`axiomAntwortSonst` hand the oracle in that step.
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **The question of thread `f`'s next step**, if it asks one. -/
def frage? (M : RufMaschineG D) (f : Faden) : Option (Σ a : D.Ax, World D × Env D (D.aparams a)) :=
  match (M.faeden f).kopf.rest with
  | ⟨_, _, Λ, ρ, .ende (.cons (.axiomCall a args ..) _)⟩ => q Λ ρ a args
  | ⟨_, _, Λ, ρ, .dann (.cons (.axiomCall a args ..) _) _⟩ => q Λ ρ a args
  | ⟨_, _, Λ, ρ, .ende (.bindAxiom a args ..)⟩ => q Λ ρ a args
  | ⟨_, _, Λ, ρ, .ende (.bindAxiomElse a args ..)⟩ => q Λ ρ a args
  | ⟨_, _, Λ, ρ, .dann (.bindAxiom a args ..) _⟩ => q Λ ρ a args
  | ⟨_, _, Λ, ρ, .dann (.bindAxiomElse a args ..) _⟩ => q Λ ρ a args
  | _ => none
where
  q {Γ : Ctx} (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) :
      Option (Σ a : D.Ax, World D × Env D (D.aparams a)) :=
    let σ₁ := (M.weltVon f).lese Λ args.orte
    some ⟨a, σ₁.fragt (.inl a), evalArgs σ₁ args σ₁ ρ⟩

end Gabbro.Stage0
