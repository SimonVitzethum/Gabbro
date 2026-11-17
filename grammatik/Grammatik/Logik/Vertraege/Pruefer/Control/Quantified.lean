module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Arguments

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Invarianten.Modell

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

def allEnvironments {context : Context A next} (budget : Nat) (Γ : Ctx)
    (target : Env D Γ → A → VC.Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ more (larger : next ≤ more) (symbols : SymEnv D Nat Γ), symbols.Bounded more →
      Except Frag.Refusal (Certificate (context.weaken larger) (fun valuation item runtime world =>
        ∀ actual, symbols.Realizes valuation world actual → target actual item runtime world))) :
    Except Frag.Refusal (Certificate context (fun _ item runtime world => ∀ actual, target actual item runtime world)) := do
  let domain ← parameters (D := D) budget next Γ
  let checks ← allCertificates context domain.templates.attach
    (fun entry valuation item runtime world => ∀ extended,
      (∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key) →
      ∀ actual, entry.val.Realizes extended world actual → target actual item runtime world)
    (fun entry => do
      let post ← compile domain.next domain.ordered entry.val (domain.bounded entry.val entry.property)
      return {
        formula := universalClosure (argumentKeys next domain.next) (.imp (environmentBounds entry.val) post.formula)
        sound := fun valuation item present runtime world valid extended agrees actual realized => by
          have ready := closure_transfer (argumentKeys next domain.next)
            (.imp (environmentBounds entry.val) post.formula) (values valuation world) (values extended world) valid (by
              intro key _ absent
              cases key with
              | inl memory => rfl
              | inr key => exact (agrees key (outside_argumentKeys next domain.next key absent)).symm)
          have frozen := (context.stable valuation extended item
            (fun key before => (agrees key (Or.inl before)).symm)).mp present
          exact post.sound extended item frozen runtime world
            (ready (environmentBounds_sound entry.val extended world actual realized)) actual realized })
  return {
    formula := checks.formula
    sound := fun valuation item present runtime world valid actual => by
      obtain ⟨symbols, member, chosen, realized, preserved⟩ := domain.cover world actual valuation
      let extended : Assignment Nat := fun key => if key < domain.next then chosen key else valuation key
      have current := (symbols.realizes_congr domain.next (domain.bounded symbols member) chosen extended
        (fun key before => by simp only [extended, before, ↓reduceIte]) world world actual).mp realized
      have agrees : ∀ key, key < next ∨ domain.next ≤ key → extended key = valuation key := by
        intro key outside
        rcases outside with before | after
        · have within := Nat.lt_of_lt_of_le before domain.ordered
          simpa only [extended, within, ↓reduceIte] using preserved key before
        · have beyond : ¬ key < domain.next := Nat.not_lt.mpr after
          simp only [extended, beyond, ↓reduceIte]
      exact checks.sound valuation item present runtime world valid ⟨symbols, member⟩ (List.mem_attach _ _)
        extended agrees actual current }

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
