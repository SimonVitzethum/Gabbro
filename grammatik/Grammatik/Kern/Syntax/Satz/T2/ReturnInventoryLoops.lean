/- Tracked return ownership through the canonical loop combinators. -/
module
public import Grammatik.Kern.Syntax.Satz.T2.ReturnInventory
@[expose] public section

namespace Gabbro.Grammatik.ReturnInventory
variable {D : Deklaration} {V : Vertrag D} {L : D.Lock} {bo : Option Int} {Λ : List (Res D)}
variable {slack : Nat}

theorem traverse (step : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (step σ ρ))
    (hi : ∀ σ ρ, (inv σ ρ).1.haelt = σ.haelt) :
    ∀ ks σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (traverseLauf (l := l) step inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
    intro σ ρ entry
    simp only [traverseLauf]
    split
    · exact Outcome.ok _ (hi σ ρ)
    · exact Outcome.logik _
  | cons k ks ih =>
    intro σ ρ entry
    simp only [traverseLauf]
    split
    · exact Outcome.logik _
    · have result := hs (inv σ ρ).1 (.cons k ρ) (entry.same (hi σ ρ))
      generalize he : step (inv σ ρ).1 (.cons k ρ) = outcome at result ⊢
      cases outcome with
      | ok σ1 ρ1 | next _ σ1 ρ1 =>
        have same := (result σ1 rfl).trans (hi σ ρ)
        exact (ih σ1 ρ1.tail (entry.same same)).vor same
      | leave _ σ1 ρ1 =>
        have same := (result σ1 rfl).trans (hi σ ρ)
        dsimp only
        split
        · exact Outcome.ok _ ((hi σ1 ρ1.tail).trans same)
        · exact Outcome.logik _
      | zurueck σ1 value | why σ1 value =>
        intro σ' equal
        cases equal
        exact result σ1 rfl
      | logik e => exact Outcome.logik e
      | hardware e => exact Outcome.hardware e

theorem retry (step : World D → Env D Γ → Ausgang V true Γ)
    (test : World D → Env D Γ → World D × Bool)
    (overflow : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (step σ ρ))
    (hi : ∀ σ ρ, (test σ ρ).1.haelt = σ.haelt)
    (ho : ∀ σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (overflow σ ρ)) :
    ∀ n σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (retryLauf step test overflow n σ ρ) := by
  intro n
  induction n with
  | zero =>
    intro σ ρ entry
    simp only [retryLauf]
    split
    · exact Outcome.ok _ (hi σ ρ)
    · exact (ho _ _ (entry.same (hi σ ρ))).vor (hi σ ρ)
  | succ n ih =>
    intro σ ρ entry
    simp only [retryLauf]
    split
    · exact Outcome.ok _ (hi σ ρ)
    · have result := hs (test σ ρ).1 ρ (entry.same (hi σ ρ))
      generalize he : step (test σ ρ).1 ρ = outcome at result ⊢
      cases outcome with
      | ok σ1 ρ1 | next _ σ1 ρ1 =>
        have same := (result σ1 rfl).trans (hi σ ρ)
        exact (ih σ1 ρ1 (entry.same same)).vor same
      | leave _ σ1 ρ1 =>
        exact Outcome.ok _ ((result σ1 rfl).trans (hi σ ρ))
      | zurueck σ1 value | why σ1 value =>
        intro σ' equal
        cases equal
        exact result σ1 rfl
      | logik e => exact Outcome.logik e
      | hardware e => exact Outcome.hardware e

theorem forever (a : D.Annahme) (step : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (step σ ρ))
    (hi : ∀ σ ρ, (inv σ ρ).1.haelt = σ.haelt) :
    ∀ n σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (foreverLauf (l := l) a step inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _; exact Outcome.hardware _
  | succ n ih =>
    intro σ ρ entry
    simp only [foreverLauf]
    split
    · exact Outcome.logik _
    · have result := hs (inv σ ρ).1 ρ (entry.same (hi σ ρ))
      generalize he : step (inv σ ρ).1 ρ = outcome at result ⊢
      cases outcome with
      | ok σ1 ρ1 | next _ σ1 ρ1 =>
        have same := (result σ1 rfl).trans (hi σ ρ)
        exact (ih σ1 ρ1 (entry.same same)).vor same
      | leave _ σ1 ρ1 =>
        exact Outcome.ok _ ((result σ1 rfl).trans (hi σ ρ))
      | zurueck σ1 value | why σ1 value =>
        intro σ' equal
        cases equal
        exact result σ1 rfl
      | logik e => exact Outcome.logik e
      | hardware e => exact Outcome.hardware e

theorem consume (t : D.Tab)
    (step : World D → Env D (.index (D.count t) :: Γ) → Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ → World D × Option (Wert D (.index (D.count t))) × Bool)
    (mass : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, Entry (slack := slack) L bo Λ σ → Outcome (slack := slack) L σ (step σ ρ))
    (hi : ∀ σ ρ, (inv σ ρ).1.haelt = σ.haelt)
    (hc : ∀ σ ρ, (sel σ ρ).1.haelt = σ.haelt)
    (hm : ∀ σ ρ, (mass σ ρ).1.haelt = σ.haelt) :
    ∀ n σ ρ, Entry (slack := slack) L bo Λ σ →
      Outcome (slack := slack) L σ (verbrauchLauf (l := l) t step inv sel mass bound n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _; exact Outcome.logik _
  | succ n ih =>
    intro σ ρ entry
    simp only [verbrauchLauf]
    split
    · exact Outcome.logik _
    · have selected := (hc (inv σ ρ).1 ρ).trans (hi σ ρ)
      generalize he : sel (inv σ ρ).1 ρ = choice at selected ⊢
      rcases choice with ⟨σr, option, flag⟩
      cases option with
      | none =>
        cases flag
        · exact Outcome.ok _ selected
        · exact Outcome.logik _
      | some k =>
        dsimp only
        have measured := (hm σr ρ).trans selected
        generalize hm0 : mass σr ρ = measurement at measured ⊢
        rcases measurement with ⟨σm, m⟩
        dsimp only
        have result := hs σm (.cons k ρ) (entry.same measured)
        generalize hs0 : step σm (.cons k ρ) = outcome at result ⊢
        cases outcome with
        | ok σ1 ρ1 | next _ σ1 ρ1 =>
          dsimp only
          have same := (hm σ1 ρ1.tail).trans ((result σ1 rfl).trans measured)
          generalize hm1 : mass σ1 ρ1.tail = nextMass at same ⊢
          rcases nextMass with ⟨σm', m'⟩
          dsimp only
          split
          · exact (ih σm' ρ1.tail (entry.same same)).vor same
          · exact Outcome.logik _
        | leave _ σ1 ρ1 =>
          dsimp only
          have same := (hm σ1 ρ1.tail).trans ((result σ1 rfl).trans measured)
          generalize hm1 : mass σ1 ρ1.tail = nextMass at same ⊢
          rcases nextMass with ⟨σm', m'⟩
          dsimp only
          split
          · split
            · exact Outcome.ok _ ((hi σm' ρ1.tail).trans same)
            · exact Outcome.logik _
          · exact Outcome.logik _
        | zurueck σ1 value | why σ1 value =>
          intro σ' equal
          cases equal
          exact result σ1 rfl
        | logik e => exact Outcome.logik e
        | hardware e => exact Outcome.hardware e

end Gabbro.Grammatik.ReturnInventory
