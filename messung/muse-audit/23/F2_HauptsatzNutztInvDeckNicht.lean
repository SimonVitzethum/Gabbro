/-
  Audit probe F2: in `allgemeinStabil`, `hInv` and `hDeck` are unused premises.

  Claim (pattern b): the main theorem takes
    (hInv : InvariantenKontext Nb J I) and (hDeck : GeteiltGedeckt Nb J)
  but its proof never mentions them (the docstring itself says they are
  "carried, not consumed"). Demonstrated below by proving the exact same
  conclusion from the remaining premises only -- with `hInv`/`hDeck`
  generalized away (i.e. the proof works for ALL values of them, hence uses
  none of their content).

  Consequence: nothing in the conclusion depends on lock discipline, the
  invariant context, or shared-carrier coverage.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `allgemeinStabil` with `hInv`/`hDeck` erased: same statement, same proof
    shape (`kette_erhaelt` + `stabil`), no invariant context, no deck. -/
theorem audit_allgemeinStabil_ohne_InvDeck
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → Q f σ₀)
    (hFremd : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨ (Q f vor ↔ Q f nach))
    (hEigen : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach)) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  intro σ hletzte f hf
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach) := by
    intro k g vor nach hkg hkv hkn
    by_cases heq : g = f
    · subst heq
      exact hEigen g hf k vor nach hkg hkv hkn
    · obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
      cases hFremd f hf k g vor nach hgm heq hkg hkv hkn with
      | inl hd => exact stabil (hAb f hf) hR hd
      | inr hiff => exact hiff
  have hall := kette_erhaelt J.welten J.schrittFaden J.hKette (Q f) (hInit f hf) hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-- The original follows from the audit version by forgetting `I`, `hInv`,
    `hDeck`: the two premises add no content to this conclusion. -/
theorem audit_allgemeinStabil_forget
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → Q f σ₀)
    (hFremd : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨ (Q f vor ↔ Q f nach))
    (hEigen : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach)) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ :=
  audit_allgemeinStabil_ohne_InvDeck Nb J Q hAb hInit hFremd hEigen

/-
CUTS:
- This probe does not claim `hFremd`/`hEigen` are dischargeable; it claims only
  that `hInv`/`hDeck` contribute nothing to the `allgemeinStabil` conclusion.
- Same erasure holds for `allgemeinStabil_invariant` and
  `allgemeinStabil_invariant_mitAusnahmen` (their `hDeck` is likewise only
  forwarded); not re-proved here to keep the probe minimal.
-/
#print axioms Gabbro.Grammatik.audit_allgemeinStabil_ohne_InvDeck
#print axioms Gabbro.Grammatik.audit_allgemeinStabil_forget
