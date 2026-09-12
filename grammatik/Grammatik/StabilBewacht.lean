/-
  File:      Grammatik/StabilBewacht.lean
  Subject:   STABILITY WITHOUT INVARIANT FORM (lane 105, D9).

  The goal theorem needs, for assertions over shared carriers that are NOT
  in invariant form, the full `InterferenceFree` shape (`hFree`). This file
  replaces it by the standard rely/guarantee argument at chain grain:

  * `stabil_ohne_form` -- the induction: head validity plus own-step
    preservation plus foreign-step preservation (`hStabil`, one direction
    only) give the assertion at every chain world. No invariant form, no
    `HaengtAb`, no discipline -- pure chain folding (`kette_erhaelt` grain).
  * `stabil_aus_bewachung` -- the corollary that connects `hStabil` to the
    checker: `hStabil` follows from a static GUARANTEE (every foreign write
    to a carrier `Q f` reads happens only while holding a guard lock that
    `f` holds throughout -- `Bewacht` / `TraegerSchreibt` / `D.haelt`) plus
    a per-step RELY (guarded foreign writes leave `Q f`'s slots alone).
    The rely is memory-level (slot agreement, checker-comparable per run),
    so no assertion-level per-step proof is owed any more.
  * `haengtAb_aus_slotDep` -- the checker-shape link: slot-level dependence
    plus footprint coverage give table-level `HaengtAb`, the shape the
    `InterferenceFree` machinery consumes downstream.

  Witnesses (`_zeuge`) run on the reference fixture (`ReferenzB.lean`):
  a two-thread chain where `Q` (`slot 0 = slot 1`, "my slot equals my local
  counter") is not a whole-table invariant and the other thread writes only
  slot 5, a different slot of the same shared table.
-/
import Grammatik.InterferenzAllgemein
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Stability without invariant form.** What holds at the chain head and
    survives every own step and every foreign step holds at every chain
    world -- by induction on the chain index (`hKette` counts one step per
    transition, so every successor position yields its writer and its
    predecessor). One direction only: stability never needs the backward
    leg. -/
theorem stabil_ohne_form (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hKopf : ∀ f ∈ J.faeden, ∀ σ₀, J.welten[0]? = some σ₀ → Q f σ₀)
    (hEigen : ∀ f ∈ J.faeden, ∀ (k : Nat) (vor nach : World D),
        J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        Q f vor → Q f nach)
    (hStabil : ∀ f ∈ J.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World D), g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        Q f vor → Q f nach) :
    ∀ f ∈ J.faeden, ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q f σ := by
  intro f hf k
  induction k with
  | zero => exact hKopf f hf
  | succ k ih =>
    intro σ hσ
    have hK := J.hKette
    have hlen : k + 1 < J.welten.length := lt_of_belegt J.welten (k + 1) σ hσ
    have hsk : k < J.schrittFaden.length := by omega
    have hwk : k < J.welten.length := by omega
    obtain ⟨g, hg⟩ := kette_welt_belegt J.schrittFaden k hsk
    obtain ⟨vor, hvor⟩ := kette_welt_belegt J.welten k hwk
    have hgm : g ∈ J.faeden := (J.hSchritt k g vor σ hg hvor hσ).1
    by_cases heq : g = f
    · have hg' : J.schrittFaden[k]? = some f := heq ▸ hg
      exact hEigen f hf k vor σ hg' hvor hσ (ih vor hvor)
    · exact hStabil f hf k g vor σ hgm heq hg hvor hσ (ih vor hvor)

#print axioms Gabbro.Grammatik.stabil_ohne_form

end Gabbro.Grammatik
