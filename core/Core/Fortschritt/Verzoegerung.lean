/-
  File:      Core/Fortschritt/Verzoegerung.lean
  Subject:   THE HARDWARE-DELAY RULE (PERFECT-MODEL §3.7, step M8): a delay caused by withheld
             hardware opportunities is the same delay in `I` — no hang is blamed on the program.

  A context step on either side needs a physical opportunity (`KannSchreiten`), so a withheld
  opportunity means neither side takes one of its steps (`verzoegerung_gilt_beidseitig`). A
  permanently withheld core is unfair (`dauernde_verzoegerung_unfair`); on a fair history the
  hardware-caused delay is finite. Fairness itself (`FairLaeufe`) speaks only about cores,
  deliveries and cycles — hardware alone, never about a scheduler.
-/
module

public import Core.Fortschritt.Klasse

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- An implementation step of a context needs its physical opportunity. -/
theorem impl_schritt_braucht_gelegenheit {ρ : Maschine.Lauf E} {t c w spur}
    (hstep : ρ.zeit.spur t = some (.kontext c w, spur)) :
    ∃ s, ρ.zeit.zustand t = some s ∧ KannSchreiten ρ.hw t c s := by
  cases hz : ρ.zeit.zustand t with
  | none =>
    cases htakt : ρ.zeit.takt t with
    | schritt label step =>
      rw [hz] at step
      cases step
    | wartet label _ _ =>
      cases label.symm.trans hstep
  | some s =>
    cases hp : ρ.zeit.zustand (t + 1) with
    | none =>
      cases htakt : ρ.zeit.takt t with
      | schritt label step =>
        rw [hz, hp] at step
        cases step
      | wartet label _ _ =>
        cases label.symm.trans hstep
    | some s' =>
      cases htakt : ρ.zeit.takt t with
      | schritt label step =>
        rw [hz, hp] at step
        cases step with
        | schritt h =>
          cases h with
          | kontext _ bereit _ _ =>
            have label' := label
            rw [hstep] at label'
            cases label'
            exact ⟨s, hz, bereit⟩
          | antwort _ _ =>
            have hcontra := Option.some.inj (label.symm.trans hstep)
            cases congrArg Prod.fst hcontra
          | interrupt _ _ =>
            have hcontra := Option.some.inj (label.symm.trans hstep)
            cases congrArg Prod.fst hcontra
          | absturz _ =>
            have hcontra := Option.some.inj (label.symm.trans hstep)
            cases congrArg Prod.fst hcontra
      | wartet label _ _ =>
        cases label.symm.trans hstep

/-- An ideal step of a context needs its physical opportunity. -/
theorem ideal_schritt_braucht_gelegenheit {η : I.Lauf E} {t c w spur}
    (hstep : η.zeit.spur t = some (.kontext c w, spur)) :
    KannSchreiten η.hw t c (η.zeit.zustand t) := by
  cases htakt : η.zeit.takt t with
  | schritt label step =>
    cases step with
    | kontext _ bereit _ _ =>
      have label' := label
      rw [hstep] at label'
      cases label'
      exact bereit
    | antwort _ _ =>
      have hcontra := Option.some.inj (label.symm.trans hstep)
      cases congrArg Prod.fst hcontra
    | interrupt _ _ =>
      have hcontra := Option.some.inj (label.symm.trans hstep)
      cases congrArg Prod.fst hcontra
    | absturz _ =>
      have hcontra := Option.some.inj (label.symm.trans hstep)
      cases congrArg Prod.fst hcontra
  | wartet label _ _ =>
    cases label.symm.trans hstep

/-- A withheld opportunity delays both sides equally: neither the implementation nor the ideal
    run takes one of the context's steps there. -/
theorem verzoegerung_gilt_beidseitig {ρ : Maschine.Lauf E} {η : I.Lauf E}
    {t c} {s : Zustand L Ort Wert Raum Lok Grund}
    (hρ : ρ.zeit.zustand t = some s) (hη : η.zeit.zustand t = s)
    (hsame : η.hw = ρ.hw)
    (hno : ¬ KannSchreiten ρ.hw t c s) :
    (∀ w spur, ρ.zeit.spur t ≠ some (.kontext c w, spur)) ∧
      ∀ w spur, η.zeit.spur t ≠ some (.kontext c w, spur) := by
  constructor
  · intro w spur hstep
    obtain ⟨s', hs', hge⟩ := impl_schritt_braucht_gelegenheit hstep
    have heq : s' = s := Option.some.inj (hs'.symm.trans hρ)
    rw [heq] at hge
    exact hno hge
  · intro w spur hstep
    have hge := ideal_schritt_braucht_gelegenheit hstep
    rw [hη, hsame] at hge
    exact hno hge

/-- A core withheld forever from a dispatched context is unfair: on a fair history every
    core gets its opportunities back. A hardware-caused delay is finite. -/
theorem dauernde_verzoegerung_unfair {η : I.Lauf E}
    {k : Kern} {c : Kontext} {a : Nat}
    (hk : k < η.umgebung.kernzahl)
    (hdisp : ∀ t, a ≤ t → ((η.zeit.zustand t).kerne k).laeuft = some c)
    (hno : ∀ t, a ≤ t → ¬ η.hw.gelegenheit t k) :
    ¬ FairLaeufe E.katalog η.umgebung η.hw := by
  intro fair
  obtain ⟨i, hge, hoffer⟩ := fair.kerne.2 k hk a
  exact hno i hge hoffer

end Gabbro.Core.Fortschritt
