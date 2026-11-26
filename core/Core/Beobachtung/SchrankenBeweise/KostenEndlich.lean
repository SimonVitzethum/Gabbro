/-
  File:      core/Core/Beobachtung/SchrankenBeweise/KostenEndlich.lean
  Subject:   THE FINITE-BOUND CORE STATEMENTS (M9, MK-12). The estimator of
              `KostenSchaetzer` bounds one invocation: from the entry of a
              function to its exit (`AufrufFenster`: depth `d + 1` with the
              function name at the entry cut, depth `d` at the exit cut, never
              below `d + 1` inside), counted in the acting context's own ticks.
              Two statements carry the finite bound, both pinned for Hy4 under
              one collective root:

              * `KostenSchaetzerKorrektAussage`: every invocation window of an
                accepted unit costs at most the estimator, and so does every
                prefix of the entry context. Proof sketch: induction over the
                window from the entry cut. Each executed source form costs
                exactly its elaborated instructions (one tick each through
                `klassenKosten`); straight-line code is counted once;
                `whileBounded`/`forRange` bodies run at most their static trip
                bound — the counters (`setzePasszahl`, `forAnfang` with the
                `zaehler`/`obergrenzen` of `Rahmen`) enforce it, and the
                `decreases` clause (`KlauselnWahr` over `I`, carried by
                acceptance) makes every recursive re-entry strictly decrease
                the entry measure inside its static interval, so the span
                bounds the cycle activations; calls cost their verified table
                entry or their structural estimate. Protocol ticks are foreign
                to every context (`kontextkosten_fremd` shape, as in
                `SchrankenB8`), so they add nothing to the window. The entry
                prefix adds the top-level declarations, the entry call and the
                final instruction around one `main` window.

              * `GebundenKHEndlichAussage`: the cost and hold duties of every
                accepted unit with a finite bound, stated window-relative: every
                cut of every invocation window and every prefix of the entry
                context meets the declared ceilings. Proof sketch: case split on
                the declaration. Open leg: the checker line is the slack line,
                so `gebundenKH` closes the whole-run duties and every window
                follows. Finite leg: the hold list is empty, so the hold legs
                are vacuous as in `bindungKHOffen`; the cost legs follow from
                the correctness statement with the checker's `E ≤ K` (extract
                `schaetzeEinheit = some E` and `E ≤ K` from
                `pruefeSchrankenEndlich = true` at `some K`).

              The window and the window-relative prefixes are inlined: no
              auxiliary statement name is introduced for them. The
              satisfiability witnesses below are run-free (checker outcomes and
              estimator values on tiny trees); the run-side joint premises are
              the prover's first step.
-/
module

public import Core.Beobachtung.SchrankenBeweise.KostenSchaetzer
public import Core.Beobachtung.Schranken

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- **Correctness of the structural estimator** (`KostenSchaetzerKorrektAussage`):
    for every accepted unit whose estimator is defined, each invocation window
    costs at most the estimator in the acting context's own ticks, and so does
    every prefix of the entry context. Open for Hy4; the sketch is in the file
    header. Difficulty: schwer. -/
def KostenSchaetzerKorrektAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
    EndlichAkzeptiertAussage P u tab z →
    schaetzeEinheit z tab u.baum = some E →
    (∀ (ρ : Lauf (einheitMitSchranken P u)) (c : Kontext) (f : Identifier)
      (a b : Nat),
      (∃ d ta tb, ρ.zeit.zustand a = some ta ∧ ρ.zeit.zustand b = some tb ∧
        (ta.lokal c).funktion = some f ∧
        (ta.lokal c).fortsetzungen.length = d + 1 ∧
        (tb.lokal c).fortsetzungen.length = d ∧ a < b ∧
        ∀ t s, a < t → t < b → ρ.zeit.zustand t = some s →
          d + 1 ≤ (s.lokal c).fortsetzungen.length) →
      Kontextkosten ρ c a (b - a) ≤ E) ∧
    ∀ (ρ : Lauf (einheitMitSchranken P u)) (t : Nat),
      Kontextkosten ρ eintritt 0 t ≤ E

/-- **The cost and hold duties of every accepted bound unit with a finite
    bound** (`GebundenKHEndlichAussage`): window-relative, over every cut of
    every invocation window and every prefix of the entry context. Open for
    Hy4; the sketch is in the file header (case split on the declaration,
    correctness statement plus the checker's `E ≤ K`, vacuous hold legs).
    Difficulty: mittel. -/
def GebundenKHEndlichAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
    (z : Wirkungsklasse → KlassenKostenzeile),
    EndlichAkzeptiertAussage P u tab z →
    (∀ (ρ : Lauf (einheitMitSchranken P u)) (c : Kontext) (f : Identifier)
      (a b : Nat),
      (∃ d ta tb, ρ.zeit.zustand a = some ta ∧ ρ.zeit.zustand b = some tb ∧
        (ta.lokal c).funktion = some f ∧
        (ta.lokal c).fortsetzungen.length = d + 1 ∧
        (tb.lokal c).fortsetzungen.length = d ∧ a < b ∧
        ∀ t s, a < t → t < b → ρ.zeit.zustand t = some s →
          d + 1 ≤ (s.lokal c).fortsetzungen.length) →
      ∀ t, a ≤ t → t ≤ b →
        UnterGrenze (einheitMitSchranken P u).schranken.kosten
          (Kontextkosten ρ c a (t - a)) ∧
        ∀ (l : Nat) (a' n : Nat), a ≤ a' → a' + n ≤ t →
          (∀ t', a' ≤ t' → t' < a' + n →
            ∃ s, ρ.zeit.zustand t' = some s ∧
              (s.sperren l).besitzer = some c) →
          UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
            (Kontextkosten ρ c a' n)) ∧
    ∀ (ρ : Lauf (einheitMitSchranken P u)) (t : Nat),
      UnterGrenze (einheitMitSchranken P u).schranken.kosten
        (Kontextkosten ρ eintritt 0 t) ∧
      ∀ (l : Nat) (a' n : Nat), a' + n ≤ t →
        (∀ t', a' ≤ t' → t' < a' + n →
          ∃ s, ρ.zeit.zustand t' = some s ∧
            (s.sperren l).besitzer = some eintritt) →
        UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
          (Kontextkosten ρ eintritt a' n)

/-- The collective root of the finite-bound core: estimator correctness and the
    finite KH duties close together. -/
def KostenEndlichWurzelAussage : Prop :=
  KostenSchaetzerKorrektAussage ∧ GebundenKHEndlichAussage

/-- Joint satisfiability for the estimator correctness: the open declaration
    passes the endliche line and the estimator is defined on a unit with a
    `main`. No run is constructed. -/
theorem kostenSchaetzer_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile) (E : Nat),
      pruefeSchrankenEndlich u tab z = true ∧
        schaetzeEinheit z tab u.baum = some E := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, _, rfl, rfl⟩

/-- Sharpness for the estimator correctness: some unit has no estimator value,
    and some declaration is refused by the endliche line. The bound is claimed
    only where it is defined. -/
theorem kostenSchaetzer_nichtTrivial :
    (∃ (u : Ast.Unit) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      schaetzeEinheit z tab u = none) ∧
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false := by
  refine ⟨⟨endlosBaum, [], Wirkungsklasse.kostenZeile, rfl⟩,
    ⟨Katalog.Plattform.x86_64, ⟨engerBaum, engeDeklaration⟩, [],
      Wirkungsklasse.kostenZeile, rfl⟩⟩

/-- Joint satisfiability for the finite KH duties: the open declaration passes
    the endliche line. -/
theorem gebundenKHEndlich_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = true := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, Schrankendeklaration.leer⟩, [],
    Wirkungsklasse.kostenZeile, rfl⟩

/-- Sharpness for the finite KH duties: the endliche line refuses a too-tight
    finite ceiling. -/
theorem gebundenKHEndlich_nichtTrivial :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken) (tab : KostenTabelle)
      (z : Wirkungsklasse → KlassenKostenzeile),
      pruefeSchrankenEndlich u tab z = false := by
  refine ⟨Katalog.Plattform.x86_64, ⟨engerBaum, engeDeklaration⟩, [],
    Wirkungsklasse.kostenZeile, rfl⟩

end Gabbro.Core.Beobachtung
