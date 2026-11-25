/-
  File:      Core/Ziel/Review/Slice/Goal.lean
  Subject:   THE SLICE GOAL FOR F_klein (Durchstich step 3): the goal legs over the concrete
             instance R₀ for every accepted slice unit, with each gap named exactly.

  `DurchstichKleinAussage P` is the pinned slice goal. Its legs, and what they rest on:
  * refinement (one ideal run per implementation run): PROVED, `verfeinerung_akzeptiert`;
  * today's guarantee on every cut: PROVED, `zielFX_akzeptiert`;
  * the four safety legs: CONDITIONAL on `(fragment .unit t).Rein` — the proof
    (`sicherheitAkzeptiert`) goes through `fragment_rein`, i.e. it covers only
    frame-only fragments. A slice unit that uses `lade`/`speichere` (M1) is outside
    that proof; its safety needs the access duties (`ZugriffBestimmtAussage` and
    `ZugriffKomponierbarAussage`, proved individually as `zugriffBestimmt` and
    `zugriffKomponierbar`, but not yet assembled under `ZugriffBefehlAussage` nor wired
    into the fragment leg proofs). GAP S.
  * noninterference: CONDITIONAL on `Rein` for the same reason (`niAkzeptiert` goes
    through `fragment_nichtinterferent`, which needs `Rein`; the reading classes are
    excluded from the step-level flow rule, MK-13). GAP N.
  * bounds: HYPOTHESIS `SchrankenAkzeptiertAussage P` — the leg is open (M9). GAP B.
  * progress (no hang + class progress): HYPOTHESIS `FortschrittAkzeptiertAussage` —
    the     scheduler premise `SchedulerFortschrittVoraussetzung` is open, and the
    composability leg needs `Rein` (else `ZugriffKomponierbarAussage` — now proved as
    `zugriffKomponierbar`, but not yet wired into `einheit_fortschrittsfelder`). GAP F.
  * the wait-free section row: PROVED from acceptance (`Akzeptiert` contains
    `AbschnittWartefrei`); vacuous in content while no lock instruction exists (M2).
  * the class duties and the memory/atomic kernel statements: PROVED,
    `klassenAussagen` (all classes incl. `lesen`/`schreiben`) and `atomAussagen`.
  * `klein_akzeptiert_bei_R₀` ties acceptance to the concrete frame: it is
    definitionally `Annahme.Akzeptiert`, i.e. the `Akzeptiert` field of `R₀ P B`.

  `klein_luecke_nicht_privat` is the sharp edge of gaps S/N/F: the slice contains a
  non-frame instruction (`zugriff (.lade …)`), so the machine-level slice is strictly
  larger than what the `Rein`-only leg proofs cover.
-/
module

public import Core.Ziel.Review.Slice.Fragment
public import Core.Ziel.Korrektheit.Pruefer
public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ziel.Korrektheit.Instanz
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert
public import Core.Ziel.Korrektheit.Beweise.SicherheitAkzeptiert
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Gesamt
public import Core.Ast.Semantik.Runtime.Atom.Aussagen
public import Core.Annahme.Annahme
public import Core.Annahme.Lokal

@[expose] public section

namespace Gabbro.Core.Ziel.Review.Slice

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Ziel.Korrektheit
open Gabbro.Core.Beobachtung

/-- The pinned slice goal: every accepted F_klein unit refines an ideal run with
    today's guarantee on every cut, meets the wait-free section row, and satisfies
    the class and kernel duties; safety and noninterference hold conditionally on
    the fragment being frame-only, bounds and progress under their open legs. -/
def DurchstichKleinAussage (P : Katalog.Plattform) : Prop :=
  ∀ t : Ast.Unit, F_klein t → Annahme.Akzeptiert (einheitVon P t) →
    (∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ η)
    ∧ (∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      ∀ k : Maschine.Schnitt (einheitVon P t) ρ, Maschine.ZielFX (einheitVon P t) H ρ k)
    ∧ ((fragment Ast.Category.unit t).Rein →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Gabbro.Core.Sicherheit.Speichersicher (sicherheitVon (einheitVon P t)) H ρ ∧
        Gabbro.Core.Sicherheit.InvariantenErhalten (sicherheitVon (einheitVon P t)) H ρ ∧
        Gabbro.Core.Sicherheit.Rennfrei (sicherheitVon (einheitVon P t)) H ρ ∧
        Gabbro.Core.Sicherheit.ToctouFrei (sicherheitVon (einheitVon P t)) H ρ)
    ∧ ((fragment Ast.Category.unit t).Rein →
      Beobachtung.Nichtinterferent (einheitVon P t))
    ∧ (SchrankenAkzeptiertAussage P →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ → Beobachtung.ImSchranken (einheitVon P t) ρ)
    ∧ (FortschrittAkzeptiertAussage →
      ∀ (H : Katalog.Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Maschine.Laeufe (einheitVon P t) H ρ →
      Katalog.FairLaeufe (einheitVon P t).katalog H ρ.hw →
      ∃ η : Maschine.I.Lauf (einheitVon P t),
        Maschine.I.Laeufe (einheitVon P t) η ∧ Maschine.I.Sim (einheitVon P t) ρ η ∧
        (∀ c, ¬ Maschine.I.Haengt (einheitVon P t) ρ η c) ∧
        Maschine.I.FortschrittDerKlasse
          (Maschine.I.FortschrittsKlasse.blockierend : Maschine.I.FortschrittsKlasse Befehl) η)
    ∧ Annahme.AbschnittWartefrei (einheitVon P t)
    ∧ KlassenAussagen ∧ AtomAussagen

/-- The slice goal holds: the unconditional legs are the existing theorems, the
    conditional legs discharge through them, the open legs stay hypotheses. -/
theorem ziel_klein (P : Katalog.Plattform) : DurchstichKleinAussage P := by
  intro t _ hacc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H ρ lauf
    exact verfeinerung_akzeptiert P t hacc H ρ lauf
  · intro H ρ lauf k
    exact zielFX_akzeptiert P t hacc H ρ lauf k
  · intro _ H ρ lauf
    exact sicherheitAkzeptiert P t hacc H ρ lauf
  · intro _
    exact niAkzeptiert P t hacc
  · intro schranken H ρ lauf
    exact schranken t hacc H ρ lauf
  · intro fortschritt H ρ lauf fair
    exact fortschritt P t hacc H ρ lauf fair
  · exact hacc.1.2.2.2.2.2.1
  · exact klassenAussagen
  · exact atomAussagen

/-- Acceptance over the slice is acceptance in the concrete frame R₀: the
    `Akzeptiert` field of `R₀ P B` is definitionally `Annahme.Akzeptiert`. -/
theorem klein_akzeptiert_bei_R₀ (P : Katalog.Plattform) (B : FormBeleg)
    (E : Ast.Semantik.Einheit) : (R₀ P B).Akzeptiert E ↔ Annahme.Akzeptiert E :=
  Iff.rfl

/-- The sharp edge of gaps S/N/F: the slice contains a non-frame instruction, so the
    machine-level slice exceeds what the `Rein`-only leg proofs cover. -/
theorem klein_luecke_nicht_privat :
    ∃ b : Befehl, KleinBefehl b ∧ ¬ b.Privat := by
  refine ⟨.zugriff (.lade 0 0 0 (Ast.Ty.int 0 0) Speicher.Modus.na), by simp only [KleinBefehl], ?_⟩
  simp only [Befehl.Privat, Befehl.klasse, Zugriffsform.klasse, reduceCtorEq, or_false,
    not_false_eq_true]

end Gabbro.Core.Ziel.Review.Slice
