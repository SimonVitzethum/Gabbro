/-
  File:      core/Core/Ast/Semantik/Runtime/ZugriffSicher/RennenLauf.lean
  Subject:   THE RUN-LEVEL RACE INVARIANT OF A SOURCE UNIT (the missing second leg of
              `ZugriffSicherAussage`). A run of a source unit appends memory events only at the entry
              context: its `eintritte` names no handler, so every other context's boot frame carries no
              arrival regions, and an access without a region is refused before it records an event.
              Therefore all executed accesses of every prefix have the one actor `.kontext eintritt`,
              and program order orders every conflicting pair (`rennenAusEinemKontext`). No statement
              is changed.
-/
module

public import Core.Ast.Semantik.Runtime.ZugriffSicher.RennenBein
public import Core.Ast.Semantik.Runtime.ZugriffSicher.Grenzen
public import Core.Ast.Semantik.Runtime.Mehrkontext.Start
public import Core.Sicherheit.KatalogSchritt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Sicherheit
open Gabbro.Core.Sicherheit (Konflikt AusgefuehrterZugriff RennenImGraph)
open Gabbro.Core.Speicher (Zustand)

/-- A context without arrival regions holds no handle, so it is authorised for no cell. -/
theorem keineBefugnisOhneAnkunft {s : Zustand} {c : Kontext}
    (leer : (s.lokal c).arrivalRegions = []) :
    ∀ (z : Zelle) (recht : Speicherrecht), ¬ s.befugt c z recht := by
  intro z recht bef
  obtain ⟨g, off, griff, _, _, _, _, _⟩ := bef
  have gn : s.griff c z = none := by
    cases z with
    | region slot offset =>
      simp only [Zustand.griff, leer, List.length_nil, Nat.not_lt_zero, if_false]
    | sperre lock => rfl
    | aussen => rfl
  rw [gn] at griff
  cases griff

/-- The authority of every access form but the fence is the cell authority of its operand. -/
theorem zugriffBefugtBrauchtAnkunft (z : Zugriffsform)
    (hz : ∀ m, z ≠ .zaun m) {s : Zustand} {c : Kontext}
    (leer : (s.lokal c).arrivalRegions = []) :
    ¬ (Befehl.zugriff z).form.klasse.befugt ((Befehl.zugriff z).form.operand (s.lokal c)) s c := by
  cases z with
  | zaun m => exact False.elim (hz m rfl)
  | lade ziel region index typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.lade ziel region index typ mode) (s.lokal c)).ort) .lesen)
  | erwarte ziel region index erwartet typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.erwarte ziel region index erwartet typ mode) (s.lokal c)).ort) .lesen)
  | speichere region index quelle mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.speichere region index quelle mode) (s.lokal c)).ort) .schreiben)
  | veroeffentliche region index quelle mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.veroeffentliche region index quelle mode) (s.lokal c)).ort) .schreiben)
  | tausche ziel region index quelle typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.tausche ziel region index quelle typ mode) (s.lokal c)).ort) .lesen)
  | vergleicheTausche ziel region index erwartet neu typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.vergleicheTausche ziel region index erwartet neu typ mode) (s.lokal c)).ort) .lesen)
  | holeUndAddiere ziel region index betrag typ mode =>
    simpa [Befehl.form, Befehl.klasse, Befehl.operand, Zugriffsform.operand, Zugriffsform.klasse,
      Wirkungsklasse.befugt] using
      (keineBefugnisOhneAnkunft (s := s) (c := c) leer
        ((Zugriffsform.operand (Zugriffsform.holeUndAddiere ziel region index betrag typ mode) (s.lokal c)).ort) .lesen)

/-- A step of a class-good instruction at a context with no arrival regions plans the
    private step: a frame-only form is private by its class; a fence plans nothing; every other
    access form is refused because it holds no handle. -/
theorem quellSchrittPlanPrivat (p : Fragment) (f : Befehl) (hgut : f.Klassengut)
    {c : Kontext} {s : Zustand} (leer : (s.lokal c).arrivalRegions = [])
    {w : PUnit} {plan : Plan} {u : Zustand}
    (impl : ((system p.code).regel f).impl c s w [plan] u) :
    plan = Semantik.plan := by
  change f.impl c s w [plan] u at impl
  rcases hgut with hpriv | ⟨z, rfl⟩
  · exact ((Befehl.impl_privat f hpriv c s w [plan] u).1 impl).1
  · have step := (Zugriffsform.ideal_iff z c s w [plan] u).1 impl
    rcases step with ⟨_, eq, _⟩ | ⟨bef, v, _, eq, _⟩
    · exact (List.cons.inj eq).1
    · by_cases hz : ∃ m, z = .zaun m
      · rcases hz with ⟨m, rfl⟩
        have hp : plan = (Befehl.zugriff (Zugriffsform.zaun m)).form.plan (s.lokal c) v :=
          (List.cons.inj eq).1
        simpa [Befehl.form, Befehl.klasse, Zugriffsform.klasse, Schrittform.plan, Wirkungsklasse.plan] using hp
      · have hf : ∀ m, z ≠ .zaun m := by
          intro m hzaun
          exact hz ⟨m, hzaun⟩
        exact False.elim ((zugriffBefugtBrauchtAnkunft z hf leer) bef)

end Gabbro.Core.Ast.Semantik
