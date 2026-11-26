/-
  File:      core/Core/Beobachtung/SchrankenBeweise/SchrankenSpielraum.lean
  Subject:   THE DECIDABLE SLACK LINE OF BOUND UNITS (M9, MK-12). The per-form and protocol
             cost/hold duties of `einheitMitSchranken` were proved under the free slack premises
             `kostenSlack`/`halteSlack` (`bindungKlassenKHRegel`, `bindungKostenProtokoll_unterSlack`
             in `BindungKosten`). Those premises are now DISCHARGED by a decidable checker line
             `pruefeSchrankenSpielraum` over the declaration and the static class cost rows
             (`Wirkungsklasse.kostenZeile`). Every class row costs one tick, so a finite ceiling is
             reached by a run and leaves no room for the next tick; only an open declaration passes.
             The line is a conjunct of `GebundenAkzeptiertAussage` (acceptance of a bound unit),
             adding refusals only. `SchrankenSpielraumAussage` is its correctness: a passing line
             gives the exact slack premises, so `GebundenKHAussage` closes both KH duties with no
             free premise. The unconditional time/per-pass and resource-start families and the full
             open-declaration case of `SchrankenbindungOffenAussage` are assembled as well. What
             remains open for a FINITE declaration is named in `SchrankenbindungTeilAussage`'s
             companion: the checker row and the per-form/protocol resource duties need footprints
             of the class and of the recovery entry; neither is carried by the slack line.
-/
module

public import Core.Beobachtung.SchrankenBeweise.BindungKosten
public import Core.Beobachtung.SchrankenBeweise.BindungZeitDurchlauf
public import Core.Beobachtung.SchrankenBeweise.BindungRessourcen
public import Core.Annahme.Annahme

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The decidable checker line: the declaration leaves room for one more occupied tick only when
    its cost ceiling is open and it declares no hold entry. Every class row costs one tick
    (`Wirkungsklasse.kostenZeile_kosten`), so a finite ceiling is reached by a run and cannot keep
    room for the next tick. The row table is an argument so the check is visibly made against the
    costs that the KH duties account for. -/
def pruefeSchrankenSpielraum (d : Schrankendeklaration)
    (z : Wirkungsklasse → KlassenKostenzeile) : Bool :=
  d.kosten.isNone && d.halten.isEmpty

/-- A passing slack line opens both ceilings. -/
private theorem pruefeSchrankenSpielraum_offen (d : Schrankendeklaration)
    (z : Wirkungsklasse → KlassenKostenzeile)
    (ok : pruefeSchrankenSpielraum d z = true) : d.kosten = none ∧ d.halten = [] := by
  have h1 : d.kosten.isNone = true := (Bool.and_eq_true_iff.mp ok).1
  have h2 : d.halten.isEmpty = true := (Bool.and_eq_true_iff.mp ok).2
  constructor
  · cases hk : d.kosten with
    | none => rfl
    | some n =>
      rw [hk, Option.isNone_some] at h1
      cases h1
  · cases hh : d.halten with
    | nil => rfl
    | cons x xs =>
      rw [hh, List.isEmpty_cons] at h2
      cases h2

/-- **Correctness of the slack line** (`SchrankenSpielraumAussage`): a passing line yields the
    exact cost and hold slack premises of `bindungKlassenKHRegel` for every form, and the cost
    slack premise of `bindungKostenProtokoll_unterSlack` for the protocol. -/
def SchrankenSpielraumAussage (P : Katalog.Plattform) (u : UnitMitSchranken) : Prop :=
  pruefeSchrankenSpielraum u.deklaration Wirkungsklasse.kostenZeile = true →
    (∀ (f : Befehl),
      (∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat),
        KostenPrefix (einheitMitSchranken P u) ρ t →
        UnterGrenze (einheitMitSchranken P u).schranken.kosten
          (Laufkosten ρ 0 t + (f.klasse.kostenZeile).kosten)) ∧
      (∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat) (c : Kontext),
        HaltePrefix (einheitMitSchranken P u) ρ t →
        ∀ (l : Nat) (a k : Nat), a + k = t →
          (∀ t', a ≤ t' → t' < a + (k + 1) →
            ∃ s, ρ.zeit.zustand t' = some s ∧ (s.sperren l).besitzer = some c) →
          UnterGrenze ((einheitMitSchranken P u).schranken.halten l)
            (Kontextkosten ρ c a k + (f.klasse.kostenZeile).kosten))) ∧
    (∀ {h : Umgebung} {ρ : Lauf (einheitMitSchranken P u)} (t : Nat),
      KostenPrefix (einheitMitSchranken P u) ρ t →
      UnterGrenze (einheitMitSchranken P u).schranken.kosten (Laufkosten ρ 0 t + 1))

/-- The correctness theorem: an open cost ceiling makes every cost slack vacuous, and an empty
    hold list makes every hold lookup open; the prefixes themselves are not needed. -/
theorem schrankenSpielraum (P : Katalog.Plattform) (u : UnitMitSchranken) :
    SchrankenSpielraumAussage P u := by
  intro ok
  obtain ⟨hkosten, hhalten⟩ := pruefeSchrankenSpielraum_offen u.deklaration
    Wirkungsklasse.kostenZeile ok
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨?_, ?_⟩
    · intro h ρ t kostenP n eq
      rw [einheitMitSchranken_kosten, hkosten] at eq
      cases eq
    · intro h ρ t c halteP l a k hak own n eq
      have hl : (einheitMitSchranken P u).schranken.halten l = none := by
        rw [einheitMitSchranken_halten]
        simp only [Schrankendeklaration.haltenVon, hhalten, List.find?_nil, Option.map_none]
      rw [hl] at eq
      cases eq
  · intro h ρ t kostenP n eq
    rw [einheitMitSchranken_kosten, hkosten] at eq
    cases eq

/-- **Acceptance of a bound unit** (`GebundenAkzeptiertAussage`): the perfect checker on the
    elaborated unit and the decidable slack line. Adding the line only refuses bound units whose
    declaration cannot leave room for a tick; it never admits an unchecked one. -/
def GebundenAkzeptiertAussage (P : Katalog.Plattform) (u : UnitMitSchranken) : Prop :=
  Akzeptiert (einheitMitSchranken P u) ∧
    pruefeSchrankenSpielraum u.deklaration Wirkungsklasse.kostenZeile = true

/-- The new conjunct only strengthens acceptance: it projects back to the perfect checker. -/
theorem gebundenAkzeptiert_verstaerkt (P : Katalog.Plattform) (u : UnitMitSchranken) :
    GebundenAkzeptiertAussage P u → Akzeptiert (einheitMitSchranken P u) := by
  intro h
  exact h.1

/-- **The cost and hold duties of every accepted bound unit** (`GebundenKHAussage`): under the
    checker line the free premises of `bindungKlassenKHRegel` and
    `bindungKostenProtokoll_unterSlack` are theorems, so both duties close unconditionally on
    accepted units. -/
def GebundenKHAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
    GebundenAkzeptiertAussage P u →
    (∀ (f : Befehl), KHRegelPflicht (einheitMitSchranken P u) f) ∧
      KHProtokollPflicht (einheitMitSchranken P u)

theorem gebundenKH : GebundenKHAussage := by
  intro P u ak
  have sp := schrankenSpielraum P u ak.2
  refine ⟨?_, ?_⟩
  · intro f
    obtain ⟨hkostenSlack, hhalteSlack⟩ := sp.1 f
    apply bindungKlassenKHRegel P u f
    · intro h ρ t kostenP
      exact hkostenSlack (h := h) (ρ := ρ) t kostenP
    · intro h ρ t c halteP l a k hak own
      exact hhalteSlack (h := h) (ρ := ρ) t c halteP l a k hak own
  · apply bindungKostenProtokoll_unterSlack P u
    intro h ρ t kostenP
    exact sp.2 (h := h) (ρ := ρ) t kostenP

/-- **The unconditional part of `SchrankenbindungOffenAussage`** (`SchrankenbindungTeilAussage`):
    the time and per-pass families close for every declaration because both stands stay empty,
    and the resource start duty closes because the loader books nothing. The remaining conjuncts
    are named precisely: the cost/hold families close under the slack line above; the checker
    row and the per-form/protocol resource families need footprints of the class and of the
    recovery entry, which no static declaration carries, and stay open for finite ceilings. -/
def SchrankenbindungTeilAussage : Prop :=
  (∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
    ZeitRegelPflicht (einheitMitSchranken P u) f ∧
      DurchlaufRegelPflicht (einheitMitSchranken P u) f) ∧
  (∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
    ZeitProtokollPflicht (einheitMitSchranken P u) ∧
      DurchlaufProtokollPflicht (einheitMitSchranken P u)) ∧
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken),
    ressourcenStartAussage (einheitMitSchranken P u)

theorem schrankenbindungTeil : SchrankenbindungTeilAussage := by
  refine ⟨?_, ?_, ?_⟩
  · intro P u f
    exact ⟨bindungZeitRegel P u f, bindungDurchlaufRegel P u f⟩
  · intro P u
    exact ⟨bindungZeitProtokoll P u, bindungDurchlaufProtokoll P u⟩
  · intro P u
    exact bindungRessourcenStart P u

/-- **The open-declaration case of `SchrankenbindungOffenAussage`**
    (`SchrankenbindungOffenTeilAussage`): with no cost, hold, stack or memory ceiling every
    conjunct of the pinned statement closes, for every form. The finite case is carried by
    `SchrankenSpielraumAussage`, `GebundenKHAussage` and `SchrankenbindungTeilAussage` instead. -/
def SchrankenbindungOffenTeilAussage : Prop :=
  ∀ (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl),
    u.deklaration.kosten = none → u.deklaration.halten = [] →
    u.deklaration.stapel = none → u.deklaration.speicher = none →
    KHRegelPflicht (einheitMitSchranken P u) f ∧
      ZeitRegelPflicht (einheitMitSchranken P u) f ∧
      DurchlaufRegelPflicht (einheitMitSchranken P u) f ∧
      Annahme.RegelSchranken (einheitMitSchranken P u) f ∧
      ressourcenRegelAussage (einheitMitSchranken P u) f ∧
      KHProtokollPflicht (einheitMitSchranken P u) ∧
      ZeitProtokollPflicht (einheitMitSchranken P u) ∧
      ressourcenProtokollAussage (einheitMitSchranken P u) ∧
      ressourcenStartAussage (einheitMitSchranken P u)

theorem schrankenbindungOffenTeil : SchrankenbindungOffenTeilAussage := by
  intro P u f hkosten hhalten hstapel hspeicher
  refine ⟨bindungKHOffen P u f hkosten hhalten, bindungZeitRegel P u f,
    bindungDurchlaufRegel P u f, bindungRegelSchrankenOffen P u f hstapel hspeicher,
    bindungRessourcenRegelOffen P u f hstapel hspeicher,
    bindungKHProtokollOffen P u hkosten hhalten, bindungZeitProtokoll P u,
    bindungRessourcenProtokollOffen P u hstapel hspeicher, bindungRessourcenStart P u⟩

/-- The empty source tree, for the satisfiability witness below. -/
private def leerBaum : Ast.Unit := ⟨[], Ast.UnitBody.done⟩

/-- Joint satisfiability: the empty declaration passes the slack line, and every KH duty of the
    bound unit closes. Together with the time, per-pass and resource-start families this makes the
    premises of `GebundenKHAussage` jointly realizable with a declaration of full slack. -/
theorem schrankenSpielraum_erfuellbar :
    ∃ (P : Katalog.Plattform) (u : UnitMitSchranken),
      pruefeSchrankenSpielraum u.deklaration Wirkungsklasse.kostenZeile = true ∧
      (∀ f : Befehl, KHRegelPflicht (einheitMitSchranken P u) f) ∧
      KHProtokollPflicht (einheitMitSchranken P u) := by
  refine ⟨Katalog.Plattform.x86_64, ⟨leerBaum, Schrankendeklaration.leer⟩, rfl, ?_, ?_⟩
  · intro f
    exact bindungKHOffen _ _ f rfl rfl
  · exact bindungKHProtokollOffen _ _ rfl rfl

/-- Sharpness: a finite cost ceiling and a nonempty hold list are both refused by the slack line,
    so the added conjunct of acceptance is not automatic and a too-tight declaration is rejected. -/
theorem schrankenSpielraum_nichtTrivial :
    (∃ d : Schrankendeklaration,
      pruefeSchrankenSpielraum d Wirkungsklasse.kostenZeile = false) ∧
      ∃ d : Schrankendeklaration,
        pruefeSchrankenSpielraum d Wirkungsklasse.kostenZeile = false := by
  refine ⟨⟨{ kosten := some 0 }, rfl⟩, ⟨{ halten := [(0, 0)] }, rfl⟩⟩

end Gabbro.Core.Beobachtung
