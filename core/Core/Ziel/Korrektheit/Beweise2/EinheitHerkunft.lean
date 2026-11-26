module

public import Core.Ziel.Korrektheit.Instanz
public import Core.Ziel.Korrektheit.Maschine
public import Core.Ziel.Korrektheit.Beweise2.Spracheinheit
public import Core.Linken.Aussage

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The dispatch convention is shared by all three whole-unit constructions. -/
theorem herkunft_fertig_ohne_kopf {E : Ast.Semantik.Einheit} (h : EinheitHerkunft E)
    (s : Ast.Semantik.Zustand) (c : Maschine.Kontext) (kopf : E.system.kopf s c = none) :
    E.system.fertig s c := by
  cases h <;> exact kopf

/-- The accepted counterexample with an injected rule table is outside the construction image. -/
theorem lueckenEinheit_ohne_herkunft : ¬ EinheitHerkunft lueckenEinheit := by
  intro h
  exact herkunft_fertig_ohne_kopf h (Maschine.I.start lueckenEinheit lueckenStart).2 (.faden 0) rfl

/-- On the construction image the existing frame relations reduce to the same acceptance, run membership
    and simulation at every run with those tags. -/
theorem spracheinheit_lauftransport (P : Katalog.Plattform) (B : FormBeleg) (E : Spracheinheit)
    (H : Katalog.Umgebung) (ρ : Maschine.Lauf E.val) (ι : Maschine.I.Lauf E.val) :
    ((R₀ P B).Akzeptiert E.val ↔ Annahme.Akzeptiert E.val) ∧
    ((R₀ P B).Laeufe E.val H ⟨E.val, ρ⟩ ↔ Maschine.Laeufe E.val H ρ) ∧
    ((R₀ P B).IdealLaeufe E.val ⟨E.val, ι⟩ ↔ Maschine.I.Laeufe E.val ι) ∧
    ((R₀ P B).Sim E.val ⟨E.val, ρ⟩ ⟨E.val, ι⟩ ↔ Maschine.I.Sim E.val ρ ι) := by
  refine ⟨Iff.rfl, ⟨And.right, fun h => ⟨rfl, h⟩⟩, ⟨And.right, fun h => ⟨rfl, h⟩⟩, ?_⟩
  constructor
  · rintro ⟨_, h, sim⟩
    cases h
    exact sim
  · exact fun h => ⟨rfl, rfl, h⟩

/-- The ideal leg for accepted linked units. -/
def IdealVerlinkteEinheitAussage : Prop :=
  ∀ (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment), Linken.linke plan = some p →
    Annahme.Akzeptiert (p.einheit plan.plattform) →
    Maschine.I.Bestimmt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system ∧
    Maschine.I.Fortschritt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system

/-- The linker enforces source origin and concatenation preserves the classes proved for that origin. -/
theorem ideal_verlinkte_einheit (zugriff : ZugriffZielAussage) : IdealVerlinkteEinheitAussage :=
  fun plan p h _ => ideal_fragment_einheit zugriff p plan.plattform (Linken.linke_klassenrein h)

theorem IdealVerlinkteEinheitAussage.erfuellbar :
    ∃ (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment), Linken.linke plan = some p ∧
      Annahme.Akzeptiert (p.einheit plan.plattform) :=
  ⟨Linken.beispielPlan, Linken.beispielFragment, Linken.beispielLinke, Linken.beispielAkzeptiert⟩

/-- The ideal leg on the construction image reduces to the linked case. Ordinary units and units carrying
    invariants receive determinacy and progress from their elaboration's class proofs. -/
theorem ideal_spracheinheit (zugriff : ZugriffZielAussage) (link : IdealVerlinkteEinheitAussage)
    (E : Spracheinheit) (akzeptiert : Annahme.Akzeptiert E.val) :
    Maschine.I.Bestimmt E.val.einrichtung E.val.system ∧
    Maschine.I.Fortschritt E.val.einrichtung E.val.system := by
  obtain ⟨E, herkunft⟩ := E
  cases herkunft with
  | quelle P t => exact ideal_akzeptierte_einheit zugriff P t
  | mitInvarianten P u => exact ideal_quelleinheit zugriff _ P (Or.inl ⟨u, rfl⟩)
  | verlinkt plan p h => exact link plan p h akzeptiert

/-- With the access-class proofs, the linked case is precisely what remains of the universal ideal leg.
    The converse uses the inclusion of every successful link, regardless of its classes. -/
theorem ideal_spracheinheit_iff (zugriff : ZugriffZielAussage) :
    (∀ E : Spracheinheit, Annahme.Akzeptiert E.val →
      Maschine.I.Bestimmt E.val.einrichtung E.val.system ∧
      Maschine.I.Fortschritt E.val.einrichtung E.val.system) ↔ IdealVerlinkteEinheitAussage := by
  refine ⟨?_, ideal_spracheinheit zugriff⟩
  intro ideal plan p h akzeptiert
  exact ideal ⟨p.einheit plan.plattform, .verlinkt plan p h⟩ akzeptiert

end Gabbro.Core.Ziel.Korrektheit
