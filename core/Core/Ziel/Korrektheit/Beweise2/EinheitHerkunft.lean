module

public import Core.Ziel.Korrektheit.Instanz
public import Core.Ziel.Korrektheit.Maschine
public import Core.Ziel.Korrektheit.Beweise2.Spracheinheit
import Core.Ziel.Korrektheit.Beweise2.ZugriffIdealBestimmt
import Core.Ziel.Korrektheit.Beweise2.ZugriffNIFragmentBeweis
import Core.Ast.Semantik.Runtime.Klasse.ZugriffSicher.RennenLauf
public import Core.Linken.Aussage

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The dispatch convention is shared by all three whole-unit constructions. -/
theorem herkunft_fertig_ohne_kopf {E : Ast.Semantik.Einheit} (h : EinheitHerkunft E)
    (s : Ast.Semantik.Zustand) (c : Maschine.Kontext) (kopf : E.system.kopf s c = none) :
    E.system.fertig s c := by
  cases h <;> exact kopf

/-- The counterexample with an injected rule table is outside the construction image. -/
theorem lueckenEinheit_ohne_herkunft : ¬ EinheitHerkunft lueckenEinheit := by
  intro h
  exact herkunft_fertig_ohne_kopf h (Maschine.I.start lueckenEinheit lueckenStart).2 (.faden 0) rfl

/-- The local binding rejects the injected table while the unit remains in the run domain. -/
theorem lueckenEinheit_quelle_verweigert : ¬ Annahme.Quelle.Akzeptiert lueckenEinheit := by
  exact fun h => lueckenEinheit_ohne_herkunft (akzeptiert_herkunft h)

/-- On the construction image the existing frame relations reduce to the same acceptance, run membership
    and simulation at every run with those tags. -/
theorem spracheinheit_lauftransport (P : Katalog.Plattform) (B : FormBeleg) (E : Spracheinheit)
    (H : Katalog.Umgebung) (ρ : Maschine.Lauf E.val) (ι : Maschine.I.Lauf E.val) :
    ((R₀ P B).Akzeptiert E.val ↔ Annahme.Akzeptiert E.val) ∧
    ((R₀ P B).Laeufe E.val H ⟨E.val, ρ⟩ ↔ Maschine.Laeufe E.val H ρ) ∧
    ((R₀ P B).IdealLaeufe E.val ⟨E.val, ι⟩ ↔ Maschine.I.Laeufe E.val ι) ∧
    ((R₀ P B).Sim E.val ⟨E.val, ρ⟩ ⟨E.val, ι⟩ ↔ Maschine.I.Sim E.val ρ ι) := by
  have hacc : Annahme.Quelle.Akzeptiert E.val ↔ Annahme.Akzeptiert E.val := by
    obtain ⟨E, h⟩ := E
    cases h with
    | quelle P t => exact Annahme.Quelle.akzeptiert_elaboriert_iff P t
    | mitInvarianten P u => exact Annahme.Quelle.akzeptiert_mitInvarianten_iff P u
    | verlinkt plan p h => exact Annahme.Quelle.akzeptiert_link_iff plan h
  refine ⟨hacc, ⟨And.right, fun h => ⟨rfl, h⟩⟩, ⟨And.right, fun h => ⟨rfl, h⟩⟩, ?_⟩
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

theorem zugriffZiel : ZugriffZielAussage :=
  ⟨Ast.Semantik.zugriffSicherBeweis, zugriffIdealBestimmt, zugriffSchrittExistiert, zugriffNIFragment⟩

/-- The concrete local check supplies the ideal proof for every accepted machine unit. -/
theorem ideal_akzeptiert_quellbindung {E : Ast.Semantik.Einheit}
    (akzeptiert : Annahme.Quelle.Akzeptiert E) :
    Maschine.I.Bestimmt E.einrichtung E.system ∧ Maschine.I.Fortschritt E.einrichtung E.system := by
  obtain ⟨P, p, herkunft, _, bindung⟩ := akzeptiert.1.2
  change E = p.einheit P at bindung
  subst E
  have klassen : p.KlassenRein := by
    cases herkunft with
    | quelle _ t => exact Ast.Semantik.fragment_klassenrein Ast.Category.unit t
    | mitInvarianten _ u => exact Ast.Semantik.programm_klassenrein u.baum
    | verlinkt _ _ h => exact Linken.linke_klassenrein h
  exact ideal_fragment_einheit zugriffZiel p P klassen

/-- The linker enforces source origin and concatenation preserves the classes proved for that origin. -/
theorem ideal_verlinkte_einheit : IdealVerlinkteEinheitAussage :=
  fun plan p h _ => ideal_fragment_einheit zugriffZiel p plan.plattform (Linken.linke_klassenrein h)

theorem IdealVerlinkteEinheitAussage.erfuellbar :
    ∃ (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment), Linken.linke plan = some p ∧
      Annahme.Akzeptiert (p.einheit plan.plattform) :=
  ⟨Linken.beispielPlan, Linken.beispielFragment, Linken.beispielLinke, Linken.beispielAkzeptiert⟩

/-- Source elaboration and successful linking supply the class proofs for ideal determinacy and progress. -/
theorem ideal_spracheinheit (E : Spracheinheit) (akzeptiert : Annahme.Akzeptiert E.val) :
    Maschine.I.Bestimmt E.val.einrichtung E.val.system ∧
    Maschine.I.Fortschritt E.val.einrichtung E.val.system := by
  obtain ⟨E, herkunft⟩ := E
  cases herkunft with
  | quelle P t => exact ideal_akzeptierte_einheit zugriffZiel P t
  | mitInvarianten P u => exact ideal_quelleinheit zugriffZiel _ P (Or.inl ⟨u, rfl⟩)
  | verlinkt plan p h => exact ideal_verlinkte_einheit plan p h akzeptiert

/-- The universal ideal leg includes every successful link. -/
theorem ideal_spracheinheit_iff :
    (∀ E : Spracheinheit, Annahme.Akzeptiert E.val →
      Maschine.I.Bestimmt E.val.einrichtung E.val.system ∧
      Maschine.I.Fortschritt E.val.einrichtung E.val.system) ↔ IdealVerlinkteEinheitAussage := by
  refine ⟨?_, fun _ => ideal_spracheinheit⟩
  intro ideal plan p h akzeptiert
  exact ideal ⟨p.einheit plan.plattform, .verlinkt plan p h⟩ akzeptiert

end Gabbro.Core.Ziel.Korrektheit
