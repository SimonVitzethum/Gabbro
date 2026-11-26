module

public import Core.Ziel.Korrektheit.Instanz
public import Core.Ziel.Korrektheit.Maschine
public import Core.Linken.Modul

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The constructions that supply whole language units to the concrete model. Each constructor fixes the
    complete machine unit, including its rules, loader, clause table and hardware catalogue. -/
inductive EinheitHerkunft : Ast.Semantik.Einheit → Prop where
  | quelle (P : Katalog.Plattform) (t : Ast.Unit) : EinheitHerkunft (einheitVon P t)
  | mitInvarianten (P : Katalog.Plattform) (u : Ast.Semantik.UnitMitInvarianten) :
      EinheitHerkunft (Ast.Semantik.elaborierenMitInvarianten P u)
  | verlinkt (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment)
      (h : Linken.linke plan = some p) : EinheitHerkunft (p.einheit plan.plattform)

/-- The image of the whole-unit constructions, with equality inherited from the machine unit. -/
abbrev Spracheinheit := { E : Ast.Semantik.Einheit // EinheitHerkunft E }

theorem bezeichnet_herkunft {P : Katalog.Plattform} {a : Text.RawText} {E : Ast.Semantik.Einheit}
    (h : Ast.Semantik.Bezeichnet P Ast.Category.unit a E) : EinheitHerkunft E := by
  obtain ⟨t, _, hElab, _⟩ := h
  rw [Ast.Semantik.elab_vollstaendig hElab]
  exact .quelle P t

/-- Restricting the type of denoted units to their construction image preserves every denotation, including
    its existing platform admission conditions. -/
theorem bezeichnet_spracheinheit_iff (P : Katalog.Plattform) (a : Text.RawText) :
    (∃ E : Spracheinheit, Ast.Semantik.Bezeichnet P Ast.Category.unit a E.val) ↔
      ∃ E : Ast.Semantik.Einheit, Ast.Semantik.Bezeichnet P Ast.Category.unit a E := by
  constructor
  · rintro ⟨E, h⟩
    exact ⟨E.val, h⟩
  · rintro ⟨E, h⟩
    exact ⟨⟨E, bezeichnet_herkunft h⟩, h⟩

/-- Retagging existing runs with their whole-unit origin preserves acceptance, implementation and ideal run
    membership, and the simulation relation at the same runs. Both tags use the same underlying unit. -/
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

/-- The existing fragment proof covers a successful link when every input module has the proved classes.
    Linking preserves this premise by concatenation. -/
theorem ideal_verlinkte_einheit (zugriff : ZugriffZielAussage)
    (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment) (h : Linken.linke plan = some p)
    (klassen : ∀ m ∈ plan.module, m.fragment.KlassenRein) :
    Maschine.I.Bestimmt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system ∧
    Maschine.I.Fortschritt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system := by
  unfold Linken.linke at h
  split at h
  · cases h
    exact ideal_fragment_einheit zugriff _ plan.plattform (Linken.verknuepfte_klassenrein plan klassen)
  · cases h

/-- The outstanding ideal leg for accepted linked units. Keeping the acceptance premise here allows a proof
    using either the link checks and acceptance, or ideal rules for classes beyond the existing fragment proof. -/
def IdealVerlinkteEinheitAussage : Prop :=
  ∀ (plan : Linken.Bauplan) (p : Ast.Semantik.Fragment), Linken.linke plan = some p →
    Annahme.Akzeptiert (p.einheit plan.plattform) →
    Maschine.I.Bestimmt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system ∧
    Maschine.I.Fortschritt (p.einheit plan.plattform).einrichtung (p.einheit plan.plattform).system

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

end Gabbro.Core.Ziel.Korrektheit
