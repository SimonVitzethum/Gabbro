module

public import Core.Annahme.Annahme
public import Core.Ast.Program.Linken
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Annahme.Quelle

open Gabbro.Core
open Ast.Semantik

/-- The source constructions supplying the ideal rules of a whole unit. -/
inductive FragmentHerkunft : Fragment → Prop where
  | quelle (t : Ast.Unit) : FragmentHerkunft (fragment Ast.Category.unit t)
  | mitInvarianten (u : UnitMitInvarianten) : FragmentHerkunft (programmMitInvarianten u)
  | verlinkt (plan : Linken.Bauplan) (p : Fragment) :
      Linken.linke plan = some p → FragmentHerkunft p

/-- Bind exactly the state interpretation and rule projections read by the ideal machine. -/
def Idealbindung (E : Ast.Semantik.Einheit) (p : Fragment) : Prop :=
  E.einrichtung = einrichtung p.eingang p.eintritte p.speicher ∧
  E.system.kopf = (system p.code).kopf ∧
  E.system.fertig = (system p.code).fertig ∧
  E.system.blockiert = (system p.code).blockiert ∧
  (∀ i, (E.system.regel i).ideal = Befehl.ideal i)

/-- Local acceptance for the concrete language checks the provenance of the ideal rules. -/
def Lokal (E : Ast.Semantik.Einheit) : Prop :=
  Annahme.Lokal E ∧ ∃ p, FragmentHerkunft p ∧ Idealbindung E p

def Akzeptiert (E : Ast.Semantik.Einheit) : Prop :=
  Lokal E ∧ Annahme.KlauselnWahr E ∧ Annahme.WaechterHalten E

theorem Akzeptiert.regeln {E : Ast.Semantik.Einheit} (h : Akzeptiert E) :
    Annahme.Akzeptiert E := ⟨h.1.1, h.2⟩

theorem akzeptiert_iff_of_bindung {E : Ast.Semantik.Einheit}
    (bindung : ∃ p, FragmentHerkunft p ∧ Idealbindung E p) :
    Akzeptiert E ↔ Annahme.Akzeptiert E :=
  ⟨Akzeptiert.regeln, fun h => ⟨⟨h.1, bindung⟩, h.2⟩⟩

theorem akzeptiert_fragment_iff (P : Katalog.Plattform) {p : Fragment} (h : FragmentHerkunft p) :
    Akzeptiert (p.einheit P) ↔ Annahme.Akzeptiert (p.einheit P) :=
  akzeptiert_iff_of_bindung ⟨p, h, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem akzeptiert_elaboriert_iff (P : Katalog.Plattform) (t : Ast.Unit) :
    Akzeptiert (elaborieren P t) ↔ Annahme.Akzeptiert (elaborieren P t) :=
  akzeptiert_fragment_iff P (.quelle t)

theorem akzeptiert_mitInvarianten_iff (P : Katalog.Plattform) (u : UnitMitInvarianten) :
    Akzeptiert (elaborierenMitInvarianten P u) ↔ Annahme.Akzeptiert (elaborierenMitInvarianten P u) :=
  akzeptiert_fragment_iff P (.mitInvarianten u)

theorem akzeptiert_link_iff (plan : Linken.Bauplan) {p : Fragment} (h : Linken.linke plan = some p) :
    Akzeptiert (p.einheit plan.plattform) ↔ Annahme.Akzeptiert (p.einheit plan.plattform) :=
  akzeptiert_fragment_iff plan.plattform (.verlinkt plan p h)

end Gabbro.Core.Annahme.Quelle
