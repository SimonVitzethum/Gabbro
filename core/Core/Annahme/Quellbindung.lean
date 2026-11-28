module

public import Core.Annahme.Annahme
public import Core.Ast.Program.Linken
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Annahme.Quelle

open Gabbro.Core
open Ast.Semantik

/-- The source constructions supplying a whole unit on its target platform. -/
inductive FragmentHerkunft : Katalog.Plattform → Fragment → Prop where
  | quelle (P : Katalog.Plattform) (t : Ast.Unit) :
      FragmentHerkunft P (fragment Ast.Category.unit t)
  | mitInvarianten (P : Katalog.Plattform) (u : UnitMitInvarianten) :
      FragmentHerkunft P (programmMitInvarianten u)
  | verlinkt (plan : Linken.Bauplan) (p : Fragment) :
      Linken.linke plan = some p → FragmentHerkunft plan.plattform p

/-- Bind exactly the state interpretation and rule projections read by the ideal machine. -/
def Idealbindung (E : Ast.Semantik.Einheit) (p : Fragment) : Prop :=
  E.einrichtung = einrichtung p.eingang p.eintritte p.speicher ∧
  E.system.kopf = (system p.code).kopf ∧
  E.system.fertig = (system p.code).fertig ∧
  E.system.blockiert = (system p.code).blockiert ∧
  (∀ i, (E.system.regel i).ideal = Befehl.ideal i)

/-- Bind the whole machine unit to the canonical elaboration on the source construction's platform. -/
def Implementierungsbindung (E : Ast.Semantik.Einheit) (p : Fragment) (P : Katalog.Plattform) : Prop :=
  E = p.einheit P

/-- Local acceptance binds the ideal rules and the implementation to the same source construction. -/
def Lokal (E : Ast.Semantik.Einheit) : Prop :=
  Annahme.Lokal E ∧ ∃ P p, FragmentHerkunft P p ∧ Idealbindung E p ∧ Implementierungsbindung E p P

def Akzeptiert (E : Ast.Semantik.Einheit) : Prop :=
  Lokal E ∧ Annahme.KlauselnWahr E ∧ Annahme.WaechterHalten E

theorem Akzeptiert.regeln {E : Ast.Semantik.Einheit} (h : Akzeptiert E) :
    Annahme.Akzeptiert E := ⟨h.1.1, h.2⟩

theorem akzeptiert_iff_of_bindung {E : Ast.Semantik.Einheit}
    (bindung : ∃ P p, FragmentHerkunft P p ∧ Idealbindung E p ∧ Implementierungsbindung E p P) :
    Akzeptiert E ↔ Annahme.Akzeptiert E :=
  ⟨Akzeptiert.regeln, fun h => ⟨⟨h.1, bindung⟩, h.2⟩⟩

theorem akzeptiert_fragment_iff (P : Katalog.Plattform) {p : Fragment} (h : FragmentHerkunft P p) :
    Akzeptiert (p.einheit P) ↔ Annahme.Akzeptiert (p.einheit P) :=
  akzeptiert_iff_of_bindung ⟨P, p, h, ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩, rfl⟩

theorem akzeptiert_elaboriert_iff (P : Katalog.Plattform) (t : Ast.Unit) :
    Akzeptiert (elaborieren P (category := Ast.Category.unit) t) ↔ Annahme.Akzeptiert (elaborieren P (category := Ast.Category.unit) t) :=
  akzeptiert_fragment_iff P (.quelle P t)

theorem akzeptiert_mitInvarianten_iff (P : Katalog.Plattform) (u : UnitMitInvarianten) :
    Akzeptiert (elaborierenMitInvarianten P u) ↔ Annahme.Akzeptiert (elaborierenMitInvarianten P u) :=
  akzeptiert_fragment_iff P (.mitInvarianten P u)

theorem akzeptiert_link_iff (plan : Linken.Bauplan) {p : Fragment} (h : Linken.linke plan = some p) :
    Akzeptiert (p.einheit plan.plattform) ↔ Annahme.Akzeptiert (p.einheit plan.plattform) :=
  akzeptiert_fragment_iff plan.plattform (.verlinkt plan p h)

end Gabbro.Core.Annahme.Quelle
