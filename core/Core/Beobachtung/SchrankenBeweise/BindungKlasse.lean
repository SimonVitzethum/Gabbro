/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungKlasse.lean
  Subject:   The checker row of `SchrankenbindungOffenAussage` on a bound unit with a finite
             declaration. `klassenSchranken` discharges `RegelSchranken` from the footprint
             of the instruction's effect class; the footprint is the exact premise the
             unconditional statement omits. Specialising it to `einheitMitSchranken`
             fixes that premise without weakening the row. For the open declaration the
             unconditional sub-theorem is `bindungRegelSchrankenOffen`.
-/
module

public import Core.Beobachtung.SchrankenBeweise.BindungOffen
public import Core.Beobachtung.SchrankenBeweise.Klasse

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast.Semantik

/-- The checker row for a bound unit and an instruction whose class footprint keeps the
    declared stack and memory bounds. The footprint is the missing premise. -/
theorem bindungKlassenRegel (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl)
    (fuss : Fussabdruck (einheitMitSchranken P u) f
      (KlassenFuss (einheitMitSchranken P u) f.klasse)) :
    Annahme.RegelSchranken (einheitMitSchranken P u) f := by
  exact klassenSchranken (einheitMitSchranken P u) f fuss

end Gabbro.Core.Beobachtung
