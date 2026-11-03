module

public import Grammatik.Speichermodell.Adressen.Layout

@[expose] public section

namespace Gabbro.Grammatik.NamedSpaces

/-- Two open byte carriers and one global in one declared nominal space. -/
@[reducible] def declaration : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 0
  offen := fun _ => true
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 255
  erlaubt := fun _ _ _ _ => true
  tabNr := fun | 0 => some false | 1 => some true | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .bool
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun l => l.elim
  maskiert := fun l => l.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Empty
  sig := fun f => f.elim
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => false, fun _ => false, [], [], none, {}⟩
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => nomatch h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun _ h => nomatch h
  dataSpaces := ["normal", "sharedData"]
  tableSpace := fun _ => 1
  globalSpace := fun _ => 1

/-- The logical name is shared, but the two unbounded extents and the global have distinct backings. -/
def layout : AdressLayout declaration where
  raum := fun t => if t then 2 else 1
  basis := fun _ => 0
  breite := fun _ => 1
  versatz := fun _ _ => 0
  groesse := fun _ _ => 1
  gbasis := fun _ => 0
  ggroesse := fun _ => 1
  graum := fun _ => 3
  nominal := fun _ => 1

theorem layout_ok : LayoutOk layout where
  tabellenRaum := fun _ => ⟨by change 1 < 2; decide, rfl⟩
  offen := by
    intro t _
    constructor
    · intro t' hne
      cases t <;> cases t' <;> simp_all [layout]
    · intro g
      cases t <;> simp [layout]
  feld := fun _ _ => by change 0 + 1 ≤ 1; decide
  felder := fun _ _ _ h => absurd rfl h
  tabellen := by
    intro t t' a hne ha ha'
    have h := ha.1.symm.trans ha'.1
    cases t <;> cases t' <;> simp_all [layout]
  tabGlob := by
    intro t g a ha ha'
    have h := ha.1.symm.trans ha'.1
    cases t <;> simp [layout] at h
  globale := fun _ _ _ h => absurd rfl h
  globalerRaum := fun _ => ⟨by change 1 < 2; decide, rfl⟩

/-- Nonempty, unbounded regions may share a declared space without sharing a byte. -/
theorem named_spaces_zeuge :
    declaration.tableSpace false = declaration.tableSpace true ∧
    layout.raum false ≠ layout.raum true ∧ LayoutOk layout ∧
    layout.inZelle false 100 () (1, 100) ∧ layout.inZelle true 100 () (2, 100) ∧
    layout.inGlobal () (3, 0) := by
  exact ⟨rfl, by decide, layout_ok,
    ⟨rfl, by decide, by decide⟩, ⟨rfl, by decide, by decide⟩,
    ⟨rfl, by decide, by decide⟩⟩

end Gabbro.Grammatik.NamedSpaces
