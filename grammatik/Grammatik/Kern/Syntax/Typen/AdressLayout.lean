module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Index `k` lies in the declared extent of table `t`: below its count, or anywhere above `0` in an open region. -/
def ImBereich (D : Deklaration) (t : D.Tab) (k : Int) : Prop := 0 ≤ k ∧ (D.offen t = true ∨ k < D.count t)

/-- An address: a backing-region identity and a byte in it. -/
abbrev Adresse : Type := Nat × Nat

/-- A byte layout with separate backing-region and declared nominal-space identities. -/
structure AdressLayout (D : Deklaration) where
  raum : D.Tab → Nat
  basis : D.Tab → Nat
  breite : D.Tab → Nat
  versatz : ∀ t, D.Feld t → Nat
  groesse : ∀ t, D.Feld t → Nat
  gbasis : D.Glob → Nat
  ggroesse : D.Glob → Nat
  /-- The backing region of a global. -/
  graum : D.Glob → Nat := fun _ => 0
  /-- Realization of backing regions in the finite nominal-space registry. -/
  nominal : Nat → Nat := fun _ => 0

namespace AdressLayout

variable (lay : AdressLayout D)

/-- The first byte of cell `(t, k, f)`. -/
def adresse (t : D.Tab) (k : Int) (f : D.Feld t) : Nat := lay.basis t + k.toNat * lay.breite t + lay.versatz t f

/-- Byte `a` belongs to cell `(t, k, f)`. -/
def inZelle (t : D.Tab) (k : Int) (f : D.Feld t) (a : Adresse) : Prop :=
  a.1 = lay.raum t ∧ lay.adresse t k f ≤ a.2 ∧ a.2 < lay.adresse t k f + lay.groesse t f

/-- Byte `a` lies in the region of table `t`: from its base up to its extent, or without end for an open region. -/
def inTabelle (t : D.Tab) (a : Adresse) : Prop :=
  a.1 = lay.raum t ∧ lay.basis t ≤ a.2 ∧ (D.offen t = true ∨ a.2 < lay.basis t + (D.count t).toNat * lay.breite t)

/-- Byte `a` lies in the region of global `g`. -/
def inGlobal (g : D.Glob) (a : Adresse) : Prop :=
  a.1 = lay.graum g ∧ lay.gbasis g ≤ a.2 ∧ a.2 < lay.gbasis g + lay.ggroesse g

end AdressLayout

/-- **What a correct layout satisfies.** -/
structure LayoutOk (lay : AdressLayout D) : Prop where
  /-- A table's backing realizes its declared nominal space, which must exist. -/
  tabellenRaum : ∀ t, D.tableSpace t < D.dataSpaces.length ∧
    lay.nominal (lay.raum t) = D.tableSpace t
  /-- An unbounded region has a distinct backing identity even within one nominal space. -/
  offen : ∀ t, D.offen t = true →
    (∀ t', t ≠ t' → lay.raum t ≠ lay.raum t') ∧ (∀ g, lay.raum t ≠ lay.graum g)
  /-- A field lies inside its element. -/
  feld : ∀ t (f : D.Feld t), lay.versatz t f + lay.groesse t f ≤ lay.breite t
  /-- Two fields of an element share no byte. -/
  felder : ∀ t (f f' : D.Feld t), f ≠ f' →
    lay.versatz t f + lay.groesse t f ≤ lay.versatz t f' ∨ lay.versatz t f' + lay.groesse t f' ≤ lay.versatz t f
  /-- Two tables share no byte. -/
  tabellen : ∀ t t' a, t ≠ t' → lay.inTabelle t a → ¬ lay.inTabelle t' a
  /-- A table and a global share no byte. -/
  tabGlob : ∀ t g a, lay.inTabelle t a → ¬ lay.inGlobal g a
  /-- Two globals share no byte. -/
  globale : ∀ g g' a, g ≠ g' → lay.inGlobal g a → ¬ lay.inGlobal g' a
  /-- Globals obey the same declaration-to-backing correspondence as tables. -/
  globalerRaum : ∀ g, D.globalSpace g < D.dataSpaces.length ∧
    lay.nominal (lay.graum g) = D.globalSpace g := by
      intro g; exact ⟨by decide, rfl⟩

end Gabbro.Grammatik
