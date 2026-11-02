/-
  File:      Grammatik/Speichermodell/Adressen/Layout.lean
  Subject:   AN ADDRESS LAYOUT OF THE CARRIERS (2026-10-22, review of gabbro_ziel, point 3).

  Machine G has no addresses: a table is a function of its index. A real memory lays the carriers out in bytes.
  `AdressLayout` is any such layout: an address space, a base and an element size per table, an offset and a size per
  field, an address and a size per global. An address is a pair (backing region, byte). Backing regions map to
  declared nominal data spaces; several distinct regions may have the same nominal space. Every OPEN region
  (`Deklaration.offen`, no element ceiling) has its own backing identity and reaches up without an end, so its
  growth can meet no other carrier. A nominal name alone establishes no separation. `LayoutOk` requires that the
  fields of an element lie inside it and apart, and the regions of different carriers lie apart.

  * `zelle_im_bereich` -- every byte of a cell `(t, k, f)` with `k` in the declared extent lies in the region of `t`;
  * `zellen_getrennt` -- two different cells in their extents share no byte, in one table or in two;
  * with Bereich.lean (`rufErreichbarGX_aussen`): every cell a run changes lies, with all its bytes, inside the
    region of its carrier -- no write leaves its carrier (the leg `speicherAdressen` of the goal).
-/
module
public import Grammatik.Speichermodell.Adressen.Bereich
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

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

variable {lay : AdressLayout D}

/-- A cell's backing realizes its table's declared logical space. -/
theorem zelle_im_raum (hL : LayoutOk lay) {t : D.Tab} {k : Int} {f : D.Feld t}
    {a : Adresse} (ha : lay.inZelle t k f a) : lay.nominal a.1 = D.tableSpace t := by
  rw [ha.1]
  exact (hL.tabellenRaum t).2

/-- A global's bytes realize its declared logical space. -/
theorem global_im_raum (hL : LayoutOk lay) {g : D.Glob} {a : Adresse}
    (ha : lay.inGlobal g a) : lay.nominal a.1 = D.globalSpace g := by
  rw [ha.1]
  exact (hL.globalerRaum g).2

/-- **A cell in its extent lies in the region of its table.** -/
theorem zelle_im_bereich (hL : LayoutOk lay) {t : D.Tab} {k : Int} (hk : ImBereich D t k) (f : D.Feld t)
    {a : Adresse} (ha : lay.inZelle t k f a) : lay.inTabelle t a := by
  obtain ⟨h0, h1, h2⟩ := ha
  have hf := hL.feld t f
  unfold AdressLayout.adresse at h1 h2
  refine ⟨h0, by omega, ?_⟩
  rcases hk.2 with ho | hc
  · exact .inl ho
  · right
    have hkn : k.toNat + 1 ≤ (D.count t).toNat := by have := hk.1; omega
    have : (k.toNat + 1) * lay.breite t ≤ (D.count t).toNat * lay.breite t := Nat.mul_le_mul_right _ hkn
    rw [Nat.succ_mul] at this
    omega

/-- **Two different cells of one table share no byte.** -/
theorem zellen_getrennt_tab (hL : LayoutOk lay) {t : D.Tab} {k k' : Int} (hk : ImBereich D t k)
    (hk' : ImBereich D t k') {f f' : D.Feld t} (hne : k ≠ k' ∨ f ≠ f') {a : Adresse} (ha : lay.inZelle t k f a) :
    ¬ lay.inZelle t k' f' a := by
  rintro ⟨-, h1', h2'⟩
  obtain ⟨-, h1, h2⟩ := ha
  unfold AdressLayout.adresse at h1 h2 h1' h2'
  have hf := hL.feld t f
  have hf' := hL.feld t f'
  by_cases hkk : k = k'
  · subst hkk
    rcases hne with hne | hne
    · exact hne rfl
    · rcases hL.felder t f f' hne with h | h <;> omega
  · have hn : k.toNat ≠ k'.toNat := by have := hk.1; have := hk'.1; omega
    rcases Nat.lt_or_gt_of_ne hn with hlt | hlt
    · have : (k.toNat + 1) * lay.breite t ≤ k'.toNat * lay.breite t := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at this
      omega
    · have : (k'.toNat + 1) * lay.breite t ≤ k.toNat * lay.breite t := Nat.mul_le_mul_right _ hlt
      rw [Nat.succ_mul] at this
      omega

/-- **Two cells of different tables share no byte.** -/
theorem zellen_getrennt (hL : LayoutOk lay) {t t' : D.Tab} {k k' : Int} (hk : ImBereich D t k)
    (hk' : ImBereich D t' k') (f : D.Feld t) (f' : D.Feld t') (ht : t ≠ t') {a : Adresse}
    (ha : lay.inZelle t k f a) : ¬ lay.inZelle t' k' f' a := fun ha' =>
  hL.tabellen t t' a ht (zelle_im_bereich hL hk f ha) (zelle_im_bereich hL hk' f' ha')

/-- **Every cell a run changes lies, with all its bytes, inside the region of its table.** -/
theorem geaendert_im_bereich {s0 s : Speicher D} (h : AussenGleich s0 s) (hL : LayoutOk lay) {t : D.Tab} {k : Int}
    {f : D.Feld t} (hne : s.slots t k f ≠ s0.slots t k f) :
    ImBereich D t k ∧ ∀ a, lay.inZelle t k f a → lay.inTabelle t a := by
  have hk : ImBereich D t k := Classical.byContradiction fun hk => hne (h t k f hk)
  exact ⟨hk, fun a ha => zelle_im_bereich hL hk f ha⟩

end Gabbro.Grammatik
