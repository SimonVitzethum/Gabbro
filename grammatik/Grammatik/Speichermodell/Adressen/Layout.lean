/-
  File:      Grammatik/Speichermodell/Adressen/Layout.lean
  Subject:   AN ADDRESS LAYOUT OF THE CARRIERS (2026-10-22, review of gabbro_ziel, point 3).

  Machine G has no addresses: a table is a function of its index. A real memory lays the carriers out in bytes.
  `AdressLayout` is any such layout: a base and an element size per table, an offset and a size per field, an
  address and a size per global. `LayoutOk` says what every layout a correct loader produces must satisfy: the
  fields of an element lie inside it and apart, and the regions of different carriers lie apart.

  * `zelle_im_bereich` -- every byte of a cell `(t, k, f)` with `k` in the declared extent lies in the region of `t`;
  * `zellen_getrennt` -- two different cells in their extents share no byte, in one table or in two;
  * with Bereich.lean (`rufErreichbarGX_aussen`): every cell a run changes lies, with all its bytes, inside the
    region of its carrier -- no write leaves its carrier (the leg `speicherAdressen` of the goal).
-/
import Grammatik.Speichermodell.Adressen.Bereich

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **An address layout**: a base and an element size per table, an offset and a size per field; an address and a
    size per global. -/
structure AdressLayout (D : Deklaration) where
  basis : D.Tab → Nat
  breite : D.Tab → Nat
  versatz : ∀ t, D.Feld t → Nat
  groesse : ∀ t, D.Feld t → Nat
  gbasis : D.Glob → Nat
  ggroesse : D.Glob → Nat

namespace AdressLayout

variable (lay : AdressLayout D)

/-- The first byte of cell `(t, k, f)`. -/
def adresse (t : D.Tab) (k : Int) (f : D.Feld t) : Nat := lay.basis t + k.toNat * lay.breite t + lay.versatz t f

/-- Byte `a` belongs to cell `(t, k, f)`. -/
def inZelle (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat) : Prop :=
  lay.adresse t k f ≤ a ∧ a < lay.adresse t k f + lay.groesse t f

/-- Byte `a` lies in the region of table `t`. -/
def inTabelle (t : D.Tab) (a : Nat) : Prop := lay.basis t ≤ a ∧ a < lay.basis t + (D.count t).toNat * lay.breite t

/-- Byte `a` lies in the region of global `g`. -/
def inGlobal (g : D.Glob) (a : Nat) : Prop := lay.gbasis g ≤ a ∧ a < lay.gbasis g + lay.ggroesse g

end AdressLayout

/-- **What a correct layout satisfies.** -/
structure LayoutOk (lay : AdressLayout D) : Prop where
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

variable {lay : AdressLayout D}

/-- **A cell in its extent lies in the region of its table.** -/
theorem zelle_im_bereich (hL : LayoutOk lay) {t : D.Tab} {k : Int} (hk : ImBereich D t k) (f : D.Feld t) {a : Nat}
    (ha : lay.inZelle t k f a) : lay.inTabelle t a := by
  obtain ⟨h1, h2⟩ := ha
  have hf := hL.feld t f
  have hkn : k.toNat + 1 ≤ (D.count t).toNat := by have := hk.2; have := hk.1; omega
  unfold AdressLayout.adresse at h1 h2
  refine ⟨by omega, ?_⟩
  have : (k.toNat + 1) * lay.breite t ≤ (D.count t).toNat * lay.breite t := Nat.mul_le_mul_right _ hkn
  rw [Nat.succ_mul] at this
  omega

/-- **Two different cells of one table share no byte.** -/
theorem zellen_getrennt_tab (hL : LayoutOk lay) {t : D.Tab} {k k' : Int} (hk : ImBereich D t k)
    (hk' : ImBereich D t k') {f f' : D.Feld t} (hne : k ≠ k' ∨ f ≠ f') {a : Nat} (ha : lay.inZelle t k f a) :
    ¬ lay.inZelle t k' f' a := by
  rintro ⟨h1', h2'⟩
  obtain ⟨h1, h2⟩ := ha
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
    (hk' : ImBereich D t' k') (f : D.Feld t) (f' : D.Feld t') (ht : t ≠ t') {a : Nat} (ha : lay.inZelle t k f a) :
    ¬ lay.inZelle t' k' f' a := fun ha' =>
  hL.tabellen t t' a ht (zelle_im_bereich hL hk f ha) (zelle_im_bereich hL hk' f' ha')

/-- **Every cell a run changes lies, with all its bytes, inside the region of its table.** -/
theorem geaendert_im_bereich {s0 s : Speicher D} (h : AussenGleich s0 s) (hL : LayoutOk lay) {t : D.Tab} {k : Int}
    {f : D.Feld t} (hne : s.slots t k f ≠ s0.slots t k f) :
    ImBereich D t k ∧ ∀ a, lay.inZelle t k f a → lay.inTabelle t a := by
  have hk : ImBereich D t k := Classical.byContradiction fun hk => hne (h t k f hk)
  exact ⟨hk, fun a ha => zelle_im_bereich hL hk f ha⟩

end Gabbro.Grammatik
