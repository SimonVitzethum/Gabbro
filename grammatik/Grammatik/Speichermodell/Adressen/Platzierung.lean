/-
  File:      Grammatik/Speichermodell/Adressen/Platzierung.lean
  Subject:   **STATIC PLACEMENT (C14)**: the alignment and the section a static asks for, and what a layout
             must satisfy to honour them.

  An `AdressLayout` (Layout.lean) gives every global a base and a size. Placement adds, per global, an
  evaluated ALIGNMENT (a positive power of two) and an optional SECTION NAME, and a checked profile POLICY
  from section names to access rights. A section is an opaque label of the selected image -- not implicitly
  ELF, not a physical address; the image mapping establishes the policy, and a string in metadata alone
  discharges nothing: `PlatzOk` is what a layout must satisfy, `Platzierung` is the data it is judged by.

  * `ausrichtungB` -- the Bool for "a positive power of two below 2^64", with its soundness;
  * `PlatzOk` -- bases aligned, every named section known to the policy, no section both writable and
    executable (no data-execute / write-code alias), read-only statics only in non-writable sections and
    mutable ones only in writable sections;
  * `platz_ausgerichtet`, `platz_kein_wx`, `platz_nur_lesen`, `platz_schreibbar` -- what `PlatzOk` gives.

  Not here (owned by the IR layout proofs): the full aggregate span of a multiword static and its
  initializer contents, checked offset/size rounding at the encoding, and the startup/relocation proof.
-/
module
public import Grammatik.Speichermodell.Adressen.Layout
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The access rights of an image section. -/
structure Zugriff where
  lesen : Bool
  schreiben : Bool
  ausfuehren : Bool
  deriving DecidableEq, Repr

/-- A section is writable XOR executable, never both: no alias between data that is written and code that
    runs. -/
def Zugriff.wxFrei (z : Zugriff) : Bool := !(z.schreiben && z.ausfuehren)

/-- The checked profile policy: the rights of every section name the image knows; `none` is an unknown
    section. -/
abbrev AbschnittPolitik : Type := String → Option Zugriff

/-- **A bound for an alignment**: a power of two below `2^64`. -/
def ausrichtungB (n : Nat) : Bool := (List.range 64).any fun k => decide (2 ^ k = n)

/-- A passing alignment is a positive power of two. -/
theorem ausrichtungB_sound {n : Nat} (h : ausrichtungB n = true) : ∃ k, n = 2 ^ k ∧ 0 < n := by
  simp only [ausrichtungB, List.any_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨k, _, hk⟩ := h
  exact ⟨k, hk.symm, hk ▸ Nat.two_pow_pos k⟩

/-- Every power of two below `2^64` passes. -/
theorem ausrichtungB_pot (k : Nat) (hk : k < 64) : ausrichtungB (2 ^ k) = true := by
  simp only [ausrichtungB, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨k, hk, rfl⟩

/-- **What the source asks of each global's placement**: an evaluated alignment (`1` for none) and an
    optional section name. -/
structure Platzierung (D : Deklaration) where
  ausrichtung : D.Glob → Nat
  abschnitt : D.Glob → Option String

/-- **A layout honours a placement under a policy.** `schreibbar g` says the static is written (`mut`). -/
structure PlatzOk (lay : AdressLayout D) (pl : Platzierung D) (pol : AbschnittPolitik)
    (schreibbar : D.Glob → Bool) : Prop where
  /-- The alignment is a power of two. -/
  zweierpotenz : ∀ g, ausrichtungB (pl.ausrichtung g) = true
  /-- The base lies on the alignment. -/
  ausgerichtet : ∀ g, lay.gbasis g % pl.ausrichtung g = 0
  /-- A named section is known to the policy, never writable and executable, readable, and writable exactly
      when the static is. -/
  abschnitt : ∀ g s, pl.abschnitt g = some s →
    ∃ z, pol s = some z ∧ z.wxFrei = true ∧ z.lesen = true ∧ z.schreiben = schreibbar g

variable {lay : AdressLayout D} {pl : Platzierung D} {pol : AbschnittPolitik} {sb : D.Glob → Bool}

/-- **The base of a placed global is a multiple of its alignment.** -/
theorem platz_ausgerichtet (h : PlatzOk lay pl pol sb) (g : D.Glob) : pl.ausrichtung g ∣ lay.gbasis g :=
  Nat.dvd_of_mod_eq_zero (h.ausgerichtet g)

/-- **No placed global lies in a section that is both writable and executable.** -/
theorem platz_kein_wx (h : PlatzOk lay pl pol sb) {g : D.Glob} {s : String}
    (hs : pl.abschnitt g = some s) : ∃ z, pol s = some z ∧ ¬ (z.schreiben = true ∧ z.ausfuehren = true) := by
  obtain ⟨z, hz, hw, _, _⟩ := h.abschnitt g s hs
  refine ⟨z, hz, ?_⟩
  rintro ⟨h1, h2⟩
  simp [Zugriff.wxFrei, h1, h2] at hw

/-- **A read-only static is never placed in a writable section.** -/
theorem platz_nur_lesen (h : PlatzOk lay pl pol sb) {g : D.Glob} {s : String}
    (hs : pl.abschnitt g = some s) (hr : sb g = false) : ∃ z, pol s = some z ∧ z.schreiben = false := by
  obtain ⟨z, hz, _, _, hwr⟩ := h.abschnitt g s hs
  exact ⟨z, hz, by rw [hwr, hr]⟩

/-- **A mutable static is placed only in a section its policy lets be written.** -/
theorem platz_schreibbar (h : PlatzOk lay pl pol sb) {g : D.Glob} {s : String}
    (hs : pl.abschnitt g = some s) (hw : sb g = true) : ∃ z, pol s = some z ∧ z.schreiben = true := by
  obtain ⟨z, hz, _, _, hwr⟩ := h.abschnitt g s hs
  exact ⟨z, hz, by rw [hwr, hw]⟩

/-- **Two different placed globals of a correct layout share no byte** (the layout's own clause, restated
    next to the placement: alignment moves bases, never overlaps them). -/
theorem platz_getrennt (hL : LayoutOk lay) (_ : PlatzOk lay pl pol sb) {g g' : D.Glob} (hne : g ≠ g')
    {a : Adresse} (ha : lay.inGlobal g a) : ¬ lay.inGlobal g' a :=
  hL.globale g g' a hne ha

end Gabbro.Grammatik
