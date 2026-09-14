/-
  File:      Grammatik/Isabelle/DeviceKonstruktor.lean
  Port of:   beweise/Device_Konstruktor.thy (template `device.konstruktor`, S13)

  From the address comes a typed handle, and the generated accesses hit the
  `device` block's DECLARED positions. That the declared positions are the
  device's is an AXIOM-LAYER assumption and is not shown here -- what remains
  is the arithmetic: two different registers never hit the same cell, a bank
  entry sits at `basis + at + k * stride`, and a bit field stays in the word
  (the last is declined with «B24» on both sides).

  Adaptations (same content, Lean core without mathlib):
  - Cells are predicates over Nat (Isabelle: sets of addresses);
    disjointness is the pointwise form (Isabelle: intersection is empty).
  - Addresses are Nat directly (Isabelle type synonym, which IS Nat);
    a named synonym would hide the variables from omega.
-/

namespace Gabbro.Grammatik.Isabelle.DeviceKonstruktor

/-- A register: offset and width (bytes, from the register width).
    (Isabelle: `record reg`.) -/
structure Reg where
  offset : Nat
  weite : Nat

/-- The cell of a register at base `b`. (Isabelle: `zelle`.) -/
def zelle (b : Nat) (r : Reg) (a : Nat) : Prop :=
  b + r.offset ≤ a ∧ a < b + r.offset + r.weite

/-- Two registers with separate positions. (Isabelle: `getrennt`.) -/
def getrennt (r s : Reg) : Prop :=
  r.offset + r.weite ≤ s.offset ∨ s.offset + s.weite ≤ r.offset

/-- THE carrying statement: two registers with separate positions never touch
    each other -- FOR EVERY base.
    (Isabelle: `getrennte_register_treffen_getrennte_zellen`.) -/
theorem getrennte_register_treffen_getrennte_zellen (b : Nat) (r s : Reg)
    (h : getrennt r s) (a : Nat) :
    ¬ (zelle b r a ∧ zelle b s a) := by
  simp only [getrennt] at h
  simp only [zelle]
  rintro ⟨⟨hr1, hr2⟩, ⟨hs1, hs2⟩⟩
  rcases h with h | h <;> omega

/-- And the base drops out -- which is why the handle may be the constructor:
    separation is a property of the DECLARATION, not of the address where the
    device happens to sit.
    (Isabelle: `trennung_haengt_nicht_an_der_basis`.) -/
theorem trennung_haengt_nicht_an_der_basis (r s : Reg)
    (h : getrennt r s) (b a : Nat) :
    ¬ (zelle b r a ∧ zelle b s a) :=
  getrennte_register_treffen_getrennte_zellen b r s h a

/-! ## The bank -/

/-- A bank entry: `basis + start + k * schritt`.
    (Isabelle: `bankzelle`.) -/
def bankzelle (b start schritt k : Nat) (a : Nat) : Prop :=
  b + start + k * schritt ≤ a ∧ a < b + start + k * schritt + schritt

/-- Bank entries do not overlap.
    (Isabelle: `bankeintraege_ueberlappen_nicht`.) -/
theorem bankeintraege_ueberlappen_nicht (b start schritt j k : Nat)
    (hjk : j < k) (a : Nat) :
    ¬ (bankzelle b start schritt j a ∧ bankzelle b start schritt k a) := by
  simp only [bankzelle]
  rintro ⟨⟨hj1, hj2⟩, ⟨hk1, hk2⟩⟩
  have hle : j + 1 ≤ k := by omega
  have hmono : (j + 1) * schritt ≤ k * schritt :=
    Nat.mul_le_mul hle (Nat.le_refl schritt)
  have hexpand : (j + 1) * schritt = j * schritt + schritt := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- A stride of zero breaks it -- immediately: then all entries coincide. The
    theorem above needs no premise for it, because at `schritt = 0` every
    `bankzelle` is EMPTY. A bank with `stride 0` generates no accesses, and
    the generator should reject it instead of letting it idle.
    (Isabelle: `stride_null_macht_die_bank_leer`.) -/
theorem stride_null_macht_die_bank_leer (b start k a : Nat) :
    ¬ bankzelle b start 0 k a := by
  simp only [bankzelle, Nat.mul_zero]
  rintro ⟨h1, h2⟩
  omega

/-! ## Witness: separation on a concrete declaration -/

/-- Witness: registers at offsets `0`/`8` (width `4`) are separate at every
    base, with disjoint cells -- and bank entries `0`/`1` at stride `16` are
    disjoint. No lemma above quantifies over syntax, so the inhabitation
    obligation is vacuous; this is a data-level witness. -/
theorem zelle_zeuge :
    getrennt ⟨0, 4⟩ ⟨8, 4⟩ ∧
    (∀ b a, ¬ (zelle b ⟨0, 4⟩ a ∧ zelle b ⟨8, 4⟩ a)) ∧
    (∀ b a, ¬ (bankzelle b 0 16 0 a ∧ bankzelle b 0 16 1 a)) := by
  refine ⟨by unfold getrennt; decide, ?_, ?_⟩
  · intro b a
    exact trennung_haengt_nicht_an_der_basis _ _ (by unfold getrennt; decide) b a
  · intro b a
    exact bankeintraege_ueberlappen_nicht b 0 16 0 1 (by decide) a

/-! ## Bridge

  `SchablonenT5Sem.lean` §5 ties `device.konstruktor` to the Lean model --
  its MODEL-FACING half only: trace reads preserve memory
  (`device_lese_frame_slots/globs`). The layout arithmetic ported here
  (separate declared layouts meet separate cells for every base; bank
  stride) has NO counterpart there and is skipped precisely: `World.slots`
  is keyed by table, index and field with no base, offset or width, and
  registers live behind `Orakel.regLies`/`regSchreib`. The two files are
  complementary halves of the same template, each naming what the other
  covers. -/

#print axioms Gabbro.Grammatik.Isabelle.DeviceKonstruktor.getrennte_register_treffen_getrennte_zellen
#print axioms Gabbro.Grammatik.Isabelle.DeviceKonstruktor.trennung_haengt_nicht_an_der_basis
#print axioms Gabbro.Grammatik.Isabelle.DeviceKonstruktor.bankeintraege_ueberlappen_nicht
#print axioms Gabbro.Grammatik.Isabelle.DeviceKonstruktor.stride_null_macht_die_bank_leer
#print axioms Gabbro.Grammatik.Isabelle.DeviceKonstruktor.zelle_zeuge

end Gabbro.Grammatik.Isabelle.DeviceKonstruktor
