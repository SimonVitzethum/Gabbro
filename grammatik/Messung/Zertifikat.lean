/-
  Certificate -- compile-time certificate measurement (PLAN-BITS.md section 6).

  A four-level page-table walk with 512 entries per level is a table of
  512 * 4 entries, each a Nat in 0 .. 2^52. This file measures how Lean
  checks a certificate "this table is correct":

  (a) encoding N: entries as bare `Nat` literals in a `List Nat`, the
      certificate predicate `List.all` with a `Decidable` instance, closed
      by `decide`; the range proofs attached afterwards by one lemma;
  (b) encoding Z: entries as `Zahl` values carrying their proofs;
  (c) fallback: the certificate cut into 8 blocks, each closed by its own
      `decide`.

  Standalone file: NOT imported by `Grammatik.lean`, so it never slows the
  main build. Scaling probes live in scratch files, not here.
-/
import Grammatik.Typen

namespace Gabbro.Messung.Zertifikat

open Gabbro.Grammatik

/-- Upper bound of a page-table entry: entries lie in `0 .. 2^52`. -/
def bound : Nat := 2 ^ 52

/-- Entry check of encoding N: boolean test on a bare `Nat`. -/
def entryOkN (e : Nat) : Bool :=
  decide (e < bound)

/-- Certificate predicate of encoding N over a whole table. -/
def certN (t : List Nat) : Bool :=
  t.all entryOkN

/-- The empty table is trivially certified. -/
theorem certN_nil : certN [] = true := rfl

/-- Range proofs attached afterwards by one lemma: a closed certificate
    yields every entry's range fact. -/
theorem certN_all_lt {t : List Nat} (h : certN t = true) {e : Nat}
    (hm : e ∈ t) : e < bound := by
  unfold certN at h
  rw [List.all_eq_true] at h
  have he := h e hm
  unfold entryOkN at he
  exact of_decide_eq_true he

/-- Eight-entry probe of encoding N, closed by `decide`. -/
example : certN [0, 1, 2, 3, 4, 5, 6, 7] = true := by decide

/-- Encoding Z: entries as `Zahl` values carrying their proofs. -/
abbrev EntryZ : Type := Zahl 0 ((2 ^ 52 : Nat) - 1)

/-- Encoding Z certificate: every carried value is in range by construction,
    so the check is the trivial fold over the carried proofs. -/
def certZ (t : List EntryZ) : Prop :=
  ∀ e : EntryZ, e ∈ t → 0 ≤ e.n ∧ e.n ≤ (2 ^ 52 : Nat) - 1

/-- Encoding Z tables are correct by their own proofs, entry by entry. -/
theorem certZ_holds (t : List EntryZ) : certZ t := by
  intro e _hm
  exact ⟨e.lo_le, e.le_hi⟩

/-- Fallback: the certificate cut into 8 blocks, each closed by its own
    `decide`. Conjoining the eight block certificates is the whole one. -/
def cert8 (bs : List (List Nat)) : Bool :=
  bs.all certN

/-- Eight separately closed blocks join to the joined table. -/
theorem cert8_flatten (bs : List (List Nat)) (h : cert8 bs = true) :
    certN bs.flatten = true := by
  unfold cert8 certN at *
  rw [List.all_eq_true] at h ⊢
  intro e hm
  rw [List.mem_flatten] at hm
  obtain ⟨b, hb, he⟩ := hm
  have hbb := h b hb
  rw [List.all_eq_true] at hbb
  exact hbb e he

/-! CUTS: scaling probes (64/512/2048 entries) live in scratch files under
  `$TMPDIR/cert`; only the 8-entry probe is closed here. No scaling claim is
  made by this file itself. -/

#print axioms certN_nil
#print axioms certN_all_lt
#print axioms certZ_holds
#print axioms cert8_flatten
