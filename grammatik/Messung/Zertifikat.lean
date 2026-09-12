/-
  Zertifikat -- compile-time certificate measurement (PLAN-BITS.md section 6).

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
def schranke : Nat := 2 ^ 52

/-- Entry check of encoding N: boolean test on a bare `Nat`. -/
def eintragOkN (e : Nat) : Bool :=
  e < schranke

/-- Certificate predicate of encoding N over a whole table. -/
def zertN (t : List Nat) : Bool :=
  t.all eintragOkN

/-- The empty table is trivially certified. -/
theorem zertN_nil : zertN [] = true := rfl

/-- Eight-entry probe of encoding N, closed by `decide`. -/
example : zertN [0, 1, 2, 3, 4, 5, 6, 7] = true := by decide

/-! CUTS: scaling probes (64/512/2048 entries), encoding Z, and the
  8-block fallback live in scratch files; only the 8-entry probe is
  closed here. -/

#print axioms zertN_nil
