/-
  File:      Grammatik/ZeichenfolgeGebunden.lean
  Subject:   Bounded strings: max length known like integer ranges.

  A bounded string is a character list with a declared maximum length,
  written `string max N` the way `u32` carries `in 0 .. N`. The length
  discipline rhymes with the M101-family range reasoning: a literal has
  a known length, `concat` adds lengths and refuses past the target max,
  indexing is in-range or refused, comparison is lexicographic.

  This file is the VALUE model only (lists with the length invariant).
  It extends no existing type and changes no existing file. Syntax,
  checker wiring and lowering are explicitly out of scope (see CUTS).
-/
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- A bounded string with declared maximum `max`: the data plus the
    proof that its length fits. An over-long list is not a value --
    it is not constructible, exactly like an out-of-range `Zahl`. -/
structure BString (max : Nat) where
  daten : List Char
  len_ok : daten.length ≤ max

/-- A literal with known length: accepted exactly when it fits `max`.
    `none` is the refusal (the over-max literal has no value). -/
def bliteral (max : Nat) (cs : List Char) : Option (BString max) :=
  if h : cs.length ≤ max then some ⟨cs, h⟩ else none

/-- The length of a bounded string. -/
def blaenge {max : Nat} (s : BString max) : Nat := s.daten.length

/-- A literal that fits reports its length. -/
theorem bliteral_laenge (max : Nat) (cs : List Char) (h : cs.length ≤ max) :
    blaenge (⟨cs, h⟩ : BString max) = cs.length := rfl

/-- `concat`: the length sum is checked against the target max and
    refused beyond it. The result lives at the TARGET max (which may
    differ from either argument max); `none` is the over-max refusal. -/
def bconcat (tmax : Nat) {m1 m2 : Nat} (a : BString m1) (b : BString m2) :
    Option (BString tmax) :=
  if h : (a.daten ++ b.daten).length ≤ tmax then some ⟨_, h⟩ else none

/-- A concat within max reports the summed length. -/
theorem bconcat_laenge (tmax : Nat) {m1 m2 : Nat} (a : BString m1) (b : BString m2)
    (h : (a.daten ++ b.daten).length ≤ tmax) :
    blaenge (⟨_, h⟩ : BString tmax) = a.daten.length + b.daten.length := by
  simp [blaenge, List.length_append]

/-- Bounded indexing (M103-class): in-range or refused. `none` is the
    out-of-range refusal. -/
def bindex {max : Nat} (s : BString max) (i : Nat) : Option Char :=
  s.daten[i]?

/-- An in-range index returns the list element. -/
theorem bindex_innen {max : Nat} (s : BString max) (i : Nat)
    (h : i < s.daten.length) : bindex s i = some (s.daten[i]) := by
  simp [bindex, List.getElem?_eq_getElem h]

/-- An out-of-range index is refused. -/
theorem bindex_aussen {max : Nat} (s : BString max) (i : Nat)
    (h : s.daten.length ≤ i) : bindex s i = none :=
  List.getElem?_eq_none h

/-- Lexicographic comparison on character codes. -/
def vergl : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match compare a.toNat b.toNat with
    | .eq => vergl as bs
    | .lt => .lt
    | .gt => .gt

/-- Comparison of bounded strings. -/
def bvergleiche {m1 m2 : Nat} (a : BString m1) (b : BString m2) : Ordering :=
  vergl a.daten b.daten

/-- A string compares equal to itself. -/
theorem vergl_refl (l : List Char) : vergl l l = .eq := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [vergl]
    have hcmp : compare a.toNat a.toNat = .eq := by simp
    rw [hcmp]
    exact ih

/-- Over-max `concat` is refused: the length sum past the target max
    has no value. This is the planted-defect shape: a proof that claims
    an over-max concat succeeds is red. -/
theorem bconcat_ablehnt (tmax : Nat) {m1 m2 : Nat} (a : BString m1) (b : BString m2)
    (h : tmax < (a.daten ++ b.daten).length) :
    bconcat tmax a b = none := by
  unfold bconcat
  rw [dif_neg (Nat.not_le.mpr h)]

/-- Over-max literals are refused. -/
theorem bliteral_ablehnt (max : Nat) (cs : List Char) (h : max < cs.length) :
    bliteral max cs = none := by
  unfold bliteral
  rw [dif_neg (Nat.not_le.mpr h)]

/-- Witness strings: `"hi"` and `"!"` at max 8. -/
def z1 : BString 8 := ⟨['h', 'i'], by decide⟩

/-- Witness strings: `"hi"` and `"!"` at max 8. -/
def z2 : BString 8 := ⟨['!'], by decide⟩

/-- Witness strings: the within-max concat `"hi!"` at max 8. -/
def z3 : BString 8 := ⟨['h', 'i', '!'], by decide⟩

/-- `bounded_string_zeuge`: a bounded string built (`z1`, `z2`),
    concatenated within max (`bconcat 8 z1 z2 = some z3`, length 3),
    and indexed (`bindex z3 0 = some 'h'`), JOINTLY with the reference
    reached run `MB` whose step changes memory (`refB_schreibt`:
    slot `0 -> 100`). The program side is NON-DEGENERATE: one table
    that the leaf writes and four reached steps. -/
theorem bounded_string_zeuge :
    ∃ (s3 : BString 8) (c : Char) (M : RufMaschineF refD),
      bconcat 8 z1 z2 = some s3 ∧ blaenge s3 = 3 ∧
      bindex s3 0 = some c ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
      M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨z3, 'h', MB, rfl, rfl, rfl, refB_erreicht, refB_schreibt⟩

end Gabbro.Grammatik

/-! ## CUTS:
  - VALUE MODEL ONLY: `BString max` as a character list with the length
    invariant, plus `bliteral` / `bconcat` / `blaenge` / `bindex` /
    `vergl` / `bvergleiche` with their length, refusal and comparison
    theorems and the joint witness `bounded_string_zeuge`.
  - NO syntax: there is no `string max N` declaration form, no literal
    or operator surface in the language. B22 (`SYNTAX.md`) stays
    metadata-only strings (claims/reasons/assumes/asm).
  - NO checker rule: no new N code is measured (N453+ still free,
    gifts 1118+ still free, both verified); the length discipline here
    is specified, not wired into `m1.rs` (lane 224 owns it) or any pass.
  - NO emitter shape: every string-typed value ends at a refusal today;
    the per-shape handoff list is in `MUSE-REPORT-256.md`.
  - NO library text (L4): formatting, parsing and UTF handling stay
    library work per `TODO.md` section 0b.
  - Planted-defect check: `bconcat_ablehnt` / `bliteral_ablehnt` prove
    the refusals, and a claim of an over-max concat success fails red
    (defect probe kept outside the tree, see the report).
-/

#print axioms Gabbro.Grammatik.bliteral_laenge
#print axioms Gabbro.Grammatik.bconcat_laenge
#print axioms Gabbro.Grammatik.bindex_innen
#print axioms Gabbro.Grammatik.bindex_aussen
#print axioms Gabbro.Grammatik.vergl_refl
#print axioms Gabbro.Grammatik.bconcat_ablehnt
#print axioms Gabbro.Grammatik.bliteral_ablehnt
#print axioms Gabbro.Grammatik.bounded_string_zeuge

/-! ## CUTS:
  - Skeleton only: operations (`concat`, `length`, `index`, `compare`)
    and their theorems land next, one definition at a time.
  - No syntax, no checker rule, no emitter shape yet (see the report).
-/
