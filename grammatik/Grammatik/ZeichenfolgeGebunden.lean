/-
  File:      Grammatik/ZeichenfolgeGebunden.lean
  Subject:   Bounded strings: max length known like integer ranges.

  A bounded string is a character list with a declared maximum length,
  written `string max N` the way `u32` carries `in 0 .. N`. The length
  discipline rhymes with the M101-family range reasoning: a literal has
  a known length, `concat` adds lengths and refuses past the target max,
  indexing is in-range or refused, comparison is lexicographic.

  This file is the VALUE model only (lists with the length invariant).
  The surface since lane 256 round 2: `string max N` parses
  (`TypExpr::Zeichenkette`), the `zeichenfolge.rs` pass holds N453-N455
  (and N465 since fix lane F6) over parameters, results and `let`s, and
  string literals parse since lane 261 (`ExprArt::Kette`, byte count as
  length). Literals and lowering are lane 261's: `emit.rs` writes
  `gabbro_string_N` (one length word plus N bytes, no NUL terminator) and
  `ZeichenfolgeC.lean` states the layout's correspondence.

  Fix lane F6 (review G12 F4/F6) adds the three facts the checker's rules
  rest on, stated over this model and nothing else:
  - `bindex_max_beweist_nichts`: a `string max 8` may be empty, so `k < max`
    proves no index (why `gift/1125` is refused now);
  - `bindex_geschuetzt` / `bindex_mindestlaenge`: a length fact
    `k < blaenge s` (or `n <= blaenge s` with `k < n`) proves the read
    (the guard forms `N454` accepts);
  - `bconcat_max_summe` / `bkopie_max`: the checker's max-sum and
    max-compare rules imply the exact-length operations succeed
    (`N453` and `N455` over-approximate, never under-approximate).
  No theorem here says the Rust pass implements these rules; that link is
  the gifts, not a proof.
-/

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

/-- Witness string `"hi"` at max 8. -/
def z1 : BString 8 := ⟨['h', 'i'], by decide⟩

/-- Witness string `"!"` at max 8. -/
def z2 : BString 8 := ⟨['!'], by decide⟩

/-- Witness strings: the within-max concat `"hi!"` at max 8. -/
def z3 : BString 8 := ⟨['h', 'i', '!'], by decide⟩

/-- A copy into a slot of max `tmax`: the exact length is checked
    against the target max; `none` is the refusal. -/
def bkopie (tmax : Nat) {m : Nat} (s : BString m) : Option (BString tmax) :=
  if h : s.daten.length ≤ tmax then some ⟨s.daten, h⟩ else none

/-- The checker's copy rule (`N455`: source max at most target max) implies
    the exact copy succeeds and keeps the characters. -/
theorem bkopie_max {tmax m : Nat} (s : BString m) (h : m ≤ tmax) :
    ∃ r : BString tmax, bkopie tmax s = some r ∧ r.daten = s.daten := by
  have hl : s.daten.length ≤ tmax := Nat.le_trans s.len_ok h
  exact ⟨⟨s.daten, hl⟩, by simp [bkopie, hl], rfl⟩

/-- A copy into a shorter slot can fail: a full `string max 8` does not fit
    `string max 2`. -/
theorem bkopie_kuerzer_scheitert :
    ∃ s : BString 8, bkopie 2 s = none :=
  ⟨⟨['a', 'b', 'c'], by decide⟩, by decide⟩

/-- The checker's concat rule (`N453`: `m1 + m2 <= tmax`) implies the exact
    concat succeeds with the summed length. -/
theorem bconcat_max_summe {tmax m1 m2 : Nat} (a : BString m1) (b : BString m2)
    (h : m1 + m2 ≤ tmax) :
    ∃ r : BString tmax, bconcat tmax a b = some r ∧
      blaenge r = blaenge a + blaenge b := by
  have hl : (a.daten ++ b.daten).length ≤ tmax := by
    rw [List.length_append]
    exact Nat.le_trans (Nat.add_le_add a.len_ok b.len_ok) h
  refine ⟨⟨_, hl⟩, ?_, ?_⟩
  · unfold bconcat
    rw [dif_pos hl]
  · simp [blaenge, List.length_append]

/-- The max proves no index: a `string max 8` may be empty, and index 7
    (below the max) is then refused. This is why the checker demands a
    length fact, not `k < max` (review G12 F4, `gift/1125`). -/
theorem bindex_max_beweist_nichts :
    ∃ s : BString 8, 7 < 8 ∧ bindex s 7 = none :=
  ⟨⟨[], by decide⟩, by decide, rfl⟩

/-- A length fact proves the read: `k < blaenge s` gives a character
    (the `i < lenof(s)` guard). -/
theorem bindex_geschuetzt {max : Nat} (s : BString max) (k : Nat)
    (h : k < blaenge s) : ∃ c, bindex s k = some c :=
  ⟨s.daten[k], bindex_innen s k h⟩

/-- A lower bound on the length proves every index below it (the
    `lenof(s) > k` / `lenof(s) >= n` guards and `requires`). -/
theorem bindex_mindestlaenge {max : Nat} (s : BString max) (n k : Nat)
    (hn : n ≤ blaenge s) (hk : k < n) : ∃ c, bindex s k = some c :=
  bindex_geschuetzt s k (Nat.lt_of_lt_of_le hk hn)

/-- `bounded_string_zeuge`: every rule on non-empty, distinct strings.
    `"hi" + "!"` at max 8 is `"hi!"` (length 3); the guard `2 < blaenge`
    reads `'!'`; the same index is refused on the empty `string max 8`;
    `"hi!"` copies into max 8 and not into max 2. No conjunct is about
    anything but strings (the earlier reference-machine conjunct was
    decorative, review G12 F6). -/
theorem bounded_string_zeuge :
    ∃ (s3 : BString 8) (leer : BString 8),
      bconcat 8 z1 z2 = some s3 ∧ blaenge s3 = 3 ∧
      2 < blaenge s3 ∧ bindex s3 2 = some '!' ∧
      blaenge leer = 0 ∧ bindex leer 2 = none ∧
      (bkopie 8 s3).isSome = true ∧ bkopie 2 s3 = none ∧
      s3.daten ≠ z1.daten :=
  ⟨z3, ⟨[], by decide⟩, rfl, rfl, by decide, rfl, rfl, rfl, by decide, by decide,
    by decide⟩

end Gabbro.Grammatik

/-! ## CUTS:
  - VALUE MODEL ONLY: `BString max` as a character list with the length
    invariant, plus `bliteral` / `bconcat` / `blaenge` / `bindex` /
    `vergl` / `bvergleiche` / `bkopie` with their length, refusal and
    comparison theorems and the witness `bounded_string_zeuge`.
  - The lowering since lane 261: `emit.rs` writes `gabbro_string_N` and
    `ZeichenfolgeC.lean` states the layout's operation correspondence
    (`clen`, `cindex`, `ckopie`, `cconcat`, `cvergleiche` over the live
    prefix). Since fix lane F6 the index rule demands a length fact
    (`bindex_geschuetzt`), never `k < max` alone (`bindex_max_beweist_nichts`).
  - The max bound (`N486`, `1 ..= 65535`) is the checker's and the
    lowering's decision, not the model's: `BString max` takes any `max`.
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
#print axioms Gabbro.Grammatik.bkopie_max
#print axioms Gabbro.Grammatik.bkopie_kuerzer_scheitert
#print axioms Gabbro.Grammatik.bconcat_max_summe
#print axioms Gabbro.Grammatik.bindex_max_beweist_nichts
#print axioms Gabbro.Grammatik.bindex_geschuetzt
#print axioms Gabbro.Grammatik.bindex_mindestlaenge
#print axioms Gabbro.Grammatik.bounded_string_zeuge
