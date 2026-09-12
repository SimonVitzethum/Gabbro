/-
  File:      Grammatik/Konstanten.lean
  Subject:   COMPILE-TIME CONSTANTS, FIRST CUT (PLAN-BITS.md section 6).

  The checker evaluates total, effect-free const initializers and const
  tables element-wise and prints the values as a certificate: a `List Nat`
  literal plus the defining equation as a `List.all` predicate (encoding N
  of the certificate measurement). This file carries the Lean side: the
  certificate predicate shape and the generic lemma that a closed
  certificate yields every entry's defining equation, with the range proofs
  attached afterwards as the measurement recommends.
-/

namespace Gabbro.Grammatik.Konstanten

/-- Certificate predicate (encoding N): the defining equation `f`
    (index to value to check) over every entry of `t`, through `zipIdx`
    so the equation sees the index. -/
def konstZert (t : List Nat) (f : Nat → Nat → Bool) : Bool :=
  t.zipIdx.all fun p => f p.2 p.1

/-- The empty table is trivially certified. -/
theorem konstZert_nil (f : Nat → Nat → Bool) : konstZert [] f = true :=
  rfl

/-- Membership at an offset: `t[j]? = some v` puts `(v, n + j)` into
    `t.zipIdx n`. The offset generalizes the induction; the public lemma
    below instantiates it at `0`. -/
theorem mem_zipIdx_aux {t : List Nat} {n j v : Nat}
    (hm : t[j]? = some v) : (v, n + j) ∈ t.zipIdx n := by
  induction t generalizing n j with
  | nil => simp at hm
  | cons a rest ih =>
    cases j with
    | zero =>
      simp at hm
      subst hm
      simp [List.zipIdx]
    | succ j =>
      simp at hm
      have hmem := ih (n := n + 1) (j := j) hm
      have heq : n + (j + 1) = (n + 1) + j := by omega
      rw [heq]
      simp [List.zipIdx]
      exact Or.inr hmem

/-- `t[j]? = some v` puts `(v, j)` into `t.zipIdx`. -/
theorem mem_zipIdx_of_getElem? {t : List Nat} {j v : Nat}
    (hm : t[j]? = some v) : (v, j) ∈ t.zipIdx := by
  have h := mem_zipIdx_aux (t := t) (n := 0) (j := j) (v := v) hm
  simpa using h

/-- Generic certificate lemma: a closed certificate yields every entry's
    defining equation. Every premise is used: `h` supplies the closed
    `List.all`, `hm` locates the entry. -/
theorem konstZert_mem {t : List Nat} {f : Nat → Nat → Bool}
    (h : konstZert t f = true) {j v : Nat}
    (hm : t[j]? = some v) : f j v = true := by
  unfold konstZert at h
  rw [List.all_eq_true] at h
  have hmem := mem_zipIdx_of_getElem? hm
  have hfv := h _ hmem
  simpa using hfv

/-- The 64-entry square table: the witness the checker evaluates and
    certifies (`i * i` for `i` in `0 .. 64`). -/
def squares64 : List Nat :=
  [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256,
    289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900,
    961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764,
    1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916,
    3025, 3136, 3249, 3364, 3481, 3600, 3721, 3844, 3969]

/-- The square table satisfies its defining equation, entry by entry,
    closed by `decide` (encoding N). -/
theorem squares64_zert :
    konstZert squares64 (fun i v => v == i * i) = true := by
  decide

/-- Witness for `konstZert_mem`: all premises instantiated jointly at the
    square table -- the table, the equation, the closed certificate, and
    entry 63 (`3969 = 63 * 63`). -/
theorem konstZert_mem_zeuge :
    (fun i v => v == i * i) 63 3969 = true :=
  konstZert_mem squares64_zert (j := 63) (v := 3969) rfl

end Gabbro.Grammatik.Konstanten

/- CUTS: what is not proved.
   - Range attachment afterwards: `konstZert_mem` at
     `f := fun _ v => decide (v < bound)` yields every entry's range fact,
     but that instantiation is not stated as its own theorem here.
   - No statement about the checker's printer: that the printed literal
     equals the evaluated table is trust base at the printer (`crates/
     gabbro-check/src/konstanten.rs`), exactly as booked for every
     certificate channel. The Rust test holds the printed literal against
     `squares64` above, so a drift breaks the build on the Rust side.
   - No block fallback: at 64 entries the single `decide` is far below any
     cliff (the measurement closes 2048 the same way); larger tables
     re-measure before use.
-/

#print axioms Gabbro.Grammatik.Konstanten.konstZert_nil
#print axioms Gabbro.Grammatik.Konstanten.mem_zipIdx_aux
#print axioms Gabbro.Grammatik.Konstanten.mem_zipIdx_of_getElem?
#print axioms Gabbro.Grammatik.Konstanten.konstZert_mem
#print axioms Gabbro.Grammatik.Konstanten.squares64_zert
#print axioms Gabbro.Grammatik.Konstanten.konstZert_mem_zeuge
