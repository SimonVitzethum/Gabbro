/-
  File:      Grammatik/Niedrig/Uebersetzung/Regime.lean
  Subject:   THE NEUTRAL TRANSLATION REGIME (L6a): levels, per-level bits,
    offset bits, the index/offset split of a virtual address, and the
    one-level split lemma.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; nothing imports these modules except the witness and L6b).
  * `Regime` is neutral: a positive level count, positive per-level index
    bits, and page-offset bits. A virtual address is a `Nat`; `indices`
    splits it little-endian above the offset (the root consumes the lowest
    index chunk), `offsetOf` keeps the page offset.
  * NOT CLAIMED here: the hardware assumption that a translation unit walks
    these tables (`Mmu`); translation caches and flushes; quiescence across
    cores; any tie to the context ledger. Those belong to L6b/L6c.
  * Vocabulary follows `Bausteine/Walk/Abbildung.lean` (`levels`, `index`,
    leaf-at-last-level) without importing it. A later lemma (L6b) connects
    `walk` (in `Tabelle.lean`) to `Walk/visitT` by mapping `Entry.table` and
    `Entry.leaf` to `WalkTree.down` and `WalkTree.leaf` over node storage;
    this package states no such lemma.
  * LEFT OUT: the general reconstruction of an address from its indices and
    offset (about 40 lines with `Nat.pow_add` arithmetic). Only the split of
    ONE level is proved (`one_level_split`, in `div_add_mod` order).
-/
module

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Uebersetzung

/-- A neutral translation regime: positive level count, positive per-level
    index bits, page-offset bits. -/
structure Regime where
  levels : Nat
  levels_pos : 0 < levels
  bits : Nat
  bits_pos : 0 < bits
  offsetBits : Nat

/-- The table size: one index runs over `2 ^ bits` entries. -/
def Regime.tableSize (R : Regime) : Nat :=
  2 ^ R.bits

/-- Every table has a positive size. -/
theorem Regime.tableSize_pos (R : Regime) : 0 < R.tableSize := by
  unfold Regime.tableSize
  exact Nat.two_pow_pos R.bits

/-- The page offset of an address. -/
def Regime.offsetOf (R : Regime) (a : Nat) : Nat :=
  a % 2 ^ R.offsetBits

/-- The address with the offset removed. -/
def Regime.restOf (R : Regime) (a : Nat) : Nat :=
  a / 2 ^ R.offsetBits

/-- The offset is below the page size. -/
theorem Regime.offsetOf_bound (R : Regime) (a : Nat) :
    R.offsetOf a < 2 ^ R.offsetBits := by
  unfold Regime.offsetOf
  exact Nat.mod_lt _ (Nat.two_pow_pos R.offsetBits)

/-- Split one index chunk off, from the low side. -/
def Regime.indicesAux (R : Regime) (n x : Nat) : List Nat :=
  match n with
  | 0 => []
  | n + 1 => (x % 2 ^ R.bits) :: Regime.indicesAux R n (x / 2 ^ R.bits)

/-- The per-level indices of an address, root first, above the offset. -/
def Regime.indices (R : Regime) (a : Nat) : List Nat :=
  R.indicesAux R.levels (a / 2 ^ R.offsetBits)

/-- The split produces one index per level. -/
theorem Regime.indicesAux_length (R : Regime) (n x : Nat) :
    (R.indicesAux n x).length = n := by
  induction n generalizing x with
  | zero =>
    rfl
  | succ n ih =>
    show (R.indicesAux n (x / 2 ^ R.bits)).length + 1 = n + 1
    rw [ih]

/-- The address split has exactly `levels` entries. -/
theorem Regime.indices_length (R : Regime) (a : Nat) :
    (R.indices a).length = R.levels := by
  unfold Regime.indices
  exact R.indicesAux_length R.levels (a / 2 ^ R.offsetBits)

/-- Every split index is below `2 ^ bits`. -/
theorem Regime.indicesAux_bound (R : Regime) (n : Nat) :
    ∀ (x i : Nat), i ∈ R.indicesAux n x → i < 2 ^ R.bits := by
  induction n with
  | zero =>
    intro x i hi
    simp only [Regime.indicesAux] at hi
    cases hi
  | succ n ih =>
    intro x i hi
    simp only [Regime.indicesAux] at hi
    cases hi
    · exact Nat.mod_lt _ (Nat.two_pow_pos R.bits)
    · rename_i hmem
      exact ih (x / 2 ^ R.bits) i hmem

/-- Every address index is below `2 ^ bits`. -/
theorem Regime.indices_bound (R : Regime) (a : Nat) (i : Nat)
    (hi : i ∈ R.indices a) : i < 2 ^ R.bits := by
  unfold Regime.indices at hi
  exact R.indicesAux_bound R.levels (a / 2 ^ R.offsetBits) i hi

/-- The split of ONE level, in `div_add_mod` order. -/
theorem one_level_split (a k : Nat) :
    2 ^ k * (a / 2 ^ k) + a % 2 ^ k = a :=
  Nat.div_add_mod a (2 ^ k)

#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.Regime.indices_length
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.Regime.indices_bound
#print axioms Gabbro.Grammatik.Niedrig.Uebersetzung.one_level_split

end Gabbro.Grammatik.Niedrig.Uebersetzung
