module

public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. `table.indexschranke` (table/count: 370/354 corpus lines).

The generated index type is `{i. i < N}`: it CONTAINS every occupied
slot (`belegt_liegt_im_indextyp`) and every generated chaining write
stays inside it (`schreibstellen_im_typ`). -/

/-- An index is valid for a table of `N` slots. -/
def idxGilt (N i : Nat) : Prop := i < N

/-- Soundness of `table.indexschranke`: the generated index type
    `{i. i < N}` CONTAINS every occupied slot (`hN`: occupancy implies
    the bound, established by `M103`), and every generated chaining
    write site (`hZ`) stays inside it. Both premises are consumed. -/
theorem index_bound_holds (N : Nat) (occupied : Nat → Bool)
    (targets : List Nat)
    (hN : ∀ i, occupied i = true → i < N)
    (hZ : ∀ z ∈ targets, z < N)
    (s : Nat) (hs : occupied s = true) :
    idxGilt N s ∧ ∀ z ∈ targets, idxGilt N z :=
  ⟨hN s hs, hZ⟩

/-! ## 2. `table.absenkung` (same family: the lowering lays out exactly
    `N` slots, so no access of the generated program runs out of the
    array -- `kein_zugriff_laeuft_aus_dem_feld`). -/

/-- Soundness of `table.absenkung`: the emitted array has length `m`
    with `m = N` (`h`: the generator writes `count N` there, held by
    `C001`), so every index below `N` (`hi`, from `M103` via
    `table.indexschranke`) is below `m`. Both premises are consumed. -/
theorem lowering_stays_in_array (N m i : Nat) (h : m = N)
    (hi : i < N) : i < m := by
  omega

/-! ## 3. `option.sonderwert` (option: 90 corpus lines).

UNDER THE PREMISE `N < 2^w`: the special value `N` lies outside the
index domain `0 ..< N`, and the word encoding `None -> N % 2^w`,
`Some i -> i % 2^w` is injective on indices below `N`
(`kodiere_wort_injektiv`). At `N = 2^w` it collapses. -/

/-- The word encoding of an option index. -/
def optWord (N w : Nat) : Option Nat → Nat
  | none => N % 2 ^ w
  | some i => i % 2 ^ w

/-- `None` encodes to `N` when `N` fits the word. -/
theorem optWord_none (N w : Nat) (hN : N < 2 ^ w) :
    optWord N w none = N :=
  Nat.mod_eq_of_lt hN

/-- `Some i` encodes to `i` when `i` is below `N` (hence below `2^w`). -/
theorem optWord_some (N w i : Nat) (hN : N < 2 ^ w) (hi : i < N) :
    optWord N w (some i) = i :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_of_lt hN))

/-- Soundness of `option.sonderwert`: the word encoding is injective on
    `None` + indices below `N`. `hN` fixes the modulus (`M103` range);
    `h1`/`h2` bound the two codes to the index domain; `h` is the code
    equation. All four premises are consumed. -/
theorem option_code_injective (N w : Nat) (hN : N < 2 ^ w)
    (o1 o2 : Option Nat)
    (h1 : ∀ i, o1 = some i → i < N)
    (h2 : ∀ i, o2 = some i → i < N)
    (h : optWord N w o1 = optWord N w o2) : o1 = o2 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some j =>
      have hj := h2 j rfl
      rw [optWord_none N w hN, optWord_some N w j hN hj] at h
      rw [h] at hj
      exact absurd hj (Nat.lt_irrefl j)
  | some i =>
    have hi := h1 i rfl
    cases o2 with
    | none =>
      rw [optWord_some N w i hN hi, optWord_none N w hN] at h
      rw [h] at hi
      exact absurd hi (Nat.lt_irrefl N)
    | some j =>
      have hj := h2 j rfl
      rw [optWord_some N w i hN hi, optWord_some N w j hN hj] at h
      rw [h]

/-! ## 4. `verbund.konstruktor` (record construction: the labelled call).

UNDER `distinct fs`: if the constructor assignment list has exactly the
field list as its key sequence (`map fst zs = fs`, established by
`M106`/`M107` as `deckt`), then every field is set exactly once AND
none is uninitialised -- the two halves coincide (`count = 1`: at
least one by membership, at most one by `Nodup`). Key `Nodup` is the
second conjunct: it is what makes the read-out unambiguous. -/

/-- Soundness of `verbund.konstruktor`. `hdist`/`hdeckt` are the two
    halves of `deckt`; `hf` names the field. All three are consumed. -/
theorem record_ctor_unique (fs : List String) (zs : List (String × Nat))
    (hdist : fs.Nodup) (hdeckt : List.map Prod.fst zs = fs)
    (f : String) (hf : f ∈ fs) :
    List.count f (List.map Prod.fst zs) = 1 ∧
    (List.map Prod.fst zs).Nodup := by
  have hkeys : (List.map Prod.fst zs).Nodup := hdeckt ▸ hdist
  have hmem : f ∈ List.map Prod.fst zs := hdeckt.symm ▸ hf
  have hone : List.count f (List.map Prod.fst zs) = 1 := by
    have hc := List.Nodup.count (a := f) hkeys
    rw [if_pos hmem] at hc
    exact hc
  exact ⟨hone, hkeys⟩

/-! ## 5. `device.konstruktor` (device: 130 corpus lines).

Out of the address arises a typed handle, and the generated accesses
meet the layouts DECLARED in the `device` block (that the declared
layouts are the device's is an axiom-layer ASSUMPTION, not shown here).
What remains is the ARITHMETIC, machine-checked: separate registers
meet separate cells, and that FOR EVERY BASE (`hB`: the base is
universally quantified inside the conclusion, so the handle may be the
constructor); bank entries do not overlap. `N009` establishes `h`
per register pair; `N010` keeps `stride` nonzero. -/

/-- Soundness of `device.konstruktor`: declared-separate layouts
    (`h`: the byte ranges do not overlap) meet separate cells at EVERY
    base `B`. `h` is consumed by the arithmetic. -/
theorem device_cells_separate (off1 sz1 off2 sz2 B : Nat)
    (h : off1 + sz1 ≤ off2 ∨ off2 + sz2 ≤ off1) :
    ∀ x, ¬ (B + off1 ≤ x ∧ x < B + off1 + sz1 ∧
      B + off2 ≤ x ∧ x < B + off2 + sz2) := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  omega

/-- Bank entries do not overlap: cells of width `sz` at stride
    `stride ≥ sz` (`hs`), two distinct entries (`hlt`) lie in disjoint
    ranges. `hs`/`hlt` are both consumed. -/
theorem device_bank_separate (B stride sz k1 k2 : Nat)
    (hs : sz ≤ stride) (hlt : k1 < k2) (x : Nat)
    (h2 : x < B + k1 * stride + sz)
    (h3 : B + k2 * stride ≤ x) : False := by
  have hstep : (k1 + 1) * stride ≤ k2 * stride :=
    Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hlt)
  have hexpand : (k1 + 1) * stride = k1 * stride + stride := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

end Gabbro.Grammatik
