/-
  File:      Grammatik/SchablonenT5.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md).

  What this file is: Lean soundness cores for the templates of
  `crates/gabbro-check/src/schablonen.rs`. All ten machine-checked proofs
  so far are Isabelle (`beweise/*.thy`); NONE of the 21 templates has a
  Lean proof. Every lemma below is proved in Lean 4.33.1 over a small
  abstract model of the template named in its doc comment, and every
  lemma comes with a `NAME_zeuge` that instantiates ALL premises JOINTLY
  on concrete values AND on the non-degenerate reference run
  (`refB_erreicht` + `refB_schreibt`: table `konto` written by
  `einzahlen`, slot `0 -> 100`).

  Order: most-used corpus construct first (measured 2026-09-13 over
  `beispiele/`: table/count 370/354, locks 292, device 130, option 90,
  entry 89, clobbers 80, format 58, transition 34, exchange 31,
  accumulates/mappings 23, consuming 13, group 10, reset 9, restrict 5,
  induction 3, transset 2).
-/

import Grammatik.ReferenzB

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

/-- Witness for `index_bound_holds`: ALL premises instantiated JOINTLY
    on the reference table (`refD.count () = 2`, slot `0` occupied,
    write sites `[0, 1]`), together with the NON-DEGENERATE run
    (`refB_erreicht`: `einzahlen` writes table `konto`;
    `refB_schreibt`: slot `0 -> 100`). -/
theorem index_bound_zeuge :
    (idxGilt ((refD.count ()).toNat) 0 ∧
      ∀ z ∈ ([0, 1] : List Nat), idxGilt ((refD.count ()).toNat) z)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h2 : (refD.count ()).toNat = 2 := rfl
  have hN : ∀ i, (decide (i = 0)) = true → i < (refD.count ()).toNat := by
    intro i hi
    rw [h2]
    have : i = 0 := of_decide_eq_true hi
    omega
  have hZ : ∀ z ∈ ([0, 1] : List Nat), z < (refD.count ()).toNat := by
    intro z hz
    rw [h2]
    simp at hz
    rcases hz with rfl | rfl <;> decide
  exact ⟨index_bound_holds _ _ _ hN hZ 0 rfl, refB_erreicht, refB_schreibt⟩

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

/-- Witness for `lowering_stays_in_array`: the reference table lays out
    `m = 2 = count` slots and slot `0` is inside, jointly with the
    NON-DEGENERATE run (`refB_erreicht`, `refB_schreibt`). -/
theorem lowering_stays_in_array_zeuge :
    (∀ i, i < (refD.count ()).toNat → i < 2)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h2 : (refD.count ()).toNat = 2 := rfl
  have h : 2 = (refD.count ()).toNat := h2.symm
  exact ⟨fun i hi => lowering_stays_in_array _ 2 i h hi,
    refB_erreicht, refB_schreibt⟩

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

/-- Witness for `option_code_injective`: ALL premises instantiated
    JOINTLY at `N = count = 2`, `w = 32` on the NON-DEGENERATE run
    (`refB_erreicht`, `refB_schreibt`). -/
theorem option_code_injective_zeuge :
    (none = (none : Option Nat))
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h2 : (refD.count ()).toNat = 2 := rfl
  have hN : (refD.count ()).toNat < 2 ^ 32 := by rw [h2]; decide
  have h1 : ∀ i, (none : Option Nat) = some i → i < (refD.count ()).toNat := by
    intro i hi
    contradiction
  have h2' : ∀ i, (none : Option Nat) = some i → i < (refD.count ()).toNat := by
    intro i hi
    contradiction
  have h : optWord (refD.count ()).toNat 32 none =
      optWord (refD.count ()).toNat 32 none := rfl
  exact ⟨option_code_injective _ 32 hN none none h1 h2' h,
    refB_erreicht, refB_schreibt⟩

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

/-- Witness for `record_ctor_unique`: fields `["a", "b"]` built once
    each, jointly with the NON-DEGENERATE run. -/
theorem record_ctor_unique_zeuge :
    (List.count "a" (List.map Prod.fst ([("a", 1), ("b", 2)] : List (String × Nat))) = 1 ∧
      (List.map Prod.fst ([("a", 1), ("b", 2)] : List (String × Nat))).Nodup)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hdist : (["a", "b"] : List String).Nodup := by decide
  have hdeckt : List.map Prod.fst ([("a", 1), ("b", 2)] : List (String × Nat)) =
      ["a", "b"] := rfl
  have hf : "a" ∈ (["a", "b"] : List String) := by decide
  exact ⟨record_ctor_unique _ _ hdist hdeckt "a" hf,
    refB_erreicht, refB_schreibt⟩

/-! ## CUTS:
  - Skeleton only: `idxGilt` is defined; all 21 soundness lemmas are open.
-/

#print axioms Gabbro.Grammatik.idxGilt

end Gabbro.Grammatik
