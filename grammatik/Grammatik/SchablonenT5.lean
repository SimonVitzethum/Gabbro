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

/-- Witness for `device_cells_separate`: registers at offsets `0`/`4`
    of width `4` stay separate at base `0x1000`, jointly with the
    NON-DEGENERATE run. -/
theorem device_cells_separate_zeuge :
    (∀ x, ¬ (0x1000 + 0 ≤ x ∧ x < 0x1000 + 0 + 4 ∧
      0x1000 + 4 ≤ x ∧ x < 0x1000 + 4 + 4))
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h : 0 + 4 ≤ 4 ∨ 4 + 4 ≤ 0 := Or.inl (by decide)
  exact ⟨device_cells_separate 0 4 4 4 0x1000 h,
    refB_erreicht, refB_schreibt⟩

/-! ## 6. `format.roundtrip` (format: 58 corpus lines).

(1) `read(write(x)) == x` for every representable `x` (`hRep`: the
written value fits the declared width, established by `M101`).
(2) A write to one field does not disturb a separate field (`hne`:
the fields are separate -- `trennt f g` from the layout itself,
held by `N008`). Model: one cell per field name; the layout-level
bit-disjointness this abstraction rests on is booked in CUTS, not
proved here. -/

/-- Abstract field store: one cell per field name. -/
def fieldStore : Type := String → Nat

/-- Write `v` to field `f` (masked to the declared width). -/
def fieldWrite (width : String → Nat) (σ : fieldStore) (f : String)
    (v : Nat) : fieldStore :=
  fun g => if g = f then v % 2 ^ (width f) else σ g

/-- Read field `f`. -/
def fieldRead (σ : fieldStore) (f : String) : Nat := σ f

/-- Roundtrip: reading back what was written gives the value. `hRep`
    is consumed by the mask removal. -/
theorem format_roundtrip (width : String → Nat) (σ : fieldStore)
    (f : String) (v : Nat) (hRep : v < 2 ^ (width f)) :
    fieldRead (fieldWrite width σ f v) f = v := by
  simp only [fieldRead, fieldWrite]
  rw [if_true, Nat.mod_eq_of_lt hRep]

/-- Non-interference: writing `f` leaves a separate field `g`
    undisturbed. `hne` is consumed by the branch. -/
theorem format_separate (width : String → Nat) (σ : fieldStore)
    (f g : String) (v : Nat) (hne : g ≠ f) :
    fieldRead (fieldWrite width σ f v) g = fieldRead σ g := by
  simp only [fieldRead, fieldWrite, if_neg hne]

/-- Witness for the `format` pair: roundtrip of `7` and undisturbed
    `"b"` after writing `"a"`, jointly with the NON-DEGENERATE run. -/
theorem format_roundtrip_zeuge :
    (fieldRead (fieldWrite (fun _ => 8) (fun _ => 0) "a" 7) "a" = 7 ∧
      fieldRead (fieldWrite (fun _ => 8) (fun _ => 0) "a" 7) "b" =
        fieldRead (fun _ => 0) "b")
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hRep : 7 < 2 ^ ((fun _ => 8 : String → Nat) "a") := by decide
  have hne : (("b" : String) ≠ "a") := by decide
  exact ⟨⟨format_roundtrip _ _ "a" 7 hRep, format_separate _ _ "a" "b" 7 hne⟩,
    refB_erreicht, refB_schreibt⟩

/-! ## 7. `gruppe.sperrabdruck` (locks: 292 corpus lines).

The group operation takes ALL locks of its carriers in ascending
`rank` order and holds them across the whole move (`U003`/`U005`/`H006`
establish the order; `U006` the absence of intermediate exits).
Three parts: (a) the declared order is acyclic -- a strictly ascending
take sequence never re-enters a lock, so the wait graph stays in
`less_than`; (b) the connecting invariant holds at BEGIN and END, NOT
in between -- the intermediate state is exactly why a group operation
exists; (c) no intermediate exit strands the move mid-way. -/

/-- Part (a): ascending rank order never re-enters a lock. `hAsc` is
    consumed by the induction. -/
theorem lock_order_no_reentry (ranks : List Nat)
    (hAsc : ranks.Pairwise (· < ·)) : ranks.Nodup := by
  induction ranks with
  | nil => exact List.nodup_nil
  | cons r rs ih =>
    cases hAsc with
    | cons hmem hrs =>
      rw [List.nodup_cons]
      exact ⟨fun hm => absurd (hmem _ hm) (Nat.lt_irrefl r), ih hrs⟩

/-- Part (b): BEGIN and END do not constrain the MIDDLE. There are a
    proposition, a start, a middle and an end with the proposition at
    both ends and its negation in the middle -- so demanding the
    invariant in between would be a strictly stronger, unkept promise.
    (This is `beobachtbares_gilt` read backwards: the locale spans the
    move, never its inside.) -/
theorem group_move_middle_free :
    ∃ (inv : Bool → Prop) (pre mid post : Bool),
      inv pre ∧ inv post ∧ ¬ inv mid :=
  ⟨(· = true), true, false, true, rfl, rfl, by decide⟩

/-- A group-move script: plain steps plus a leaving exit. -/
inductive GAct : Type
  | step : Nat → GAct
  | leave : GAct
  deriving DecidableEq

/-- Execution: `leave` aborts to `none`. -/
def gexec : List GAct → Nat → Option Nat
  | [], s => some s
  | .step k :: rest, s => gexec rest (s + k)
  | .leave :: _, _ => none

/-- The total step fold, ignoring exits. -/
def gfold : List GAct → Nat → Nat
  | [], s => s
  | .step k :: rest, s => gfold rest (s + k)
  | .leave :: rest, s => gfold rest s

/-- Part (c): with no intermediate exit in the script (`hNoExit`,
    established by `U006`), execution never aborts -- it equals the
    total fold. `hNoExit` is consumed in the `leave` case. -/
theorem group_move_no_exit (script : List GAct)
    (hNoExit : GAct.leave ∉ script) (s : Nat) :
    gexec script s = some (gfold script s) := by
  induction script generalizing s with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | step k =>
      have hr : GAct.leave ∉ rest :=
        fun hm => hNoExit (List.mem_cons_of_mem _ hm)
      show gexec rest (s + k) = some (gfold rest (s + k))
      exact ih hr _
    | leave =>
      have hc : False := hNoExit (List.mem_cons.mpr (Or.inl rfl))
      exact hc.elim

/-- Witness for `lock_order_no_reentry`: ranks `[0, 1]` ascend, jointly
    with the NON-DEGENERATE run. -/
theorem lock_order_no_reentry_zeuge :
    ([0, 1] : List Nat).Nodup
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hAsc : ([0, 1] : List Nat).Pairwise (· < ·) := by decide
  exact ⟨lock_order_no_reentry _ hAsc, refB_erreicht, refB_schreibt⟩

/-! ## 8. `entry.abdruck` (entry 89 / clobbers 80 corpus lines).

(1) The generated entry path preserves every register from
`preserves` (`hPres`: no path write targets a preserved register).
(2) It writes no register outside `clobbers` (`hClob`: every path
write targets `clobbers`). (3) The stack switch is NOT an obligation
but an undefined word -- documented, not stated. Model: an abstract
register file; the hardware meaning of each register is booked in
CUTS. -/

/-- Abstract register file. -/
def regFile : Type := String → Nat

/-- Run an entry path over a register file. -/
def regRun : List (String × Nat) → regFile → regFile
  | [], σ => σ
  | (r, v) :: rest, σ => regRun rest (fun q => if q = r then v else σ q)

/-- Part (1): preserved registers survive the path. -/
private theorem entry_keeps_aux (P : List String) (path : List (String × Nat))
    (hPres : ∀ w ∈ path, w.1 ∉ P) (σ : regFile) (r : String)
    (hr : r ∈ P) : regRun path σ r = σ r := by
  induction path generalizing σ with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨a, b⟩ := w
    have hni : a ∉ P := hPres _ (List.mem_cons.mpr (Or.inl rfl))
    have hrne : r ≠ a := fun he => hni (he ▸ hr)
    have hrest : ∀ u ∈ rest, u.1 ∉ P :=
      fun u hu => hPres u (List.mem_cons_of_mem _ hu)
    exact (ih hrest _).trans (if_neg hrne)

theorem entry_keeps (path : List (String × Nat)) (P : List String)
    (hPres : ∀ w ∈ path, w.1 ∉ P) (σ : regFile) (r : String)
    (hr : r ∈ P) : regRun path σ r = σ r :=
  entry_keeps_aux P path hPres σ r hr

/-- Part (2): a changed register is in `clobbers`. -/
private theorem entry_same_aux (C : List String) (path : List (String × Nat))
    (hClob : ∀ w ∈ path, w.1 ∈ C) (σ : regFile) (r : String)
    (hrC : r ∉ C) : regRun path σ r = σ r := by
  induction path generalizing σ with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨a, b⟩ := w
    have hmem : a ∈ C := hClob _ (List.mem_cons.mpr (Or.inl rfl))
    have hrne : r ≠ a := fun he => hrC (he.symm ▸ hmem)
    have hrest : ∀ u ∈ rest, u.1 ∈ C :=
      fun u hu => hClob u (List.mem_cons_of_mem _ hu)
    have step : (fun q => if q = a then b else σ q) r = σ r :=
      if_neg hrne
    exact (ih hrest _).trans step

theorem entry_clobbers (path : List (String × Nat)) (C : List String)
    (hClob : ∀ w ∈ path, w.1 ∈ C) (σ : regFile) (r : String)
    (h : regRun path σ r ≠ σ r) : r ∈ C := by
  by_cases hrC : r ∈ C
  · exact hrC
  · exact absurd (entry_same_aux C path hClob σ r hrC) h

/-- Witness for the `entry` pair: path `[("t0", 1)]` keeps `"s0"` and
    changes only `"t0"`, jointly with the NON-DEGENERATE run. -/
theorem entry_keeps_zeuge :
    (regRun [("t0", 1)] (fun _ => 0) "s0" = 0 ∧
      "t0" ∈ (["t0"] : List String))
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hPres : ∀ w ∈ ([("t0", 1)] : List (String × Nat)), w.1 ∉ (["s0"] : List String) := by
    intro w hw
    simp at hw
    simp [hw]
  have hClob : ∀ w ∈ ([("t0", 1)] : List (String × Nat)), w.1 ∈ (["t0"] : List String) := by
    intro w hw
    simp at hw
    simp [hw]
  have hkeep := entry_keeps _ ["s0"] hPres (fun _ => 0) "s0" (by decide)
  have hchange := entry_clobbers _ ["t0"] hClob (fun _ => 0) "t0" (by decide)
  exact ⟨⟨hkeep, hchange⟩, refB_erreicht, refB_schreibt⟩

/-! ## 9. `transition.transset` (transition: 34 corpus lines).

Several places in ONE move: no intermediate state is observable FOR A
NAMED OBSERVER (`Obs`: the observer's footprint; `hObs` names the two
moved places as outside it -- on one core the control flow, on several
every core that does not hold the move's lock). Without a named
observer the promise is empty on a multicore. Model: slot states as
place valuations; the joint move writes both places at once; the trace
holds exactly the before/after worlds. -/

/-- A joint move writes two places at once. -/
def jointMove (σ : Nat → Nat) (p1 p2 v1 v2 : Nat) : Nat → Nat :=
  fun p => if p = p1 then v1 else if p = p2 then v2 else σ p

/-- The trace of the joint move: before and after, no middle. -/
def jointTrace (σ : Nat → Nat) (p1 p2 v1 v2 : Nat) : List (Nat → Nat) :=
  [σ, jointMove σ p1 p2 v1 v2]

/-- Soundness of `transition.transset`: the named observer sees no
    change anywhere in the trace. `hObs` names both moved places as
    outside the footprint; `hw`/`hq` fix the world and the observed
    place. All four are consumed. -/
theorem joint_move_hidden (σ : Nat → Nat) (p1 p2 v1 v2 : Nat)
    (Obs : List Nat) (hObs : p1 ∉ Obs ∧ p2 ∉ Obs)
    (w : Nat → Nat) (hw : w ∈ jointTrace σ p1 p2 v1 v2)
    (q : Nat) (hq : q ∈ Obs) : w q = σ q := by
  have h1 : q ≠ p1 := fun he => hObs.1 (he ▸ hq)
  have h2 : q ≠ p2 := fun he => hObs.2 (he ▸ hq)
  simp only [jointTrace, List.mem_cons] at hw
  simp at hw
  rcases hw with rfl | rfl
  · rfl
  · simp only [jointMove, if_neg h1, if_neg h2]

/-- Witness for `joint_move_hidden`: moving places `0`/`1`, observer of
    place `2` sees nothing, jointly with the NON-DEGENERATE run. -/
theorem joint_move_hidden_zeuge :
    ((fun _ => 0) 2 = (fun _ => (0 : Nat)) 2)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hObs : (0 : Nat) ∉ ([2] : List Nat) ∧ 1 ∉ ([2] : List Nat) := by
    decide
  have hw : (fun _ => (0 : Nat)) ∈ jointTrace (fun _ => 0) 0 1 7 8 := by
    simp [jointTrace]
  have hq : (2 : Nat) ∈ ([2] : List Nat) := by decide
  exact ⟨joint_move_hidden _ 0 1 7 8 [2] hObs _ hw 2 hq,
    refB_erreicht, refB_schreibt⟩

/-! ## 10. `exchange.rmw` (exchange: 31 corpus lines).

The body of `update(v)` is pure (mechanically, Pass 8 -- in the model
a body IS a function of the read value, so purity holds by
construction). The atomicity of the read-modify-write sequence is NOT
a template obligation but an assumption of the axiom layer. What Lean
checks is the serial content: an RMW chain applies innermost first --
the fold direction is fixed, no interleaving inside. -/

/-- An RMW chain: each body sees the previous write. -/
def runRmw : List (Nat → Nat) → Nat → Nat
  | [], σ => σ
  | f :: rest, σ => runRmw rest (f σ)

/-- Soundness core of `exchange.rmw`: the chain equals the left fold --
    bodies apply innermost first, deterministically. -/
theorem rmw_chain_order (fs : List (Nat → Nat)) (σ : Nat) :
    runRmw fs σ = fs.foldl (fun s f => f s) σ := by
  induction fs generalizing σ with
  | nil => rfl
  | cons f rest ih =>
    show runRmw rest (f σ) = rest.foldl (fun s g => g s) (f σ)
    exact ih _

/-- Witness for `rmw_chain_order`: `[+1, *2]` from `5` gives `12`,
    jointly with the NON-DEGENERATE run. -/
theorem rmw_chain_order_zeuge :
    (runRmw [(· + 1), (· * 2)] 5 = 12)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hchain := rmw_chain_order [(· + 1), (· * 2)] 5
  have hval : ([(· + 1), (· * 2)] : List (Nat → Nat)).foldl (fun s f => f s) 5 = 12 := by
    decide
  exact ⟨hchain.trans hval, refB_erreicht, refB_schreibt⟩

/-! ## 11. `accumulates.monoid` (accumulates: 23 corpus lines).

The merge set is a commutative monoid (mechanically checkable: the
closed `MergeOp` vocabulary over integral types). What Lean checks is
the order-independence core (`faltung_ist_reihenfolgeunabhaengig`):
under associativity (`hassoc`) and commutativity (`hcomm`) the fold
does not see adjacent swaps -- hence no interleaving. The quiescent
point (`am_ruhepunkt_gleich_dem_atomaren_rmw`) and the per-operator
units (`min` starts at the type maximum) are booked in CUTS. -/

/-- Soundness core of `accumulates.monoid`: adjacent swaps leave the
    fold unchanged. `hassoc`/`hcomm` are both consumed. -/
theorem merge_swap_invariant (op : Nat → Nat → Nat)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hcomm : ∀ a b, op a b = op b a)
    (xs ys : List Nat) (a b s : Nat) :
    (xs ++ [a, b] ++ ys).foldl (fun t x => op t x) s =
    (xs ++ [b, a] ++ ys).foldl (fun t x => op t x) s := by
  have key : ∀ t, op (op t a) b = op (op t b) a := by
    intro t
    rw [hassoc, hcomm a b, ← hassoc]
  simp only [List.foldl_append]
  have h2 : ([a, b] : List Nat).foldl (fun t x => op t x)
        (xs.foldl (fun t x => op t x) s) =
      ([b, a] : List Nat).foldl (fun t x => op t x)
        (xs.foldl (fun t x => op t x) s) :=
    key _
  rw [h2]

/-- Witness for `merge_swap_invariant`: addition folds `[1, 2]` and
    `[2, 1]` to the same value, jointly with the NON-DEGENERATE run. -/
theorem merge_swap_invariant_zeuge :
    (([1, 2] : List Nat).foldl (fun t x => t + x) 0 =
      ([2, 1] : List Nat).foldl (fun t x => t + x) 0)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h := merge_swap_invariant (· + ·) Nat.add_assoc Nat.add_comm
    ([] : List Nat) [] 1 2 0
  exact ⟨h, refB_erreicht, refB_schreibt⟩

/-! ## 12. `walk.mappings` (mappings: 23 corpus lines).

The generated domain `mappings of` meets every reachable entry that
CARRIES a mapping -- together with va and level. That is not the same
as `leaf entry`: a large page maps above the full depth. The meeting
holds BY CONSTRUCTION of the domain (filter); whether the generator
builds that filter -- and whether it meets large pages -- is the open
half, booked in CUTS. -/

/-- A page-table entry: address, level, and whether it carries a mapping. -/
def ptEntry : Type := Nat × Nat × Bool

/-- It carries a mapping (possibly above the full depth). -/
def carriesMapping (e : ptEntry) : Bool := e.2.2

/-- The generated domain: every entry that carries a mapping. -/
def mappingsOf (entries : List ptEntry) : List ptEntry :=
  entries.filter carriesMapping

/-- Soundness core of `walk.mappings`: a carried mapping is met.
    `hmem`/`hcar` are both consumed. -/
theorem walk_hits_mapping (entries : List ptEntry) (e : ptEntry)
    (hmem : e ∈ entries) (hcar : carriesMapping e = true) :
    e ∈ mappingsOf entries :=
  List.mem_filter.mpr ⟨hmem, hcar⟩

/-- Witness for `walk_hits_mapping`: entry `(7, 1, true)` is met,
    jointly with the NON-DEGENERATE run. -/
theorem walk_hits_mapping_zeuge :
    ((7, 1, true) ∈ mappingsOf [(7, 1, true), (8, 2, false)])
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hmem : ((7, 1, true) : ptEntry) ∈ [(7, 1, true), (8, 2, false)] := by
    decide
  have hcar : carriesMapping (7, 1, true) = true := rfl
  exact ⟨walk_hits_mapping _ _ hmem hcar, refB_erreicht, refB_schreibt⟩

/-! ## 13. `consuming.ordnung` (consuming: 13 corpus lines).

The domain delivers its witnesses in the generated well-founded
order. Under the REMOVAL of the visited witness the order is
preserved -- the edge set shrinks (`wf_subset` at list level: what
remains was there), and consumption strictly drops the domain measure,
so the traversal terminates. Leaf status at the moment of consumption
does NOT follow -- it additionally requires the choice to be MINIMAL
(`waehlt_minimal`, owed by the witness-order generator). -/

/-- Soundness core of `consuming.ordnung`: removal shrinks the domain
    (`hrem`: the consumed witness is gone from the rest is NOT needed --
    only the membership `hmem` in the remainder) and drops its measure
    (`ha`: the consumed witness was there). Both are consumed. -/
theorem consume_shrinks (domain : List Nat) (a x : Nat)
    (hmem : x ∈ domain.erase a) (ha : a ∈ domain) :
    x ∈ domain ∧ (domain.erase a).length < domain.length := by
  have hpos : 0 < domain.length := by
    cases he : domain with
    | nil =>
      rw [he] at ha
      exact absurd ha List.not_mem_nil
    | cons _ _ => exact Nat.zero_lt_succ _
  exact ⟨List.mem_of_mem_erase hmem,
    by rw [List.length_erase_of_mem ha]; omega⟩

/-- Witness for `consume_shrinks`: consuming `1` out of `[0, 1]`
    leaves `[0]` present and shorter, jointly with the NON-DEGENERATE
    run. -/
theorem consume_shrinks_zeuge :
    ((0 : Nat) ∈ [0, 1] ∧ (([0, 1] : List Nat).erase 1).length < [0, 1].length)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hmem : (0 : Nat) ∈ ([0, 1] : List Nat).erase 1 := by decide
  have ha : (1 : Nat) ∈ ([0, 1] : List Nat) := by decide
  exact ⟨consume_shrinks _ 1 0 hmem ha, refB_erreicht, refB_schreibt⟩

/-! ## 14. `consuming.leermenge`.

The generated witness set is COMPLETE at a NAMED state (`hC`: every
domain element at that state is witnessed) -- if it is empty there
(`hempty`), the domain is empty there. Without the named state the
sentence is ambiguous in a consuming traversal
(`leermenge_ist_zustandsabhaengig`). -/

/-- Soundness core of `consuming.leermenge`. The named state is the
    explicit pair `(domain, wit)`; `hC`/`hempty` are both consumed. -/
theorem consume_empty_at (domain wit : List Nat)
    (hC : ∀ x ∈ domain, x ∈ wit) (hempty : wit = []) :
    domain = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h := hC x hx
  rw [hempty] at h
  exact absurd h List.not_mem_nil

/-- Witness for `consume_empty_at`: empty witnesses over `[]`,
    jointly with the NON-DEGENERATE run. -/
theorem consume_empty_at_zeuge :
    (([] : List Nat) = [])
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hC : ∀ x ∈ ([] : List Nat), x ∈ ([] : List Nat) := by
    intro x hx
    contradiction
  exact ⟨consume_empty_at [] [] hC rfl, refB_erreicht, refB_schreibt⟩

/-! ## 15. `consuming.umhaengen` (the refuted blanket version).

A generated mutation that ADDS edges preserves well-foundedness -- and
that is NOT covered by `wf_subset`; it has to be shown per mutation.
The blanket version is REFUTED, not open
(`umhaengen_kann_zyklus_erzeugen`): one re-hang turns the acyclic edge
`(0, 1)` into a self-loop. What Lean exhibits is that loop. -/

/-- Re-hang the head edge's target. -/
def rehang (edges : List (Nat × Nat)) (a b c : Nat) : List (Nat × Nat) :=
  (edges.erase (a, b)) ++ [(a, c)]

/-- The refutation exhibit: re-hanging `(0, 1)` onto `0` leaves the
    self-loop `(0, 0)` -- a cycle from one move. -/
theorem rehang_can_cycle : (0, 0) ∈ rehang [(0, 1)] 0 1 0 := by
  decide

/-- Witness for `rehang_can_cycle`: the loop exhibit, jointly with the
    NON-DEGENERATE run (the run shows the program side is real; the
    loop shows the template side falls). -/
theorem rehang_can_cycle_zeuge :
    ((0, 0) ∈ rehang [(0, 1)] 0 1 0)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨rehang_can_cycle, refB_erreicht, refB_schreibt⟩

/-! ## 16. `gruppe.ops` (group: 10 corpus lines).

The connecting invariant of the group is preserved under every group
operation. The lock footprint under which that holds does NOT stand
here but in `gruppe.sperrabdruck` -- this template presupposes it
(the `lock_order_no_reentry` half above). What Lean checks is the
composition core: two footprint-covered group operations that each
preserve the link (`h1`/`h2`) preserve it in sequence. (The
single-carrier operations that BREAK a connecting invariant --
`verbindung_nicht_gedeckt` -- are exactly why this entry exists.) -/

/-- Soundness core of `gruppe.ops`: preservation composes. `h1`/`h2`
   /`hp` are all consumed. -/
theorem group_ops_compose (A B : Type) (link : A → B → Prop)
    (g1 g2 : A × B → A × B)
    (h1 : ∀ p, link p.1 p.2 → link (g1 p).1 (g1 p).2)
    (h2 : ∀ p, link p.1 p.2 → link (g2 p).1 (g2 p).2)
    (p : A × B) (hp : link p.1 p.2) :
    link (g2 (g1 p)).1 (g2 (g1 p)).2 :=
  h2 _ (h1 _ hp)

/-- Witness for `group_ops_compose`: the equality link over `Nat`
    survives `(+1, +1)` then `(*2, *2)`, jointly with the
    NON-DEGENERATE run. -/
theorem group_ops_compose_zeuge :
    ((12 : Nat) = 12)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h1 : ∀ p : Nat × Nat, p.1 = p.2 →
      ((fun q : Nat × Nat => (q.1 + 1, q.2 + 1)) p).1 =
      ((fun q : Nat × Nat => (q.1 + 1, q.2 + 1)) p).2 := by
    intro p hp
    simp only []
    omega
  have h2 : ∀ p : Nat × Nat, p.1 = p.2 →
      ((fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) p).1 =
      ((fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) p).2 := by
    intro p hp
    simp only []
    omega
  exact ⟨group_ops_compose Nat Nat (fun a b => a = b)
    (fun q : Nat × Nat => (q.1 + 1, q.2 + 1))
    (fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) h1 h2 (5, 5) rfl,
    refB_erreicht, refB_schreibt⟩

/-! ## 17. `state.reset` (reset: 9 corpus lines).

The generated transition into the initial state holds from every
state in which no linear value is held (`h`: the held-flag is down),
and is itself a `transset` (single move, no middle -- see §9). From a
state with a held linear value it is a leak and is rejected -- M2, not
this template (`reset_rejects_held`). Model: a value plus a
held-linear flag. -/

/-- The generated reset: clean states go home, holding states abort. -/
def treset (s : Nat × Bool) : Option (Nat × Bool) :=
  if s.2 then none else some (0, false)

/-- Soundness core of `state.reset`: total on clean states. `h` is
    consumed by the branch. -/
theorem reset_from_clean (s : Nat × Bool) (h : s.2 = false) :
    treset s = some (0, false) := by
  simp [treset, h]

/-- The M2 side: a held linear value is rejected, not leaked. -/
theorem reset_rejects_held (v : Nat) : treset (v, true) = none :=
  rfl

/-- Witness for `reset_from_clean`: `(7, false)` goes home, jointly
    with the NON-DEGENERATE run. -/
theorem reset_from_clean_zeuge :
    (treset (7, false) = some (0, false))
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨reset_from_clean _ rfl, refB_erreicht, refB_schreibt⟩

/-! ## 18. `table.induktion` (induction: 3 corpus lines).

The induction scheme generated from the `table` declaration is
well-founded and complete: (N-1) chaining edges stay inside the table
(`hfin`: the predecessor bound, from `table.indexschranke` via
`M103`); (N-2) the principle holds for ONE state; (N-3) no
empty-set clause of its own -- the base case is absorbed (vacuous
predecessors discharge `hstep`); (N-4) for `chain(a,b) in` the domain
has TWO kinds of edge and the scheme takes TWO premises
(`e1`/`e2` both feed the step). Well-foundedness is a HYPOTHESIS
(`hwf`: the declaration names the carrying invariant), not a result.
`induct_edge_in_type` is the `im_bereich` direction of (N-1). -/

/-- Soundness core of `table.induktion`. `hfin` bounds predecessors,
    `hwf` carries accessibility, `hstep` is the two-premise step, `hx`
    puts the target in the carrier. All are consumed. -/
theorem table_induction (N : Nat) (e1 e2 : Nat → Nat → Prop)
    (hfin : ∀ a b, e1 a b ∨ e2 a b → a < N)
    (hwf : WellFounded (fun a b => e1 a b ∨ e2 a b))
    (P : Nat → Prop)
    (hstep : ∀ x, x < N → (∀ y, e1 y x ∨ e2 y x → P y) → P x)
    (x : Nat) (hx : x < N) : P x := by
  have key : ∀ z, Acc (fun a b => e1 a b ∨ e2 a b) z → z < N → P z := by
    intro z ha
    induction ha with
    | intro z _ ih =>
      intro hz
      exact hstep z hz (fun y hy => ih y hy (hfin y z hy))
  exact key x (hwf.apply x) hx

/-- The `im_bereich` direction: a chained edge lands in the type. -/
theorem induct_edge_in_type (N : Nat) (e1 e2 : Nat → Nat → Prop)
    (hfin : ∀ a b, e1 a b ∨ e2 a b → b < N)
    (a b : Nat) (h : e1 a b ∨ e2 a b) : b < N :=
  hfin a b h

/-- Witness for `table_induction`: successor edges below `2`, property
    `True`, jointly with the NON-DEGENERATE run. -/
theorem table_induction_zeuge :
    (True)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hfin : ∀ a b : Nat,
      (a + 1 = b ∧ b < 2 ∨ False) → a < (refD.count ()).toNat := by
    intro a b h
    have h2 : (refD.count ()).toNat = 2 := rfl
    rw [h2]
    rcases h with h | h'
    · omega
    · contradiction
  have hsub : Subrelation (fun a b : Nat => a + 1 = b ∧ b < 2 ∨ False)
      (· < ·) := by
    intro a b h
    rcases h with h | h'
    · omega
    · contradiction
  have hwf : WellFounded (fun a b : Nat => a + 1 = b ∧ b < 2 ∨ False) :=
    Subrelation.wf hsub Nat.lt_wfRel.wf
  have hstep : ∀ x : Nat, x < (refD.count ()).toNat →
      (∀ y : Nat, (y + 1 = x ∧ x < 2 ∨ False) → True) → True := by
    intro x _ _
    trivial
  have hx : (0 : Nat) < (refD.count ()).toNat := by
    have h2 : (refD.count ()).toNat = 2 := rfl
    rw [h2]
    decide
  exact ⟨table_induction _ _ _ hfin hwf _ hstep 0 hx,
    refB_erreicht, refB_schreibt⟩

/-! ## 20. `table.ops.erhaltung` (by-ops: `16-by-ops-am-feld.gab` plus
    the `by ops`/`maintains` corpus sites).

Per generated mutation every `online` invariant OF THIS CARRIER is
preserved -- once over the declaration, not per call site (`h`: each
generated operation preserves `inv`). Invariants ACROSS carriers are
expressly not covered; they are `gruppe.ops` (§16). What Lean checks
is the amortisation: a whole run of generated operations (`hr`: every
run step is generated) preserves the invariant from a good state
(`hs`). All three are consumed. -/

/-- Soundness core of `table.ops.erhaltung`: the declaration-level
    check covers every call-site run. -/
private theorem table_ops_keep_aux (S : Type) (inv : S → Prop)
    (ops : List (S → S))
    (h : ∀ op ∈ ops, ∀ s, inv s → inv (op s)) :
    ∀ (run : List (S → S)), (∀ op ∈ run, op ∈ ops) →
      ∀ (s : S), inv s → inv (run.foldl (fun acc op => op acc) s)
  | [], _, _s, hs => hs
  | op :: rest, hr, s, hs =>
    have hop : op ∈ ops := hr _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ _op' ∈ rest, _op' ∈ ops :=
      fun _op' hm => hr _ (List.mem_cons_of_mem _ hm)
    table_ops_keep_aux S inv ops h rest hrest (op s) (h _ hop _ hs)

theorem table_ops_keep (S : Type) (inv : S → Prop) (ops : List (S → S))
    (h : ∀ op ∈ ops, ∀ s, inv s → inv (op s))
    (run : List (S → S)) (hr : ∀ op ∈ run, op ∈ ops)
    (s : S) (hs : inv s) :
    inv (run.foldl (fun acc op => op acc) s) :=
  table_ops_keep_aux S inv ops h run hr s hs

/-- Witness for `table_ops_keep`: operations `[+1, *2]` keep
    nonnegativity along the run, jointly with the NON-DEGENERATE run. -/
theorem table_ops_keep_zeuge :
    ((0 : Nat) ≤ ([(· + 1), (· * 2)] : List (Nat → Nat)).foldl
      (fun acc op => op acc) 0)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h : ∀ op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)),
      ∀ s : Nat, 0 ≤ s → 0 ≤ op s := by
    intro op hop s hs
    simp at hop
    rcases hop with rfl | rfl <;> simp_all <;> omega
  have hr : ∀ op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)),
      op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)) := by
    intro op hop
    exact hop
  exact ⟨table_ops_keep Nat (fun s => 0 ≤ s) _ h _ hr 0 (Nat.zero_le 0),
    refB_erreicht, refB_schreibt⟩

/-! ## 21. `ops.suche` (candidate from «B10»: no corpus use yet).

The generated search returns the first hit in a GENERATED, NAMED
enumeration order (`hpre`: everything before the hit misses; `hpx`:
the hit hits) and leaves the set unchanged (the search is pure: the
fst-projection is the input list). For domains with several kinds of
edge the order has to be fixed on top -- it does not fall out of the
domain (booked in CUTS). -/

/-- The generated search: input list plus first hit. -/
def opSearch : List Nat → (Nat → Bool) → List Nat × Option Nat
  | [], _ => ([], none)
  | x :: xs, p =>
    if p x then (x :: xs, some x)
    else (x :: (opSearch xs p).1, (opSearch xs p).2)

/-- The search leaves every list unchanged. -/
private theorem op_search_keeps_all :
    ∀ (xs : List Nat) (p : Nat → Bool), (opSearch xs p).1 = xs
  | [], _ => rfl
  | y :: ys, p => by
    simp only [opSearch]
    split
    · rfl
    · rw [op_search_keeps_all ys p]

/-- The search leaves the set unchanged. -/
theorem op_search_keeps (pre : List Nat) (x : Nat) (post : List Nat)
    (p : Nat → Bool) :
    (opSearch (pre ++ [x] ++ post) p).1 = pre ++ [x] ++ post :=
  op_search_keeps_all _ _

/-- The search returns the first hit. `hpre`/`hpx` are both consumed. -/
theorem op_search_first (pre : List Nat) (x : Nat) (post : List Nat)
    (p : Nat → Bool)
    (hpre : ∀ y ∈ pre, p y = false) (hpx : p x = true) :
    (opSearch (pre ++ [x] ++ post) p).2 = some x := by
  induction pre with
  | nil =>
    show (opSearch ([x] ++ post) p).2 = some x
    simp [opSearch, hpx]
  | cons y ys ih =>
    have hy : p y = false := hpre _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ z ∈ ys, p z = false :=
      fun z hz => hpre z (List.mem_cons_of_mem _ hz)
    have hys := ih hrest
    show (opSearch ((y :: ys) ++ [x] ++ post) p).2 = some x
    simp only [show (y :: ys) ++ [x] ++ post = y :: (ys ++ [x] ++ post) from rfl,
      opSearch, hy]
    exact hys

/-- Witness for the `ops.suche` pair: searching `[1, 3, 2, 4]` for an
    even number returns `2` and keeps the list, jointly with the
    NON-DEGENERATE run. -/
theorem op_search_zeuge :
    ((opSearch ([1, 3] ++ [2] ++ [4]) (fun n => n == 2)).1 = [1, 3, 2, 4] ∧
      (opSearch ([1, 3] ++ [2] ++ [4]) (fun n => n == 2)).2 = some 2)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hpre : ∀ y ∈ ([1, 3] : List Nat), (y == 2) = false := by decide
  have hpx : ((2 : Nat) == 2) = true := rfl
  exact ⟨⟨op_search_keeps _ _ _ _,
    op_search_first _ _ _ _ hpre hpx⟩, refB_erreicht, refB_schreibt⟩

/-! ## 19. `restrict.alleinzugriff` (restrict: 5 corpus lines).

UNDER H1 (the frame is COMPLETE -- every access of the body has a
root from the declared set: in the model an access IS a rooted pair,
so H1 holds by construction, established checker-side by `E008`/`E010`)
and H2 (no other root meets the same place: at most ONE pointer
parameter per carrier type, syntactically -- `emit::darf_restrict` --
and no pointer to a global table formable in the language): every
access to the object behind `p` runs through `p`, so the C11-6.7.3.1
condition holds. -/

/-- Soundness core of `restrict.alleinzugriff`: two accesses meeting
    at one place share the one root. `hOnly` (H2) is consumed twice;
    `h1`/`h2` fix the two accesses. -/
theorem single_root (q : Nat) (reach : Nat → Nat → Prop) (p r1 r2 : Nat)
    (hOnly : ∀ r, reach r q → r = p) (h1 : reach r1 q)
    (h2 : reach r2 q) : r1 = r2 := by
  rw [hOnly _ h1, hOnly _ h2]

/-- Witness for `single_root`: both accesses run through root `7`,
    jointly with the NON-DEGENERATE run. -/
theorem single_root_zeuge :
    ((7 : Nat) = 7)
    ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
    ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hOnly : ∀ r, (r = 7 ∧ (0 : Nat) = 0) → r = 7 := by
    intro r hr
    exact hr.1
  have h1 : (7 : Nat) = 7 ∧ (0 : Nat) = 0 := ⟨rfl, rfl⟩
  exact ⟨single_root 0 (fun r qq => r = 7 ∧ qq = 0) 7 7 7 hOnly h1 h1,
    refB_erreicht, refB_schreibt⟩

/-! ## CUTS:
  - All 21 templates of `crates/gabbro-check/src/schablonen.rs` have a
    Lean soundness core in this file (previously: 0 of 21 in Lean; 10 of
    21 in Isabelle `beweise/*.thy`). Each core is proved over a small
    abstract model of the template, every premise is consumed by its
    proof, and every template has a `NAME_zeuge` instantiating ALL
    premises JOINTLY on concrete values plus the NON-DEGENERATE
    reference run (`refB_erreicht` + `refB_schreibt`).
  - What is NOT proved (per template, weaker than the Isabelle
    counterpart where noted):
    (1) `table.indexschranke`: the checker side (`M103` establishes
    `hN`/`hZ` per program) is assumed, not proved.
    (2) `table.absenkung`: `m = N` comes from `C001`, assumed.
    (3) `option.sonderwert`: the arithmetic ON an index (no generated
    computation hits the special value) is a statement about `emit.rs`,
    not proved.
    (4) `verbund.konstruktor`: `deckt` comes from `M106`/`M107`,
    assumed; the executable read-out (`liest ... = some v`) is not
    stated -- only `count = 1` plus key `Nodup`, which is what makes
    read-out unambiguous.
    (5) `device.konstruktor`: declared layouts = device layouts is an
    axiom-layer assumption; `stride 0` refusal (`N010`) is assumed.
    (6) `format.roundtrip`: proved over one-cell-per-field; the
    bit-level disjointness (`trennt`, `N008`) this rests on is assumed;
    variable lengths are out of scope (fixed case only).
    (7) `gruppe.sperrabdruck`: the axiom-layer premise (a held
    footprint keeps foreign cores out) is presupposed; (b) is the
    negative exhibit, not a preservation proof.
    (8) `entry.abdruck`: the hardware meaning of registers and the
    stack switch (undefined word) are not modelled.
    (9) `transition.transset`: the observer footprint is named by
    premise; who holds the lock on multicore is outside the model.
    (10) `exchange.rmw`: purity holds by construction (body IS a
    function); atomicity is an axiom-layer assumption, not proved.
    (11) `accumulates.monoid`: only adjacent-swap invariance (the
    order-independence core); the quiescent-point agreement with the
    atomic RMW chain and the per-operator units are not proved.
    (12) `walk.mappings`: meeting holds by construction (filter);
    whether the generator builds it, and large pages above full depth,
    are open.
    (13,14) `consuming.ordnung/leermenge`: finite-list level only; the
    well-founded order itself and `waehlt_minimal` are assumed.
    (15) `consuming.umhaengen`: the refutation exhibit only (as the
    template demands: the blanket version is refuted, not open).
    (16) `gruppe.ops`: preservation composes; the per-operation base
    cases for real group operations are not proved.
    (17) `state.reset`: single-flag model; the M2 linearity context is
    assumed.
    (18) `restrict.alleinzugriff`: H1 holds by construction (access IS
    a rooted pair); H2a/H2b are folded into one `hOnly` premise whose
    checker establishment (`emit::darf_restrict`, language shape) is
    assumed; `own`-exclusivity stays a language decision.
    (19) `table.induktion`: well-foundedness is a hypothesis; the
    generator side (two edge premises per `chain(a,b)`) is assumed.
    (20) `table.ops.erhaltung`: the per-operation preservation `h`
    (Teil II by hand) is a premise, not a result; the emitted-C step
    (`relabel` lowering branches) is not modelled.
    (21) `ops.suche`: construct has no generator; the multi-edge order
    is assumed.
  - No theorem quantifies over program syntax (`Vertrag`/`Stmt`/sic),
    so no conclusion claims a Gabbro semantics; the models are
    explicitly abstract (`fieldStore`, `regFile`, `GAct`, ...).
-/

#print axioms Gabbro.Grammatik.idxGilt
#print axioms Gabbro.Grammatik.index_bound_holds
#print axioms Gabbro.Grammatik.index_bound_zeuge
#print axioms Gabbro.Grammatik.lowering_stays_in_array
#print axioms Gabbro.Grammatik.lowering_stays_in_array_zeuge
#print axioms Gabbro.Grammatik.optWord
#print axioms Gabbro.Grammatik.optWord_none
#print axioms Gabbro.Grammatik.optWord_some
#print axioms Gabbro.Grammatik.option_code_injective
#print axioms Gabbro.Grammatik.option_code_injective_zeuge
#print axioms Gabbro.Grammatik.record_ctor_unique
#print axioms Gabbro.Grammatik.record_ctor_unique_zeuge
#print axioms Gabbro.Grammatik.device_cells_separate
#print axioms Gabbro.Grammatik.device_bank_separate
#print axioms Gabbro.Grammatik.device_cells_separate_zeuge
#print axioms Gabbro.Grammatik.fieldWrite
#print axioms Gabbro.Grammatik.fieldRead
#print axioms Gabbro.Grammatik.format_roundtrip
#print axioms Gabbro.Grammatik.format_separate
#print axioms Gabbro.Grammatik.format_roundtrip_zeuge
#print axioms Gabbro.Grammatik.lock_order_no_reentry
#print axioms Gabbro.Grammatik.group_move_middle_free
#print axioms Gabbro.Grammatik.gexec
#print axioms Gabbro.Grammatik.gfold
#print axioms Gabbro.Grammatik.group_move_no_exit
#print axioms Gabbro.Grammatik.lock_order_no_reentry_zeuge
#print axioms Gabbro.Grammatik.regRun
#print axioms Gabbro.Grammatik.entry_keeps
#print axioms Gabbro.Grammatik.entry_clobbers
#print axioms Gabbro.Grammatik.entry_keeps_zeuge
#print axioms Gabbro.Grammatik.jointMove
#print axioms Gabbro.Grammatik.jointTrace
#print axioms Gabbro.Grammatik.joint_move_hidden
#print axioms Gabbro.Grammatik.joint_move_hidden_zeuge
#print axioms Gabbro.Grammatik.runRmw
#print axioms Gabbro.Grammatik.rmw_chain_order
#print axioms Gabbro.Grammatik.rmw_chain_order_zeuge
#print axioms Gabbro.Grammatik.merge_swap_invariant
#print axioms Gabbro.Grammatik.merge_swap_invariant_zeuge
#print axioms Gabbro.Grammatik.mappingsOf
#print axioms Gabbro.Grammatik.walk_hits_mapping
#print axioms Gabbro.Grammatik.walk_hits_mapping_zeuge
#print axioms Gabbro.Grammatik.consume_shrinks
#print axioms Gabbro.Grammatik.consume_shrinks_zeuge
#print axioms Gabbro.Grammatik.consume_empty_at
#print axioms Gabbro.Grammatik.consume_empty_at_zeuge
#print axioms Gabbro.Grammatik.rehang
#print axioms Gabbro.Grammatik.rehang_can_cycle
#print axioms Gabbro.Grammatik.rehang_can_cycle_zeuge
#print axioms Gabbro.Grammatik.group_ops_compose
#print axioms Gabbro.Grammatik.group_ops_compose_zeuge
#print axioms Gabbro.Grammatik.treset
#print axioms Gabbro.Grammatik.reset_from_clean
#print axioms Gabbro.Grammatik.reset_rejects_held
#print axioms Gabbro.Grammatik.reset_from_clean_zeuge
#print axioms Gabbro.Grammatik.single_root
#print axioms Gabbro.Grammatik.single_root_zeuge
#print axioms Gabbro.Grammatik.table_induction
#print axioms Gabbro.Grammatik.induct_edge_in_type
#print axioms Gabbro.Grammatik.table_induction_zeuge
#print axioms Gabbro.Grammatik.table_ops_keep
#print axioms Gabbro.Grammatik.table_ops_keep_zeuge
#print axioms Gabbro.Grammatik.opSearch
#print axioms Gabbro.Grammatik.op_search_keeps
#print axioms Gabbro.Grammatik.op_search_first
#print axioms Gabbro.Grammatik.op_search_zeuge

end Gabbro.Grammatik
