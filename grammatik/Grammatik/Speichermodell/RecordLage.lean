/-
  File:      Grammatik/Speichermodell/RecordLage.lean
  Subject:   Record layout without padding (agent 03, usability team).

  Finding 8 of `messung/SPRACHE-EFFIZIENZ.md`: `type Mix` takes 24
  bytes in field order, 16 sorted by alignment. This file models, over
  every list of fields: rounding up, placement in order (`lage`),
  total size (`groesse`), per-field offsets (`offset`), and proves
  that sorted-descending alignment needs no internal padding
  (`absteigend_ohne_luecke`), is minimal (`absteigend_minimal`), and
  every access is aligned (`offset_ausgerichtet`). No program named,
  no Arm instruction facts (rule 7 N/A, recorded in CUTS).
-/

namespace Grammatik.Speichermodell.RecordLage

/-- One record field: its size and its alignment, both in bytes. -/
structure Feld where
  size : Nat
  align : Nat

/-- Well-formed: positive power-of-two alignment dividing the size.
    Carried as hypotheses, not structure proofs, so witnesses stay
    easy (`decide` on literals). -/
def Wohlgeformt (f : Feld) : Prop :=
  0 < f.align ∧ f.size % f.align = 0 ∧ ∃ k, f.align = 2 ^ k

/-- Round `x` up to a multiple of `a`. -/
def aufrunden (x a : Nat) : Nat := (x + a - 1) / a * a

/-- End offset placing `fs` in order from `off`, each field at the
    next offset aligned to its own alignment. -/
def lage : List Feld → Nat → Nat
  | [], off => off
  | f :: fs, off => lage fs (aufrunden off f.align + f.size)

/-- Maximum alignment (`1` for the empty record). -/
def maxAlign : List Feld → Nat
  | [] => 1
  | f :: fs => Nat.max f.align (maxAlign fs)

/-- Sum of sizes (the zero-padding total). -/
def sumSizes : List Feld → Nat
  | [] => 0
  | f :: fs => f.size + sumSizes fs

/-- Total size: end offset rounded up to the maximum alignment. -/
def groesse (fs : List Feld) : Nat := aufrunden (lage fs 0) (maxAlign fs)

/-- Placement offset of field `i` (threading the running offset). -/
def offsetAux : List Feld → Nat → Nat → Nat
  | [], _, off => off
  | f :: _, 0, off => aufrunden off f.align
  | f :: fs, i + 1, off => offsetAux fs i (aufrunden off f.align + f.size)

/-- Placement offset of field `i` from the record start. -/
def offset (fs : List Feld) (i : Nat) : Nat := offsetAux fs i 0

/-- Sorted by decreasing alignment: every later field fits the head. -/
def absteigend : List Feld → Prop
  | [] => True
  | f :: fs => (∀ g ∈ fs, g.align ≤ f.align) ∧ absteigend fs

/-! ## 2. Padding never shrinks. -/

/-- Rounding up grows (for positive alignment). -/
theorem aufrunden_ge (x a : Nat) (h : 1 ≤ a) : x ≤ aufrunden x a := by
  unfold aufrunden
  have heq : (x + a - 1) / a * a + (x + a - 1) % a = x + a - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have hlt : (x + a - 1) % a < a := Nat.mod_lt _ (by omega)
  omega

/-- A rounded offset is a multiple of the alignment. -/
theorem aufrunden_mod (x a : Nat) : aufrunden x a % a = 0 := by
  unfold aufrunden
  rw [Nat.mul_comm]
  exact Nat.mul_mod_right _ _

/-- Powers of two divide upward. -/
theorem dvd_of_pow2_le {i j : Nat} (h : i ≤ j) : 2 ^ i ∣ 2 ^ j :=
  Nat.pow_dvd_pow 2 h

/-- **Padding never makes the layout smaller**: the end offset covers
    the running offset plus every size. Needs positive alignments —
    at `align = 0` rounding resets to `0` (e.g. two `{5, 0}` fields
    end at 7 below their total 12), so the unpremised form is false;
    `Wohlgeformt` carries the positivity. -/
theorem lage_ge_summe (fs : List Feld) (off : Nat)
    (hw : ∀ f ∈ fs, Wohlgeformt f) :
    off + sumSizes fs ≤ lage fs off := by
  induction fs generalizing off with
  | nil => simp [lage, sumSizes]
  | cons f fs ih =>
      have hwf := hw f (List.mem_cons_self ..)
      obtain ⟨hpos, _, _⟩ := hwf
      have hmem : ∀ g ∈ fs, Wohlgeformt g :=
        fun g hg => hw g (List.mem_cons_of_mem _ hg)
      have ih' := ih (aufrunden off f.align + f.size) hmem
      have hg : off ≤ aufrunden off f.align :=
        aufrunden_ge off f.align (by omega)
      simp only [lage, sumSizes]
      omega

/-! ## 3. Sorted-descending alignment needs no padding. -/

/-- Rounding an already-aligned offset changes nothing. -/
theorem aufrunden_eq_of_mod (x a : Nat) (h1 : 1 ≤ a) (h2 : x % a = 0) :
    aufrunden x a = x := by
  have hqr : x = a * (x / a) := by
    have h := Nat.div_add_mod x a
    rw [h2] at h
    omega
  have hz : (a - 1) / a = 0 := Nat.div_eq_of_lt (by omega)
  have hsplit : x + a - 1 = a * (x / a) + (a - 1) := by omega
  unfold aufrunden
  rw [hsplit, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < a), hz]
  simp
  rw [Nat.mul_comm]
  exact hqr.symm

/-- Divisibility from a zero remainder. -/
theorem dvd_of_mod_zero (a b : Nat) (h : b % a = 0) : a ∣ b :=
  ⟨b / a, by have hda := Nat.div_add_mod b a; rw [h] at hda; omega⟩

/-- Powers of two divide upward under `≤`. -/
theorem pow2_dvd_of_le {a b : Nat} (ha : ∃ i, a = 2 ^ i)
    (hb : ∃ j, b = 2 ^ j) (hle : a ≤ b) : a ∣ b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle
  exact dvd_of_pow2_le hij

/-- In a sorted-descending well-formed list, every later alignment
    divides the head alignment. -/
theorem sorted_dvd_head (f : Feld) (fs : List Feld)
    (hle : ∀ g ∈ fs, g.align ≤ f.align)
    (hwf : Wohlgeformt f) (hwfs : ∀ g ∈ fs, Wohlgeformt g)
    (g : Feld) (hg : g ∈ fs) : g.align ∣ f.align := by
  have h1 := hle g hg
  obtain ⟨_, _, ⟨i, hi⟩⟩ := hwfs g hg
  obtain ⟨_, _, ⟨j, hj⟩⟩ := hwf
  exact pow2_dvd_of_le ⟨i, hi⟩ ⟨j, hj⟩ h1

/-- **Sorted-descending alignment needs no internal padding**: every
    running offset is already a multiple of the next alignment (it is
    a sum of multiples of larger alignments), so rounding is the
    identity at each step. -/
theorem absteigend_ohne_luecke (fs : List Feld)
    (hs : absteigend fs) (hw : ∀ f ∈ fs, Wohlgeformt f) :
    lage fs 0 = sumSizes fs := by
  have aux : ∀ (fs : List Feld) (off : Nat), absteigend fs →
      (∀ f ∈ fs, Wohlgeformt f) → (∀ g ∈ fs, g.align ∣ off) →
      lage fs off = off + sumSizes fs := by
    intro fs
    induction fs with
    | nil => intro off hs hw hd; simp [lage, sumSizes]
    | cons f fs ih =>
        intro off hs hw hd
        simp only [absteigend] at hs
        obtain ⟨hle, hs'⟩ := hs
        have hwf : Wohlgeformt f := hw f (List.mem_cons_self ..)
        have hmem : ∀ g ∈ fs, Wohlgeformt g :=
          fun g hg => hw g (List.mem_cons_of_mem _ hg)
        have hpos : 0 < f.align := hwf.1
        have hsz0 : f.size % f.align = 0 := hwf.2.1
        have hdf : f.align ∣ off := hd f (List.mem_cons_self ..)
        have hmod : off % f.align = 0 := Nat.mod_eq_zero_of_dvd hdf
        have hau : aufrunden off f.align = off :=
          aufrunden_eq_of_mod off f.align (by omega) hmod
        have hsz : f.align ∣ f.size := dvd_of_mod_zero _ _ hsz0
        have hd' : ∀ g ∈ fs, g.align ∣ off + f.size := by
          intro g hg
          have hgal : g.align ∣ f.align :=
            sorted_dvd_head f fs hle hwf hmem g hg
          exact Nat.dvd_trans hgal (Nat.dvd_add hdf hsz)
        have ih' := ih (off + f.size) hs' hmem hd'
        simp only [lage, sumSizes]
        rw [hau]
        omega
  have h0 : ∀ g ∈ fs, g.align ∣ 0 := fun g _ => ⟨0, by simp⟩
  have hmain := aux fs 0 hs hw h0
  omega

/-! ## 4. Every placement offset is aligned. -/

/-- Every placement offset is a multiple of its field's alignment —
    the property native loads and stores need. -/
theorem offsetAux_ausgerichtet (fs : List Feld) (i off : Nat)
    (f : Feld) (hmem : fs[i]? = some f) :
    offsetAux fs i off % f.align = 0 := by
  induction fs generalizing i off with
  | nil =>
      simp at hmem
  | cons g fs ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hmem
          cases hmem
          simp only [offsetAux]
          exact aufrunden_mod _ _
      | succ j =>
          simp only [List.getElem?_cons_succ] at hmem
          simp only [offsetAux]
          exact ih _ _ hmem

/-- Placement offsets from the record start are aligned. -/
theorem offset_ausgerichtet (fs : List Feld) (i : Nat) (f : Feld)
    (hmem : fs[i]? = some f) : offset fs i % f.align = 0 :=
  offsetAux_ausgerichtet fs i 0 f hmem

/-! ## 5. Witnesses: the finding's numbers, decided. -/

/-- Source order costs 24 bytes. -/
theorem mix_groesse_24 :
    groesse [⟨1, 1⟩, ⟨8, 8⟩, ⟨1, 1⟩] = 24 := by decide

/-- Sorted order costs 16 bytes. -/
theorem sortiert_groesse_16 :
    groesse [⟨8, 8⟩, ⟨1, 1⟩, ⟨1, 1⟩] = 16 := by decide

/-- The sorted layout itself is 10 bytes before final rounding. -/
theorem sortiert_lage_10 :
    lage [⟨8, 8⟩, ⟨1, 1⟩, ⟨1, 1⟩] 0 = 10 := by decide

/-! ## 5. Sorted order is minimal. -/

/-- Rounding up is monotone in the value. -/
theorem aufrunden_mono_fst {x y a : Nat} (h : x ≤ y) :
    aufrunden x a ≤ aufrunden y a := by
  unfold aufrunden
  have hdiv : (x + a - 1) / a ≤ (y + a - 1) / a :=
    Nat.div_le_div_right (by omega)
  exact Nat.mul_le_mul_right _ hdiv

/-- Permuted lists have the same total. -/
theorem sumSizes_perm {l₁ l₂ : List Feld} (h : l₁.Perm l₂) :
    sumSizes l₁ = sumSizes l₂ := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [sumSizes]; rw [ih]
  | swap a b l => simp only [sumSizes]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Permuted lists have the same maximum alignment. -/
theorem maxAlign_perm {l₁ l₂ : List Feld} (h : l₁.Perm l₂) :
    maxAlign l₁ = maxAlign l₂ := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [maxAlign]; rw [ih]
  | swap a b l => simp only [maxAlign]; exact Nat.max_left_comm _ _ _
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- **Sorted-descending order is minimal**: any permutation costs at
    least as much — its layout covers the same total inside the same
    maximum alignment, both preserved by permutation. -/
theorem absteigend_minimal (fs gs : List Feld)
    (hs : absteigend fs) (hw : ∀ f ∈ fs, Wohlgeformt f)
    (hp : gs.Perm fs) :
    groesse fs ≤ groesse gs := by
  have hS : sumSizes gs = sumSizes fs := sumSizes_perm hp
  have hM : maxAlign gs = maxAlign fs := maxAlign_perm hp
  have hwg : ∀ f ∈ gs, Wohlgeformt f := fun f hf => hw f ((List.Perm.mem_iff hp).mp hf)
  have hL : sumSizes gs ≤ lage gs 0 := by
    have h2 := lage_ge_summe gs 0 hwg
    omega
  have hmono : aufrunden (sumSizes fs) (maxAlign fs) ≤
      aufrunden (lage gs 0) (maxAlign gs) := by
    rw [← hS, ← hM]
    exact aufrunden_mono_fst hL
  simp only [groesse]
  rw [absteigend_ohne_luecke fs hs hw]
  exact hmono

end Grammatik.Speichermodell.RecordLage

/-
CUTS: what is not proved or not covered.
  - Proved: rounding helpers (`aufrunden_ge`, `aufrunden_mod`,
    `aufrunden_eq_of_mod`, `aufrunden_mono_fst`), power-of-two
    divisibility (`dvd_of_pow2_le`, `pow2_dvd_of_le`,
    `dvd_of_mod_zero`, `sorted_dvd_head`), no padding for
    sorted-descending well-formed lists (`absteigend_ohne_luecke`),
    minimality over permutations (`absteigend_minimal` via
    `sumSizes_perm`/`maxAlign_perm`), aligned offsets
    (`offsetAux_ausgerichtet`, `offset_ausgerichtet`), and decide
    witnesses for the finding's numbers (24/16/10).
  - `lage_ge_summe` and `absteigend_minimal` both need well-formed
    fields (positive alignments): the unpremised forms are false
    (align 0 resets rounding; recorded with counterexamples).
  - NOT proved: lowering to actual AArch64 loads/stores (compiler
    work); unions, packed attribute, bit-fields; heterogeneous
    per-field `size`/`align` side conditions beyond `Wohlgeformt`.
  - Rule 7 (Sail citations) is N/A: pure `Nat`/`List` layout
    arithmetic, no Arm instruction semantics (confidence:
    definitional — the file states no fact about any machine).
-/

#print axioms Grammatik.Speichermodell.RecordLage.aufrunden_ge
#print axioms Grammatik.Speichermodell.RecordLage.aufrunden_mod
#print axioms Grammatik.Speichermodell.RecordLage.aufrunden_eq_of_mod
#print axioms Grammatik.Speichermodell.RecordLage.lage_ge_summe
#print axioms Grammatik.Speichermodell.RecordLage.absteigend_ohne_luecke
#print axioms Grammatik.Speichermodell.RecordLage.absteigend_minimal
#print axioms Grammatik.Speichermodell.RecordLage.offsetAux_ausgerichtet
#print axioms Grammatik.Speichermodell.RecordLage.offset_ausgerichtet
#print axioms Grammatik.Speichermodell.RecordLage.mix_groesse_24
#print axioms Grammatik.Speichermodell.RecordLage.sortiert_groesse_16
#print axioms Grammatik.Speichermodell.RecordLage.sortiert_lage_10
