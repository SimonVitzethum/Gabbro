/-
  File:      Grammatik/X86/PipelineTables.lean
  Subject:   Table extents for the direct pipeline: fixed arrays (indexed
             loads/stores with the checked bound), records (field
             offsets/layout) and region pointers with their declared
             extent, over the accepted `Pipeline.lean` lowering.

  Reused, not duplicated:
    - pipeline: `Layout`, `WorldRep`, `LayoutSep`, `senkWertT`,
      `senkWertT_gerade`, `senkWertT_korrekt`, `assignT_lauf`,
      `worldRep_store`, `repOk_int`, `senkStmt`, `senkBlock`,
      `validate`, `compileProg`, `lauf_zu_laufBytes`, `encodeAll`,
      `kanon`, `gerade`, `addrOff_natAdresse`;
    - image: `slotWort`, `slotWort_cast` (`PipelineImage.lean`);
    - representation: `repOk`, `RepSlot`, `zahlWort`, `intWort_zahlWort`
      (`SourceMemory.lean`), `read64`/`write64`, `lesbar8`/
      `schreibbar8`, `natAdresse` (`Speicher.lean`);
    - addresses: `effAddr_null`, `effAddr_in_region`
      (`EffectiveAddress.lean`); `basisKeinForm`, `adrOk`,
      `basisKeinForm_ok` (`AddressEncoding.lean`);
    - machine: `schritt_load64_erfolg`, `schritt_store64_erfolg`
      (`Ausfuehrung.lean`); `constInt?`, `constInt?_sound`
      (`OptimizationRules.lean`); source `execStmt`/`eval`
      (`Semantik.lean`, used, never redefined).
  No second IR, no second source interpreter, no per-program rule.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineImage
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86.PipelineTables

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage

variable {D : Deklaration}

/-! ## 1. Table anchors: array bases, row lengths, record field offsets -/

/-- A table anchor declares, per table, the array base address (`basis`),
    the row length in bytes (`zeile`) and the record field offsets
    (`felder`): row `k`, field `f` lives at
    `base + k * rowLen + off f`. Tables/fields absent from the lists
    are unplaced (their access is refused, never guessed). -/
structure TabAnker (D : Deklaration) where
  basis : List (D.Tab × Nat)
  zeile : List (D.Tab × Nat)
  felder : (t : D.Tab) → List (D.Feld t × Nat)

/-- The array base of a table: the first listed base (first hit). -/
def ankerBasis (A : TabAnker D) (t : D.Tab) : Option Nat :=
  (A.basis.find? (fun e => decide (e.1 = t))).map Prod.snd

/-- The row length of a table: the first listed length. -/
def ankerZeile (A : TabAnker D) (t : D.Tab) : Option Nat :=
  (A.zeile.find? (fun e => decide (e.1 = t))).map Prod.snd

/-- The record offset of a field: the first listed offset. -/
def feldOff (A : TabAnker D) (t : D.Tab) (f : D.Feld t) : Option Nat :=
  ((A.felder t).find? (fun e => decide (e.1 = f))).map Prod.snd

/-- The checked array bound: the source's bounds duty as a decided
    check (`0 <= k < n`, never silently assumed). -/
def idxOkB (k n : Int) : Bool := decide (0 ≤ k ∧ k < n)

/-- The address of row `k`, field `f`: base plus row stride plus record
    offset. `none` outside the declared extent (unlisted table, missing
    row length, unlisted field, or the index outside `0 ..< count`):
    every such access is refused downstream, never guessed. -/
def feldAdr (A : TabAnker D) (t : D.Tab) (k : Int) (f : D.Feld t) : Option Nat :=
  match ankerBasis A t, ankerZeile A t, feldOff A t f with
  | some B, some Z, some O =>
    if idxOkB k (D.count t) then some (B + k.toNat * Z + O) else none
  | _, _, _ => none

/-- Inversion of a placed address: the base, row length and offset the
    anchor lists, the checked bound, and the address equation. -/
theorem feldAdr_some (A : TabAnker D) (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat)
    (h : feldAdr A t k f = some a) :
    ∃ B Z O, ankerBasis A t = some B ∧ ankerZeile A t = some Z ∧
      feldOff A t f = some O ∧ 0 ≤ k ∧ k < D.count t ∧
      a = B + k.toNat * Z + O := by
  unfold feldAdr at h
  cases hB : ankerBasis A t with
  | none => simp [hB] at h
  | some B =>
    cases hZ : ankerZeile A t with
    | none => simp [hB, hZ] at h
    | some Z =>
      cases hO : feldOff A t f with
      | none => simp [hB, hZ, hO] at h
      | some O =>
        simp only [hB, hZ, hO] at h
        by_cases hb : idxOkB k (D.count t) = true
        · rw [if_pos hb, Option.some.injEq] at h
          unfold idxOkB at hb
          simp only [decide_eq_true_eq] at hb
          exact ⟨B, Z, O, rfl, rfl, rfl, hb.1, hb.2, h.symm⟩
        · rw [if_neg hb] at h; cases h

/-- An index outside the extent is refused: no address is computed. -/
theorem feldAdr_kein_oob (A : TabAnker D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (h : ¬ (0 ≤ k ∧ k < D.count t)) : feldAdr A t k f = none := by
  unfold feldAdr idxOkB
  cases hB : ankerBasis A t <;> cases hZ : ankerZeile A t <;> cases hO : feldOff A t f <;>
    simp_all only [decide_eq_true_eq, if_false]

/-- The checked bound as a `Nat` bound for the row enumeration. -/
theorem idxOk_toNat (k n : Int) (h : idxOkB k n = true) : k.toNat < n.toNat := by
  unfold idxOkB at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ((k.toNat : Int) = k) := Int.toNat_of_nonneg h1
  by_cases hn : 0 ≤ n
  · have e2 : ((n.toNat : Int) = n) := Int.toNat_of_nonneg hn
    omega
  · have hn' : n < 0 := Int.not_le.mp hn
    have : False := by omega
    exact False.elim this

/-! ## 2. The computed layout and its decided separation -/

/-- The layout of an anchor: the computed address, `none` outside the
    declared extent. This plugs directly into the accepted lowering
    (`senkStmt`/`senkBlock`/`validate`): an unplaced slot is refused
    there, never guessed. -/
def tabLayout (A : TabAnker D) : Layout D where
  loc := fun t k f => feldAdr A t k f

theorem tabLayout_loc (A : TabAnker D) (t : D.Tab) (k : Int) (f : D.Feld t) :
    (tabLayout A).loc t k f = feldAdr A t k f := rfl

/-- A looked-up base comes from a listed entry naming the table. -/
theorem ankerBasis_mem (A : TabAnker D) (t : D.Tab) (B : Nat)
    (h : ankerBasis A t = some B) : ∃ e ∈ A.basis, e.1 = t ∧ e.2 = B := by
  unfold ankerBasis at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hp := List.find?_some he
  simp only [decide_eq_true_eq] at hp
  exact ⟨e, List.mem_of_find?_eq_some he, hp, rfl⟩

/-- A looked-up row length comes from a listed entry. -/
theorem ankerZeile_mem (A : TabAnker D) (t : D.Tab) (Z : Nat)
    (h : ankerZeile A t = some Z) : ∃ e ∈ A.zeile, e.1 = t ∧ e.2 = Z := by
  unfold ankerZeile at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hp := List.find?_some he
  simp only [decide_eq_true_eq] at hp
  exact ⟨e, List.mem_of_find?_eq_some he, hp, rfl⟩

/-- A looked-up field offset comes from a listed entry. -/
theorem feldOff_mem (A : TabAnker D) (t : D.Tab) (f : D.Feld t) (O : Nat)
    (h : feldOff A t f = some O) : ∃ e ∈ A.felder t, e.1 = f ∧ e.2 = O := by
  unfold feldOff at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  have hp := List.find?_some he
  simp only [decide_eq_true_eq] at hp
  exact ⟨e, List.mem_of_find?_eq_some he, hp, rfl⟩

/-- DECIDED LAYOUT SEPARATION: every basis entry has a row length with
    its extent inside 64 bits, every listed offset lies inside its row,
    listed fields of one table are pairwise disjoint, and distinct
    tables' extents are disjoint. All over finite lists. -/
def ankerEintragB (A : TabAnker D) (e : D.Tab × Nat) : Bool :=
  match ankerZeile A e.1 with
  | some Z => decide (0 < Z ∧ e.2 + (D.count e.1).toNat * Z ≤ 2 ^ 64) &&
    ((A.felder e.1).all fun fo => decide (fo.2 + 8 ≤ Z)) &&
    decide ((A.felder e.1).Pairwise fun f1 f2 =>
      f1.1 ≠ f2.1 → (f1.2 + 8 ≤ f2.2 ∨ f2.2 + 8 ≤ f1.2)) &&
    A.basis.all fun e2 => (match ankerZeile A e2.1 with
      | some Z2 => if decide (e.1 = e2.1) then true
          else decide (e.2 + (D.count e.1).toNat * Z ≤ e2.2 ∨
            e2.2 + (D.count e2.1).toNat * Z2 ≤ e.2)
      | none => true)
  | none => false

def ankerSepB (A : TabAnker D) : Bool := A.basis.all (ankerEintragB A)

/-- Inversion of one entry check: the row facts, the offset facts, the
    field-disjointness and the cross-table facts, at the looked-up row
    length. -/
theorem ankerEintrag_inv (A : TabAnker D) (e : D.Tab × Nat) (Z : Nat)
    (hz : ankerZeile A e.1 = some Z) (h : ankerEintragB A e = true) :
    (0 < Z ∧ e.2 + (D.count e.1).toNat * Z ≤ 2 ^ 64) ∧
    (∀ fo ∈ A.felder e.1, fo.2 + 8 ≤ Z) ∧
    ((A.felder e.1).Pairwise fun f1 f2 =>
      f1.1 ≠ f2.1 → (f1.2 + 8 ≤ f2.2 ∨ f2.2 + 8 ≤ f1.2)) ∧
    (∀ e2 ∈ A.basis, ∀ Z2, ankerZeile A e2.1 = some Z2 →
      e.1 = e2.1 ∨
      (e.2 + (D.count e.1).toNat * Z ≤ e2.2 ∨
        e2.2 + (D.count e2.1).toNat * Z2 ≤ e.2)) := by
  unfold ankerEintragB at h
  cases hz2 : ankerZeile A e.1 with
  | none =>
    rw [hz2] at hz
    simp at hz
  | some Z' =>
    have hZZ : Z' = Z := Option.some.inj (hz2.symm.trans hz)
    subst hZZ
    simp only [hz2, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hZ, hOff⟩, hPair⟩, hCross⟩ := h
    refine ⟨of_decide_eq_true hZ, ?_, of_decide_eq_true hPair, ?_⟩
    · intro fo hfo
      have hfo2 := List.all_eq_true.mp hOff fo hfo
      exact of_decide_eq_true hfo2
    · intro e2 he2 Z2 hz2e
      have hcr := List.all_eq_true.mp hCross e2 he2
      simp only [hz2e] at hcr
      by_cases heq : e.1 = e2.1
      · rw [if_pos (by simp [heq])] at hcr
        exact Or.inl heq
      · rw [if_neg (by simp [heq])] at hcr
        exact Or.inr (of_decide_eq_true hcr)

/-- SEPARATION FROM THE CHECK: the decided `ankerSepB` gives the
    pipeline's `LayoutSep` for the computed layout. Same slot or
    disjoint eight-byte footprints: rows of one table are apart by
    row-stride arithmetic, fields of one row by the listed offsets,
    tables by their extents. -/
theorem ankerSep_sound (A : TabAnker D) (h : ankerSepB A = true) :
    LayoutSep (tabLayout A) := by
  intro t1 k1 f1 a1 t2 k2 f2 a2 h1 h2
  rw [tabLayout_loc] at h1 h2
  obtain ⟨B1, Z1, O1, hB1, hZ1, hO1, hk1a, hk1b, ha1⟩ := feldAdr_some A t1 k1 f1 a1 h1
  obtain ⟨B2, Z2, O2, hB2, hZ2, hO2, hk2a, hk2b, ha2⟩ := feldAdr_some A t2 k2 f2 a2 h2
  obtain ⟨e1, he1, ht1, hB1e⟩ := ankerBasis_mem A t1 B1 hB1
  obtain ⟨e2, he2, ht2, hB2e⟩ := ankerBasis_mem A t2 B2 hB2
  obtain ⟨o1, ho1, hf1, hO1e⟩ := feldOff_mem A t1 f1 O1 hO1
  obtain ⟨o2, ho2, hf2, hO2e⟩ := feldOff_mem A t2 f2 O2 hO2
  have hall : ∀ x ∈ A.basis, ankerEintragB A x = true := by
    unfold ankerSepB at h
    exact List.all_eq_true.mp h
  have hz1e : ankerZeile A e1.1 = some Z1 := by rw [ht1]; exact hZ1
  obtain ⟨hZE1, hOff1, hPair1e, hCross1⟩ := ankerEintrag_inv A e1 Z1 hz1e (hall e1 he1)
  rw [ht1, hB1e] at hZE1
  obtain ⟨hZ1pos, hE1⟩ := hZE1
  have hz2e : ankerZeile A e2.1 = some Z2 := by rw [ht2]; exact hZ2
  obtain ⟨-, hOff2, -, -⟩ := ankerEintrag_inv A e2 Z2 hz2e (hall e2 he2)
  have hb1 : idxOkB k1 (D.count t1) = true := by
    simp only [idxOkB, decide_eq_true_eq]; exact ⟨hk1a, hk1b⟩
  have hb2 : idxOkB k2 (D.count t2) = true := by
    simp only [idxOkB, decide_eq_true_eq]; exact ⟨hk2a, hk2b⟩
  have hkn1 : k1.toNat < (D.count t1).toNat := idxOk_toNat _ _ hb1
  have hkn2 : k2.toNat < (D.count t2).toNat := idxOk_toNat _ _ hb2
  have hOff1' : ∀ fo ∈ A.felder t1, fo.2 + 8 ≤ Z1 := by
    rw [← ht1]; exact hOff1
  have hPair1' : (A.felder t1).Pairwise fun f1 f2 =>
      f1.1 ≠ f2.1 → (f1.2 + 8 ≤ f2.2 ∨ f2.2 + 8 ≤ f1.2) := by
    rw [← ht1]; exact hPair1e
  have hOff2' : ∀ fo ∈ A.felder t2, fo.2 + 8 ≤ Z2 := by
    rw [← ht2]; exact hOff2
  have hO1 : O1 + 8 ≤ Z1 := by
    have h7 := hOff1' o1 ho1
    rw [hO1e] at h7
    exact h7
  have hO2 : O2 + 8 ≤ Z2 := by
    have h7 := hOff2' o2 ho2
    rw [hO2e] at h7
    exact h7
  by_cases ht : t1 = t2
  · subst ht
    have hBB : B1 = B2 := Option.some.inj (hB1.symm.trans hB2)
    have hZZ : Z1 = Z2 := Option.some.inj (hZ1.symm.trans hZ2)
    subst hBB
    subst hZZ
    by_cases hk : k1 = k2
    · subst hk
      by_cases hf : f1 = f2
      · subst hf
        exact Or.inl ⟨rfl, rfl, HEq.rfl⟩
      · have mo2 : o2 ∈ A.felder t1 := ho2
        rcases pairwise_drei hPair1' ho1 mo2 with heq | hR | hR
        · have : o1.1 = o2.1 := congrArg Prod.fst heq
          rw [hf1, hf2] at this
          exact absurd this hf
        · have hne : o1.1 ≠ o2.1 := by rw [hf1, hf2]; exact hf
          have hd := hR hne
          rw [hO1e, hO2e] at hd
          right
          rw [ha1, ha2]
          rcases hd with hd | hd <;> omega
        · have hne : o2.1 ≠ o1.1 := by rw [hf1, hf2]; exact fun e => hf e.symm
          have hd := hR hne
          rw [hO1e, hO2e] at hd
          right
          rw [ha1, ha2]
          rcases hd with hd | hd <;> omega
    · have hne : k1.toNat ≠ k2.toNat := by
        intro heq
        have g1 : ((k1.toNat : Int) = k1) := Int.toNat_of_nonneg hk1a
        have g2 : ((k2.toNat : Int) = k2) := Int.toNat_of_nonneg hk2a
        exact hk (by omega)
      have hord : k1.toNat < k2.toNat ∨ k2.toNat < k1.toNat := by omega
      have hexp1 : (k1.toNat + 1) * Z1 = k1.toNat * Z1 + Z1 := by
        rw [Nat.add_mul, Nat.one_mul]
      have hexp2 : (k2.toNat + 1) * Z1 = k2.toNat * Z1 + Z1 := by
        rw [Nat.add_mul, Nat.one_mul]
      right
      rcases hord with hlt | hlt
      · have hmul : (k1.toNat + 1) * Z1 ≤ k2.toNat * Z1 :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        omega
      · have hmul : (k2.toNat + 1) * Z1 ≤ k1.toNat * Z1 :=
          Nat.mul_le_mul (by omega) (Nat.le_refl _)
        omega
  · have hcr := hCross1 e2 he2 Z2 hz2e
    rw [ht1, ht2, hB1e, hB2e] at hcr
    have hexp1 : (k1.toNat + 1) * Z1 = k1.toNat * Z1 + Z1 := by
      rw [Nat.add_mul, Nat.one_mul]
    have hexp2 : (k2.toNat + 1) * Z2 = k2.toNat * Z2 + Z2 := by
      rw [Nat.add_mul, Nat.one_mul]
    right
    rcases hcr with heq | hle | hle
    · exact absurd heq ht
    · have hmul : (k1.toNat + 1) * Z1 ≤ (D.count t1).toNat * Z1 :=
        Nat.mul_le_mul (by omega) (Nat.le_refl _)
      omega
    · have hmul : (k2.toNat + 1) * Z2 ≤ (D.count t2).toNat * Z2 :=
        Nat.mul_le_mul (by omega) (Nat.le_refl _)
      omega

/-! ## 3. Decided admission and the world representation -/

/-- DECIDED PLACEMENT ADMISSION over a memory (`platzOkB`-style): every
    row of every anchored table, at every listed field, is an admitted
    integer slot (`repOk`), readable and writable for its eight bytes.
    The enumeration is finite: rows by `count`, fields by the list. -/
def tabOkB (A : TabAnker D) (m : Speicher) : Bool :=
  A.basis.all fun e => (match ankerZeile A e.1 with
    | some Z => ((List.range (D.count e.1).toNat).all fun kn =>
      ((A.felder e.1).all fun fo =>
        let Adr := e.2 + kn * Z + fo.2
        (repOk (D.typ e.1 fo.1) Adr 8 0 && lesbar8 m (natAdresse Adr) &&
          schreibbar8 m (natAdresse Adr))))
    | none => false)

/-- DECIDED WORLD CHECK over a memory: every placed slot reads back the
    representation word of the source value. -/
def tabWeltB (A : TabAnker D) (m : Speicher) (σ : World D) : Bool :=
  A.basis.all fun e => (match ankerZeile A e.1 with
    | some Z => ((List.range (D.count e.1).toNat).all fun kn =>
      ((A.felder e.1).all fun fo =>
        let Adr := e.2 + kn * Z + fo.2
        decide (read64 m (natAdresse Adr) =
          some (slotWort _ (σ.slots e.1 (kn : Int) fo.1)))))
    | none => false)

/-- REPRESENTATION FROM THE CHECKS: admission and the world check give
    the pipeline's `WorldRep` for the computed layout. -/
theorem tabWorldRep (A : TabAnker D) (m : Speicher) (σ : World D)
    (hOk : tabOkB A m = true) (hW : tabWeltB A m σ = true) :
    WorldRep (tabLayout A) m σ := by
  intro t k f a hloc
  rw [tabLayout_loc] at hloc
  obtain ⟨B, Z, O, hB, hZ, hO, hka, hkb, ha⟩ := feldAdr_some A t k f a hloc
  obtain ⟨e, he, ht, hBe⟩ := ankerBasis_mem A t B hB
  obtain ⟨o, ho, hf, hOe⟩ := feldOff_mem A t f O hO
  subst hf
  have hallOk : ∀ x ∈ A.basis, (match ankerZeile A x.1 with
      | some Z => ((List.range (D.count x.1).toNat).all fun kn =>
        ((A.felder x.1).all fun fo =>
          let Adr := x.2 + kn * Z + fo.2
          (repOk (D.typ x.1 fo.1) Adr 8 0 && lesbar8 m (natAdresse Adr) &&
            schreibbar8 m (natAdresse Adr))))
      | none => false) = true := by
    unfold tabOkB at hOk
    exact List.all_eq_true.mp hOk
  have hZe : ankerZeile A e.1 = some Z := by rw [ht]; exact hZ
  have hrow := hallOk e he
  simp only [hZe] at hrow
  have hkn : k.toNat < (D.count t).toNat := idxOk_toNat k _
    (by simp only [idxOkB, decide_eq_true_eq]; exact ⟨hka, hkb⟩)
  have hkn' : k.toNat < (D.count e.1).toNat := by rw [ht]; exact hkn
  have hknmem : k.toNat ∈ List.range (D.count e.1).toNat := by
    rw [List.mem_range]; exact hkn'
  have hcell := List.all_eq_true.mp hrow _ hknmem
  rw [ht] at hcell
  have hslot := List.all_eq_true.mp hcell o ho
  simp only [Bool.and_eq_true] at hslot
  obtain ⟨⟨hrep, hrd⟩, hwr⟩ := hslot
  have hallW : ∀ x ∈ A.basis, (match ankerZeile A x.1 with
      | some Z => ((List.range (D.count x.1).toNat).all fun kn =>
        ((A.felder x.1).all fun fo =>
          let Adr := x.2 + kn * Z + fo.2
          decide (read64 m (natAdresse Adr) =
            some (slotWort _ (σ.slots x.1 (kn : Int) fo.1)))))
      | none => false) = true := by
    unfold tabWeltB at hW
    exact List.all_eq_true.mp hW
  have hrowW := hallW e he
  simp only [hZe] at hrowW
  have hcellW := List.all_eq_true.mp hrowW _ hknmem
  rw [ht] at hcellW
  have hreadW := List.all_eq_true.mp hcellW o ho
  have hslots : σ.slots t (k.toNat : Int) o.1 = σ.slots t k o.1 := by
    rw [Int.toNat_of_nonneg hka]
  rw [hBe, hOe] at hrep hrd hwr hreadW
  simp only [decide_eq_true_eq] at hreadW
  rw [← ha] at hrep hrd hwr
  rw [← ha, hslots] at hreadW
  refine ⟨hrep, hrd, hwr, fun lo hi hT => ?_⟩
  unfold RepSlot
  rw [slotWort_cast _ hT] at hreadW
  exact hreadW
