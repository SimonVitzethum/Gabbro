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
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86.PipelineTables

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineWitnesses

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

/-! ## 4. Lowering of source reads -/

/-- READ LOWERING: a table read at a constant in-extent index becomes
    the address materialisation plus a pilot `load64` through the
    address register (the `basisKeinForm` shape with zero displacement;
    `adrOk` is the checked premise, refused for `rbp`/`r13` bases).
    Reads through region pointers (`durch`) lower to the same address:
    the pointer value is `Unit`, so the pointer contributes no address,
    only its carrier equation (reused, never rechecked). A
    non-constant index, an out-of-extent index, an unlisted
    table/field, a non-integer field, or a refused address form gives
    `none`: unsupported shapes are refused, never guessed. -/
def senkLesen (A : TabAnker D) (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) : Option (List Befehl) :=
  match e with
  | .slot t f i _ => match constInt? i with
    | some k => match feldAdr A t k f with
      | some Adr => if repOk (D.typ t f) Adr 8 0 &&
          adrOk (basisKeinForm c.adr) then
          some [.movImm64 c.adr (natAdresse Adr),
            .load64 c.dst c.adr (BitVec.ofNat 32 0)]
        else none
      | none => none
    | none => none
  | .durch _ t _ f i _ => match constInt? i with
    | some k => match feldAdr A t k f with
      | some Adr => if repOk (D.typ t f) Adr 8 0 &&
          adrOk (basisKeinForm c.adr) then
          some [.movImm64 c.adr (natAdresse Adr),
            .load64 c.dst c.adr (BitVec.ofNat 32 0)]
        else none
      | none => none
    | none => none
  | _ => none

/-- LOAD CHUNK: materialise the computed address and load the word
    through it. `effAddr_null` pins the effective address to the base
    register, so the load reads exactly the computed slot address.
    Memory and every register but the two working ones are kept. -/
theorem lesChunk_lauf (c : PipeCfg) (hc : cfgOk c = true)
    (Adr : Nat) (w : Wort) (s : Zustand)
    (hrd : read64 s.speicher (natAdresse Adr) = some w) :
    ∃ s', lauf ([Befehl.movImm64 c.adr (natAdresse Adr),
      Befehl.load64 c.dst c.adr (BitVec.ofNat 32 0)].map kanon) s = some s' ∧
      s'.register c.dst = w ∧ s'.speicher = s.speicher ∧
      (∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s.register q) := by
  obtain ⟨-, hda, -, -, -, -⟩ := cfgOk_regs c hc
  have hmov := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse Adr))) s c.adr
    (natAdresse Adr) (laengeOk_encode _) rfl
  let s1 : Zustand := schrittRegister s
    (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse Adr))).laenge)
    s.flags c.adr (natAdresse Adr)
  have heff : effAddr s1 c.adr (BitVec.ofNat 32 0) = natAdresse Adr := by
    simp only [effAddr_null]
    exact regSet_gleich _ _ _
  have hrd1 : read64 s1.speicher (effAddr s1 c.adr (BitVec.ofNat 32 0)) = some w := by
    rw [heff]
    exact hrd
  have hload := schritt_load64_erfolg (kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0)))
    s1 c.dst c.adr (BitVec.ofNat 32 0) w (laengeOk_encode _) rfl hrd1
  let s' : Zustand := schrittRegister s1 (ripNach s1.rip
    (kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0))).laenge) s1.flags c.dst w
  have hrun : lauf ([Befehl.movImm64 c.adr (natAdresse Adr),
      Befehl.load64 c.dst c.adr (BitVec.ofNat 32 0)].map kanon) s = some s' := by
    have e1 : ([Befehl.movImm64 c.adr (natAdresse Adr),
        Befehl.load64 c.dst c.adr (BitVec.ofNat 32 0)].map kanon) =
        [kanon (.movImm64 c.adr (natAdresse Adr))] ++
        [kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0))] := rfl
    rw [e1, lauf_anhang _ _ _ _ (by rw [lauf_einzeln_gleich, hmov]),
      lauf_einzeln_gleich, hload]
  have hdst : s'.register c.dst = w :=
    regSet_gleich _ _ _
  have hmem : s'.speicher = s.speicher :=
    (schrittRegister_speicher _ _ _ _ _).trans (schrittRegister_speicher _ _ _ _ _)
  have hreg : ∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s.register q := by
    intro q hqd hqa
    show regSet s1.register c.dst w q = s.register q
    rw [regSet_fremd _ _ _ _ hqd]
    show regSet s.register c.adr (natAdresse Adr) q = s.register q
    rw [regSet_fremd _ _ _ _ hqa]
  exact ⟨s', hrun, hdst, hmem, hreg⟩

/-- READ CORRECTNESS: the lowered load code leaves the modular word of
    the exact source value in `dst`, keeps memory and the environment,
    and keeps every register but the two working ones. Stated at a
    general type index with `τ = .int lo hi` (the stuck slot type
    `D.typ t f`), in the style of `senkWert_korrekt`. -/
theorem senkLesen_korrekt (A : TabAnker D) (c : PipeCfg) (hc : cfgOk c = true)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {lo hi : Int}
    (e : Expr D Γ Λ τ) (hτ : τ = .int lo hi)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hE : EnvRepr ρ s.register (abbOf c)) (hW : WorldRep (tabLayout A) s.speicher σ)
    (p : List Befehl) (h : senkLesen A c e = some p) :
    ∃ s', lauf (p.map kanon) s = some s' ∧
      s'.register c.dst = intWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) :
        Wert D (.int lo hi)).n ∧
      s'.speicher = s.speicher ∧
      EnvRepr ρ s'.register (abbOf c) ∧
      (∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s.register q) := by
  cases e with
  | slot t f i hL =>
    simp only [senkLesen] at h
    cases hk : constInt? i with
    | none => rw [hk] at h; cases h
    | some k =>
      simp only [hk] at h
      cases hA : feldAdr A t k f with
      | none => simp [hA] at h
      | some Adr =>
        simp only [hA] at h
        by_cases hok : (repOk (D.typ t f) Adr 8 0 &&
            adrOk (basisKeinForm c.adr)) = true
        · rw [if_pos hok] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hok
          obtain ⟨hrep, hokRest⟩ := hok
          obtain ⟨lo', hi', hT', hlo, hhi, -⟩ := repOk_int _ _ hrep
          have hTT : (Ty.int lo hi) = (Ty.int lo' hi') := by rw [← hτ]; exact hT'
          have hlo' : lo = lo' := by cases hTT; rfl
          have hhi' : hi = hi' := by cases hTT; rfl
          subst hlo'
          subst hhi'
          have hki : (eval σ₀ i σ ρ).n = k := by
            have hci := constInt?_sound i σ₀ σ ρ k hk
            simpa [intOf] using hci
          have heval : (eval σ₀ (.slot t f i hL) σ ρ) = σ.slots t k f := by
            have hrfl : (eval σ₀ (.slot t f i hL) σ ρ) =
              σ.slots t (eval σ₀ i σ ρ).n f := rfl
            rw [hki] at hrfl
            exact hrfl
          obtain ⟨-, -, -, hword⟩ := hW t k f Adr
            (by rw [tabLayout_loc]; exact hA)
          have hrdW := hword lo hi hT'
          unfold RepSlot at hrdW
          obtain ⟨s', hrun, hdst, hmem, hreg⟩ := lesChunk_lauf c hc Adr _ s hrdW
          refine ⟨s', hrun, ?_, hmem, ?_, hreg⟩
          · rw [hdst, heval]
            exact (intWort_zahlWort _ hlo hhi).symm
          · exact envRepr_fremd ρ _ _ _ hE
              (fun _ x => hreg _ (cfgOk_frei c hc x).1 ((cfgOk_frei c hc x).2.2))
        · rw [if_neg hok] at h; cases h
  | durch p t ht f i hL =>
    simp only [senkLesen] at h
    cases hk : constInt? i with
    | none => rw [hk] at h; cases h
    | some k =>
      simp only [hk] at h
      cases hA : feldAdr A t k f with
      | none => simp [hA] at h
      | some Adr =>
        simp only [hA] at h
        by_cases hok : (repOk (D.typ t f) Adr 8 0 &&
            adrOk (basisKeinForm c.adr)) = true
        · rw [if_pos hok] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hok
          obtain ⟨hrep, hokRest⟩ := hok
          obtain ⟨lo', hi', hT', hlo, hhi, -⟩ := repOk_int _ _ hrep
          have hTT : (Ty.int lo hi) = (Ty.int lo' hi') := by rw [← hτ]; exact hT'
          have hlo' : lo = lo' := by cases hTT; rfl
          have hhi' : hi = hi' := by cases hTT; rfl
          subst hlo'
          subst hhi'
          have hki : (eval σ₀ i σ ρ).n = k := by
            have hci := constInt?_sound i σ₀ σ ρ k hk
            simpa [intOf] using hci
          have heval : (eval σ₀ (.durch p t ht f i hL) σ ρ) = σ.slots t k f := by
            have hrfl : (eval σ₀ (.durch p t ht f i hL) σ ρ) =
              σ.slots t (eval σ₀ i σ ρ).n f := rfl
            rw [hki] at hrfl
            exact hrfl
          obtain ⟨-, -, -, hword⟩ := hW t k f Adr
            (by rw [tabLayout_loc]; exact hA)
          have hrdW := hword lo hi hT'
          unfold RepSlot at hrdW
          obtain ⟨s', hrun, hdst, hmem, hreg⟩ := lesChunk_lauf c hc Adr _ s hrdW
          refine ⟨s', hrun, ?_, hmem, ?_, hreg⟩
          · rw [hdst, heval]
            exact (intWort_zahlWort _ hlo hhi).symm
          · exact envRepr_fremd ρ _ _ _ hE
              (fun _ x => hreg _ (cfgOk_frei c hc x).1 ((cfgOk_frei c hc x).2.2))
        · rw [if_neg hok] at h; cases h
  | _ => simp [senkLesen] at h

/-! ## 5. Lowering of source writes -/

/-- WRITE LOWERING: an array/record store at a constant in-extent index
    becomes the deep value code plus the address materialisation and a
    pilot `store64` (same shape as the accepted `senkStmt`, with the
    bound checked here instead of silently assumed). Stores through
    region pointers (`assignDurch`) lower identically: the pointer value
    is `Unit`, so only its carrier equation is reused. A non-constant
    index, an out-of-extent index, an unlisted table/field, a
    non-integer field, an unlowerable value, or a refused address form
    gives `none`. -/
def senkSchreiben (A : TabAnker D) (c : PipeCfg) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Option (List Befehl) :=
  match s with
  | .assignSlot t f i e _ _ => match constInt? i with
    | some k => match feldAdr A t k f with
      | some Adr => if repOk (D.typ t f) Adr 8 0 &&
          adrOk (basisKeinForm c.adr) then
          (senkWertT c e).map fun pv => pv ++
            [.movImm64 c.adr (natAdresse Adr),
              .store64 c.adr c.dst (BitVec.ofNat 32 0)]
        else none
      | none => none
    | none => none
  | .assignDurch _ t _ f i e _ _ => match constInt? i with
    | some k => match feldAdr A t k f with
      | some Adr => if repOk (D.typ t f) Adr 8 0 &&
          adrOk (basisKeinForm c.adr) then
          (senkWertT c e).map fun pv => pv ++
            [.movImm64 c.adr (natAdresse Adr),
              .store64 c.adr c.dst (BitVec.ofNat 32 0)]
        else none
      | none => none
    | none => none
  | _ => none

/-- WRITE CORRECTNESS: the lowered store runs the real `execStmt`
    outcome — the source world with the slot written — keeps the world
    represented and the environment, in the style of
    `senkBlock_korrektC` for one statement. -/
theorem senkSchreiben_korrekt (A : TabAnker D) (c : PipeCfg) (hc : cfgOk c = true)
    (hsep : ankerSepB A = true)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ')
    (ρ : Env D Γ) (σ : World D) (st : Zustand)
    (hE : EnvRepr ρ st.register (abbOf c)) (hW : WorldRep (tabLayout A) st.speicher σ)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (p : List Befehl) (h : senkSchreiben A c s = some p) :
    ∃ s' σ', lauf (p.map kanon) st = some s' ∧
      execStmt O passes R s σ ρ = .ok σ' ρ ∧
      WorldRep (tabLayout A) s'.speicher σ' ∧ EnvRepr ρ s'.register (abbOf c) := by
  cases s with
  | assignSlot t f i e hw hL =>
    simp only [senkSchreiben] at h
    cases hk : constInt? i with
    | none => rw [hk] at h; cases h
    | some k =>
      simp only [hk] at h
      cases hA : feldAdr A t k f with
      | none => simp [hA] at h
      | some Adr =>
        simp only [hA] at h
        by_cases hok : (repOk (D.typ t f) Adr 8 0 &&
            adrOk (basisKeinForm c.adr)) = true
        · rw [if_pos hok] at h
          cases hpv : senkWertT c e with
          | none => simp [hpv] at h
          | some pv =>
            simp only [hpv, Option.map_some, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hok
            obtain ⟨hrep, -⟩ := hok
            obtain ⟨lo, hi, hT, hlo, hhi, -⟩ := repOk_int _ _ hrep
            let σL := σ.lese Λ (i.orte ++ e.orte)
            have hki : (eval σL i σL ρ).n = k := by
              have hci := constInt?_sound i σL σL ρ k hk
              simpa [intOf] using hci
            have hsrc : execStmt O passes R
                ((.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ =
                .ok (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
              rw [← hki]; rfl
            obtain ⟨-, -, hwrA, -⟩ := hW t k f Adr
              (by rw [tabLayout_loc]; exact hA)
            obtain ⟨s1, hrun1, hw1, hE1⟩ :=
              assignT_lauf c hc e hT hlo hhi pv hpv Adr ρ σL σL st hE hwrA
            have hloc : (tabLayout A).loc t k f = some Adr := by
              rw [tabLayout_loc]; exact hA
            have hW1 : WorldRep (tabLayout A) s1.speicher
                (σL.schreibSlot t Λ k f (eval σL e σL ρ)) :=
              worldRep_store (tabLayout A) (ankerSep_sound A hsep) st.speicher s1.speicher
                σL t k f Adr hloc hW lo hi hT _ hw1 Λ
            exact ⟨s1, _, hrun1, hsrc, hW1, hE1⟩
        · rw [if_neg hok] at h; cases h
  | assignDurch q t ht f i e hw hL =>
    simp only [senkSchreiben] at h
    cases hk : constInt? i with
    | none => rw [hk] at h; cases h
    | some k =>
      simp only [hk] at h
      cases hA : feldAdr A t k f with
      | none => simp [hA] at h
      | some Adr =>
        simp only [hA] at h
        by_cases hok : (repOk (D.typ t f) Adr 8 0 &&
            adrOk (basisKeinForm c.adr)) = true
        · rw [if_pos hok] at h
          cases hpv : senkWertT c e with
          | none => simp [hpv] at h
          | some pv =>
            simp only [hpv, Option.map_some, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hok
            obtain ⟨hrep, -⟩ := hok
            obtain ⟨lo, hi, hT, hlo, hhi, -⟩ := repOk_int _ _ hrep
            let σL := σ.lese Λ (q.orte ++ i.orte ++ e.orte)
            have hki : (eval σL i σL ρ).n = k := by
              have hci := constInt?_sound i σL σL ρ k hk
              simpa [intOf] using hci
            have hsrc : execStmt O passes R
                ((.assignDurch q t ht f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ =
                .ok (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
              rw [← hki]; rfl
            obtain ⟨-, -, hwrA, -⟩ := hW t k f Adr
              (by rw [tabLayout_loc]; exact hA)
            obtain ⟨s1, hrun1, hw1, hE1⟩ :=
              assignT_lauf c hc e hT hlo hhi pv hpv Adr ρ σL σL st hE hwrA
            have hloc : (tabLayout A).loc t k f = some Adr := by
              rw [tabLayout_loc]; exact hA
            have hW1 : WorldRep (tabLayout A) s1.speicher
                (σL.schreibSlot t Λ k f (eval σL e σL ρ)) :=
              worldRep_store (tabLayout A) (ankerSep_sound A hsep) st.speicher s1.speicher
                σL t k f Adr hloc hW lo hi hT _ hw1 Λ
            exact ⟨s1, _, hrun1, hsrc, hW1, hE1⟩
        · rw [if_neg hok] at h; cases h
  | _ => simp [senkSchreiben] at h

/-! ## 6. Refusals: unplaced slots lower to nothing -/

/-- READ REFUSAL: a read whose slot has no computed address — an index
    outside the declared extent, an unlisted table, a missing row
    length, or an unlisted field — is refused (`none`): the source's
    bounds duty is the checked premise, never silently assumed. Reads
    through region pointers take the same path (their probes are
    concrete). -/
theorem senkLesen_verweigert_ausserhalb (A : TabAnker D) (c : PipeCfg)
    {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (k : Int) (hk : constInt? i = some k)
    (hno : feldAdr A t k f = none) (hL : darf D t Λ) :
    senkLesen A c (.slot t f i hL) = none := by
  simp only [senkLesen, hk, hno]

/-- READ REFUSAL, NON-CONSTANT INDEX: a read whose index is not a
    constant (a variable index, with no scaled addressing in the pilot)
    is refused (`none`). -/
theorem senkLesen_verweigert_nichtkonstant (A : TabAnker D) (c : PipeCfg)
    {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (hnc : constInt? i = none) (hL : darf D t Λ) :
    senkLesen A c (.slot t f i hL) = none := by
  simp only [senkLesen, hnc]

/-- WRITE REFUSAL: a store whose slot has no computed address is
    refused (`none`), for direct and pointer-through stores alike (the
    pointer path shares the check; its probes are concrete). -/
theorem senkSchreiben_verweigert_ausserhalb (A : TabAnker D) (c : PipeCfg)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (k : Int) (hk : constInt? i = some k)
    (hno : feldAdr A t k f = none) :
    senkSchreiben A c (.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ) = none := by
  simp only [senkSchreiben, hk, hno]

/-- WRITE REFUSAL, NON-CONSTANT INDEX: a store whose index is not a
    constant is refused (`none`). -/
theorem senkSchreiben_verweigert_nichtkonstant (A : TabAnker D) (c : PipeCfg)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (hnc : constInt? i = none) :
    senkSchreiben A c (.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ) = none := by
  simp only [senkSchreiben, hnc]

/-! ## 8. Witness declaration, anchor and programs -/

/-- Witness signature: parameterless, no answer, writes tables. -/
def zeSig : Signatur Bool Empty Empty Empty :=
  { params := [], erg := none, gruende := 0, haelt := [],
    schreibt := fun _ => true, gschreibt := fun g => (nomatch g),
    konsumiert := [], produziert := [], boden := none }

/-- One table family of two tables with two rows and two integer fields
    each — a genuine two-field record per row. Only the first table is
    anchored (the second is the unlisted-table probe). -/
def zeD : Deklaration where
  Tab := Bool
  count := fun _ => 2
  Feld := fun _ => Bool
  typ := fun _ _ => .int 0 1000
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some false | _ => none
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => zeSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The contract: writes tables, one refusal reason. -/
def zeV : Vertrag zeD :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 1
    haelt := []
    produziert := []
    boden := none }

def zeO : Orakel zeD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

def zeR : ∀ f : zeD.Fn, World zeD → Env zeD (zeD.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Target configuration: `r10` for a context variable; `rax`/`rcx`
    working, `rbx` the address register; code at 4096. -/
def zeCfg : PipeCfg :=
  { regs := [.r10], dst := .rax, tmp := .rcx, adr := .rbx, codeBase := 4096,
    exitBase := 12288 }

theorem zeCfgOk : cfgOk zeCfg = true := by decide

/-- The anchor: the first table at 8192, rows of 16 bytes, fields at
    offsets 0 and 8. Row 1, second field is at 8216. -/
def zeA : TabAnker zeD :=
  { basis := [(false, 8192)], zeile := [(false, 16)],
    felder := fun _ => [(false, 0), (true, 8)] }

theorem zeSep : ankerSepB zeA = true := by decide

theorem zeHw : zeV.schreibt false = true := rfl

theorem zeHL : darf zeD false [] := fun _ h => False.elim (List.not_mem_nil h)

theorem zeHL2 : darf zeD true [] := fun _ h => False.elim (List.not_mem_nil h)

/-- Row `1` as an index. -/
def zeIdx1 : Expr zeD [] [] (.index (zeD.count false)) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- The stored value `42`, widened to the field type. -/
def zeVal42 : Expr zeD [] [] (zeD.typ false true) :=
  .weiter (by decide) (by decide) (.lit 42)

/-- THE SOURCE WRITE: `T[1].f2 = 42;` -/
def zeWrite : Stmt zeD zeV false [] [] [] :=
  .assignSlot false true zeIdx1 zeVal42 zeHw zeHL

/-- THE SOURCE READ: `T[1].f2`. -/
def zeReadSlot : Expr zeD [] [] (zeD.typ false true) :=
  .slot false true zeIdx1 zeHL

/-- A region pointer to the anchored table. -/
def zePtr : Expr zeD [] [] (.ptr 0 true) := .ptrOf false 0 rfl true

/-- THE SOURCE READ THROUGH THE POINTER: `p->f2` at row 1. -/
def zeReadDurch : Expr zeD [] [] (zeD.typ false true) :=
  .durch zePtr false rfl true zeIdx1 zeHL

/-- THE SOURCE WRITE THROUGH THE POINTER: `p->f2 = 42;` at row 1. -/
def zeWriteDurch : Stmt zeD zeV false [] [] [] :=
  .assignDurch zePtr false rfl true zeIdx1 zeVal42 zeHw zeHL

/-- A read of the UNLISTED table (refused: no extent). -/
def zeReadFremd : Expr zeD [] [] (zeD.typ true true) :=
  .slot true true zeIdx1 zeHL2

/-- THE LOWERED STORE, written out as a producer would emit it. -/
def zeStoreProg : List Befehl :=
  [.movImm64 .rax (intWort 42),
    .movImm64 .rbx (natAdresse 8216), .store64 .rbx .rax (BitVec.ofNat 32 0)]

theorem zeLowWrite : senkSchreiben zeA zeCfg zeWrite = some zeStoreProg := by decide

/-- THE LOWERED LOAD, written out as a producer would emit it. -/
def zeLoadProg : List Befehl :=
  [.movImm64 .rbx (natAdresse 8216), .load64 .rax .rbx (BitVec.ofNat 32 0)]

theorem zeLowRead : senkLesen zeA zeCfg zeReadSlot = some zeLoadProg := by decide

theorem zeLowReadDurch : senkLesen zeA zeCfg zeReadDurch = some zeLoadProg := by decide

theorem zeLowWriteDurch : senkSchreiben zeA zeCfg zeWriteDurch = some zeStoreProg := by decide

/-! ## 9. Witness memory, world and representation -/

/-- The source world: every row and field holds 7. -/
def zeSigma : World zeD where
  slots := fun _ _ _ => (⟨7, by decide, by decide⟩ : Zahl 0 1000)
  globs := fun g => nomatch g
  spur := []

/-- The lowered store bytes (what the image holds). -/
def zeBytes : List Byte := encodeAll zeStoreProg

/-- The memory: code at `[4096, 4096 + len)`, the table extent at
    `[8192, 8224)` holding 7 in every slot, zero elsewhere. -/
def zeMemBytes (a : Adresse) : Byte :=
  if 4096 ≤ a.toNat ∧ a.toNat < 4096 + zeBytes.length then zeBytes.getD (a.toNat - 4096) 0
  else if 8192 ≤ a.toNat ∧ a.toNat < 8224 then wortByte 7 ((a.toNat - 8192) % 8)
  else 0

def zeCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + zeBytes.length)

def zeDaten (a : Adresse) : Bool := decide (8192 ≤ a.toNat ∧ a.toNat < 8224)

def zeMem : Speicher :=
  { bytes := zeMemBytes, lesbar := zeDaten, schreibbar := zeDaten, ausfuehrbar := zeCode }

/-- Registers: `r10` holds the variable index 0, everything else zero. -/
def zeReg : Register → Wort := fun q => if q = .r10 then intWort 0 else 0

def zeStart : Zustand :=
  { register := zeReg, flags := witnessFlags, rip := natAdresse 4096, speicher := zeMem }

theorem zeLenLt : 4096 + zeBytes.length < 2 ^ 64 := by decide

theorem zeLenDaten : zeBytes.length ≤ 4096 := by decide

theorem zeCodeAt : CodeAt zeMem (natAdresse 4096) zeBytes := by
  apply codeAt_von zeMem 4096 zeBytes zeLenLt
  intro a h1 h2
  have hlen := zeLenDaten
  have hd : ¬ (8192 ≤ a.toNat ∧ a.toNat < 8224) := by omega
  simp only [zeMem, zeCode, zeDaten, zeMemBytes, decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨⟨h1, h2⟩, hd, by rw [if_pos ⟨h1, h2⟩]⟩

theorem zeOkB : tabOkB zeA zeMem = true := by decide

theorem zeWeltB : tabWeltB zeA zeMem zeSigma = true := by decide

theorem zeWorldRep : WorldRep (tabLayout zeA) zeMem zeSigma :=
  tabWorldRep zeA zeMem zeSigma zeOkB zeWeltB

theorem zeEnvRepr : EnvRepr (D := zeD) (Env.nil : Env zeD []) zeStart.register (abbOf zeCfg) := by
  intro lo hi x
  cases x

/-- THE SOURCE RUN: `T[1].f2 = 42;` writes 42, through the real
    `execStmt`. -/
theorem zeSrcWrite : ∃ σ', execStmt zeO 0 zeR zeWrite zeSigma Env.nil = .ok σ' Env.nil ∧
    (σ'.slots false 1 true).n = 42 :=
  ⟨_, rfl, rfl⟩

/-- THE TARGET RUN reaches a state whose byte at 8216 changed from 7
    to 42: a real memory-changing reached run. -/
theorem zeWriteRun :
    ((lauf (zeStoreProg.map kanon) zeStart).map
      (fun s => s.speicher.bytes (natAdresse 8216)) =
      some (BitVec.ofNat 8 42)) ∧
    (zeStart.speicher.bytes (natAdresse 8216) = wortByte 7 0) := by
  refine ⟨by decide, by decide⟩

/-- The source read evaluates to 7. -/
theorem zeReadEval : (eval zeSigma zeReadSlot zeSigma Env.nil).n = 7 := rfl

/-! ## 7. The closing theorem over fetched bytes -/

/-- **TABLE-STORE CORRECTNESS OVER FETCHED BYTES.** For a lowered
    store, the fetched byte run from a code region holding the bytes
    reaches the end of the code in a state representing the real
    `execStmt` outcome, with the environment: the chunk correctness
    (`senkSchreiben_korrekt`: value lowering, `repOk`/`RepSlot`, the
    `worldRep_store` frame) lifted to bytes by `lauf_zu_laufBytes`. -/
theorem tabellen_schreiben_laufBytes (A : TabAnker D) (c : PipeCfg)
    (hc : cfgOk c = true) (hsep : ankerSepB A = true)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (s : Stmt D V l Γ Λ Λ)
    (ρ : Env D Γ) (σ : World D) (st : Zustand)
    (hE : EnvRepr ρ st.register (abbOf c)) (hW : WorldRep (tabLayout A) st.speicher σ)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (flat pre post : List Byte) (p : List Befehl)
    (h : senkSchreiben A c s = some p) (hgp : p.all gerade = true)
    (hcode : CodeAt st.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll p ++ post)
    (hrip : st.rip = addrOff (natAdresse c.codeBase) pre.length) :
    ∃ n s' σ', laufBytes n st = .weiter s' ∧
      s'.rip = addrOff (natAdresse c.codeBase) (pre.length + (encodeAll p).length) ∧
      execStmt O passes R s σ ρ = .ok σ' ρ ∧
      WorldRep (tabLayout A) s'.speicher σ' ∧ EnvRepr ρ s'.register (abbOf c) := by
  obtain ⟨s1, σ', hrun1, hsrc, hW1, hE1⟩ :=
    senkSchreiben_korrekt A c hc hsep s ρ σ st hE hW O passes R p h
  obtain ⟨hb, hr, -, -, -⟩ :=
    lauf_zu_laufBytes (natAdresse c.codeBase) flat p pre post st s1 hgp hrun1 hcode hf hrip
  exact ⟨p.length, s1, σ', hb, hr, hsrc, hW1, hE1⟩
