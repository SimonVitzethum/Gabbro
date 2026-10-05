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
