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
