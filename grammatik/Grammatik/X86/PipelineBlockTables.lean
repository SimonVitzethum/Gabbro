/-
  File:      Grammatik/X86/PipelineBlockTables.lean
  Subject:   Block-level table READS with scaled-index addressing for the
             direct pipeline: follow-up of lane 1159 (`PipelineTables.lean`).

             Lane 1159 lowers constant-index reads/writes (absolute address
             materialisation) and block-level WRITES. What it does NOT cover:
             reads inside blocks (`Block.bind`/`assignVar` consumers) and
             variable indices (no scaled addressing in the pilot). This file
             provides both WITHOUT editing existing files: a `senkBlock`-style
             block lowering for `assignVar`-of-table-read statements with a
             VARIABLE index, where the address `B + k * Z + O` is computed at
             run time with pilot adds (scale doubling for `Z` in 1/2/4/8,
             checked by the reused `skalaOk`), plus the correctness theorem
             over fetched bytes and refusal theorems for every unsupported
             shape. Rust is out of scope.

  Reused, not duplicated:
    - anchor/layout/world: `TabAnker`, `ankerBasis/Zeile`, `feldOff`,
      `feldAdr`, `feldAdr_some`, `feldAdr_kein_oob`, `idxOk_toNat`,
      `tabLayout`, `ankerSepB`, `ankerSep_sound`, `tabWorldRep`,
      `WorldRep`, `LayoutSep` (`PipelineTables.lean`, lane 1159);
    - pipeline: `PipeCfg`, `cfgOk`, `cfgOk_frei/regs`, `abbOf`,
      `EnvRepr`, `envRepr_fremd`, `CodeAt`, `kanon`, `encodeAll`,
      `gerade`, `lauf_zu_laufBytes`, `laufBytes_add`, `Entspricht`,
      `worldRep_lese`, `repOk_int`, `natAdresse_ohneUmbruch/toNat`
      (`Pipeline.lean`); `intWort_add`, `lauf_anhang`,
      `lauf_einzeln_gleich` (`ExpressionLowering.lean`);
    - addresses: `skaliertAddr` (`EffectiveAddress.lean`); `skalaOk`,
      `basisKeinForm`, `adrOk` (`AddressEncoding.lean`);
    - machine: `schritt_movImm64/movReg64/addReg64/load64_erfolg`,
      `schrittRegister`, `regSet_gleich/fremd`,
      `schrittRegister_speicher` (`Ausfuehrung.lean`); `effAddr_null`
      (`EffectiveAddress.lean`); `intWort`, `natAdresse`, `read64`.
  No second IR, no second source interpreter, no per-program rule.
-/
import Grammatik.X86.PipelineTables
import Grammatik.X86.ExpressionLowering
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.X86.SourceMemory

namespace Gabbro.Grammatik.X86.PipelineBlockTables

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineTables

variable {D : Deklaration}

/-- Doubling count for an admitted SIB scale: `Z = 2 ^ skalExp Z`. -/
def skalExp : Nat → Nat
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | _ => 0

/- CUTS:
   Skeleton only: scale exponent stub. The chunk, lowering, correctness,
   refusals and witnesses are OPEN.
-/
