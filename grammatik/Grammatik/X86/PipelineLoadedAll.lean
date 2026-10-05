/-
  File:      Grammatik/X86/PipelineLoadedAll.lean
  Subject:   Loaded-image correctness for the spill, call, table, float
              and work pipeline fragments (lane 1199).

  Follow-up of lanes 1161, 1165, 1189, 1191, 1159: their theorems run
  on constructed decodings or model code regions, not on the loaded
  image with relocations. Here each fragment family gets its
  `pipeline_correct_loaded`-shaped theorem over the checked mapping:
  the start state is the existing loader's state (`PipelineImage`
  `startZustand` over `ladung`, i.e. `geladen`), fetch runs through
  actual memory (`LoadedExecution`), W^X sits in the per-byte `CodeAt`
  (executable and not writable), and the relocation leg reuses the
  accepted `PipelineLink` patch frame plus re-decode. The block-level
  families (spill, work) share the one loaded-premise pattern
  (`imageOk`/`weltOk` projected to `CodeAt`/`LayoutSep`/`WorldRep`);
  chunk-level families (tables, calls) run from loaded memory with
  decided checks; floats honestly refuse the byte image (their
  correctness lives over `FpZustand`, never over bytes).

  Reused unchanged: `Pipeline` (`CodeAt`, `validate`,
  `pipeline_correct`, `lauf_zu_laufBytes`), `PipelineImage`
  (`startZustand`, `ladung`, `imageOk`, `weltOk`,
  `imageOk_codeAt/layoutSep/worldRep`, `codeAt_lauf`),
  `LoadedExecution` (`bildZustand`, `holeFetchAux_geladen`,
  `bildStore_schritt_speichert`), `PipelineLink`
  (`linkPatch_rahmen`, `verknuepft_rel32_schliesst`,
  witness patch/decode), `PipeSpill`, `PipelineCalls`,
  `PipelineCallsExec`, `PipelineTables`, `PipelineFloat`,
  `PipelineWork`, `PipelineWitnesses`. No second IR, no second
  source interpreter, no optimiser edit, no reserved file.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineImage
import Grammatik.X86.LoadedExecution
import Grammatik.X86.PipelineLink
import Grammatik.X86.PipelineSpill
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineCallsExec
import Grammatik.X86.PipelineTables
import Grammatik.X86.PipelineFloat
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineLoadedAll

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipeSpill
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineCallsExec
open Gabbro.Grammatik.X86.PipelineTables
open Gabbro.Grammatik.X86.PipelineFloat
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineWitnesses

/-- Loaded code, the one generic predicate every family below runs
    from: the loaded mapping holds the bytes at the code base,
    executable and not writable (W^X, per byte). -/
def fragmentBytesGeladen (bild : Bild) (c : PipeCfg) (bytes : List Byte) : Prop :=
  CodeAt (ladung bild) (natAdresse c.codeBase) bytes

/- CUTS (skeleton):
   Only the shared loaded-code predicate so far. Per-family
   correctness, refusals, probes and witnesses follow in pieces.
-/

#print axioms fragmentBytesGeladen

end Gabbro.Grammatik.X86.PipelineLoadedAll
