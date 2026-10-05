/-
  File:      Grammatik/X86/PipelineWorkPath.lean
  Subject:   Taken-path work and per-round loop correspondence over the
             direct pipeline lowering (lane 1259).

  Follow-up of `PipelineWork.lean`: its `Deckung` counts the STATIC
  whole-list length and its dynamic-path bound is arithmetic only, not
  connected to a taken-path `lauf` prefix; loop work stops at the
  labelled-step budget. This file connects the taken-path bound to the
  executed `lauf` prefix of the byte-level run, and proves the
  per-round loop body correspondence and the labelled-to-bytes leg
  with `PipelineLoops.lean`.

  Reused, not duplicated: `Pipeline.lauf_zu_laufBytes`/`gerade`/`kanon`/
  `encodeAll`/`CodeAt`, `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`,
  `PipelineWork.pipeSummary`/`pipeSummary_expand`/`senkStmt_flach_laenge`/
  `PipePaket`, `PipelineLoops.schleifeProg`/`schleifeSchritte`/
  `schleife_korrekt_endlich`/`schleife_bytes`/`relax_laufBytes`,
  the actual `lauf`/`laufBytes`/`laufL`/`laufBytesI` runs. No second IR,
  no second source interpreter, no new cost model. Unsupported shapes
  are REFUSED, never guessed. Rust is out of scope.
-/
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineLoops
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86.PipelineWorkPath

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineWitnesses

/-! ## 1. Taken-path work: the executed prefix length.

    The taken-path work of a byte-level run is the length of the
    instruction prefix it actually retires -- never the static
    whole-list length. -/

/-- TAKEN-PATH WORK: the retired count of the executed prefix. -/
def genommenArbeit (T : List Befehl) : Nat := T.length

/- CUTS:
   - Skeleton only: `genommenArbeit` names the taken-path count.
   - OPEN: the prefix-run bridge (`laufBytes_genommen`), the dynamic
     `Deckung` producer, the per-round loop correspondence
     (`runde_einzel`), the labelled-to-bytes leg
     (`schleife_pfad_bytes`), refusals, gifts and joint witnesses.
-/

#print axioms genommenArbeit

end Gabbro.Grammatik.X86.PipelineWorkPath
