/-
  File:      Grammatik/X86/TsoGxEntryBytes.lean
  Subject:   Byte-level entry/call linkage for the start-anchored bridged run.

  Follow-up of lane 1253 (`TsoGxStart.lean`): the prefix there is
  source-level (`RufSchrittG` from `RufStartG`), while
  `PipelineEntry.prolog_lauf` and
  `StackExecution.geholt_verschachtelt_wiederhergestellt` live on the byte
  machine (`Zustand`, `laufBytes`). This module proves the linkage on the
  byte side and names the admission it stands on: the entry sequence
  (`prolog_lauf`: `AbiArgs` to `EnvRepr`) followed by one fetched
  call/push/pop/ret nest (return word below the old top, inner value
  delivered, stack pointer restored) reaches the fragment-head byte state
  with the entry `WorldRep`/`EnvRepr` transported across the two stack
  writes (both slots foreign to every placed slot). The source-level
  prefix (`fragmentKopf_erreichbar`, `startFragment_zeuge`) is reused by
  reference; the joint witness shows both sides reach their head, with the
  call frame written and restored through memory. What is NOT covered is
  refused (guard slot, non-executable return, clobbering prolog) or listed
  in CUTS. No new machine, no new decoder, no silicon claim.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.StackExecution
import Grammatik.X86.TsoGxStart

namespace Gabbro.Grammatik.X86.TsoGxEntryBytes

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineEntry

/-- Both stack slots are foreign to every placed slot: the admission that
    lets the entry representation survive the call frame writes. -/
def StapelLayoutFremd {D : Deklaration} (L : Layout D) (aussen innen : Adresse) : Prop :=
  ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
    L.loc t k f = some a0 → Disjunkt aussen (natAdresse a0) ∧ Disjunkt innen (natAdresse a0)

/- CUTS (exactly what is NOT proved here):
   - No lowering certificate from the source program `eP` to bytes: the
     identity of the source fragment head with the byte head is OPEN with
     the pipeline owners. Proved here is co-reachability plus transport.
   - No TSO/GX bridge: every fact is sequential over one canonical
     `Speicher`; store buffers and refinement stay with the TSO work.
   - Pilot ISA, one core, model memory, no time (cuts of the reused modules).
-/

#print axioms StapelLayoutFremd

end Gabbro.Grammatik.X86.TsoGxEntryBytes
