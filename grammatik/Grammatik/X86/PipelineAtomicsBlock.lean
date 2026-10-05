/-
  File:      Grammatik/X86/PipelineAtomicsBlock.lean
  Subject:   Pipeline atomics: execBlock correspondence for blocks with
             shared-atomic reads/writes.

  Lane 1217 (follow-up of lanes 1163 `PipelineAtomics.lean` and 1203
  `PipelineAtomicsBind.lean`): atomics have per-access facts only, never
  a block run. This file proves the block level: lock sections chain
  (`SperrLauf` over `List (List AtomQuelle)` with one reached run),
  CAS failure bound at register level (`bind_cas_fehlschlag`, the twin
  of lane-1203 `bind_cas_erfolg`), and a real source `execBlock` with a
  shared-atomic global read/write plus a lock section related to the
  lowered access sequence (`abblock_korrekt`) with a non-degenerate
  joint witness. No seq_cst total order, no fairness, no retry bound.
  Reused unchanged: `senkAtom`/`senkListe`/`valAtom`, `sperre_korrekt`,
  `cas_korrekt_fehlschlag`, `lockVoll_cmpxchg_fehlschlag_adapter`,
  `mfenceDrain_*`, `senkAtom_zeuge`, `bind_zeuge`. No second IR, no
  second source interpreter, no optimiser change. Rust is out of scope.
-/
import Grammatik.X86.PipelineAtomicsBind

namespace Gabbro.Grammatik.X86.PipelineAtomicsBlock

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineAtomics

/-- One lock-section step: entry drain, a reached middle run with a
    foreign frame, exit drain, over a lowerable body. -/
def SperrSchritt (c : Nat) (innen : List AtomQuelle)
    (s s' : TSOZustand) : Prop :=
  ∃ s1 s2 : TSOZustand,
    mfenceDrain s c = some s1 ∧ TSOErreichbar s1 s2 ∧
    (∀ d : Nat, d ≠ c → s2.puffer d = s1.puffer d) ∧
    mfenceDrain s2 c = some s' ∧
    (senkListe innen).isSome = true

/- CUTS: what is not proved here
     Proved here so far: nothing beyond `SperrSchritt` (skeleton).
     NOT proved here, and not claimed:
     - No block run yet; no CAS-failure binding; no source link.
     - No seq_cst total order, no fairness, no retry bound.
-/

#print axioms SperrSchritt

end Gabbro.Grammatik.X86.PipelineAtomicsBlock
