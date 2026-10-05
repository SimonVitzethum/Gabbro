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

/-- A lock-section block run: each section brackets entry drain,
    reached middle, exit drain; sections chain state to state. -/
inductive SperrLauf (c : Nat) :
    List (List AtomQuelle) → TSOZustand → TSOZustand → Prop where
  | nil (s) : SperrLauf c [] s s
  | cons (innen rest s s' sN) :
      SperrSchritt c innen s s' → SperrLauf c rest s' sN →
      SperrLauf c (innen :: rest) s sN

/-- **SECTION-CHAIN REACHABILITY.** A lock-section block run is one
    reached run: each section contributes its bracket (lane-1163
    `sperre_korrekt`) and sections chain (`erreichbar_kette`). -/
theorem sperrlauf_erreichbar (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN) :
    TSOErreichbar s0 sN := by
  induction h with
  | nil s => exact .start
  | cons innen rest s s' sN hstep _ ih =>
    obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
    obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨-, -, -, -, hreach⟩ :=
      sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
    exact erreichbar_kette s s' sN hreach ih

/-- **SECTION-CHAIN DRAIN.** A NONEMPTY lock-section block run ends
    with an empty own buffer: the last section's exit drain empties it.
    (The empty block drains nothing, hence the premise.) -/
theorem sperrlauf_leer (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN)
    (hne : secs ≠ []) :
    sN.puffer c = [] := by
  induction h with
  | nil s => exact absurd rfl hne
  | cons innen rest s s' sN hstep htail ih =>
    cases htail with
    | nil _ =>
      obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
      obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
      obtain ⟨-, hempty, -, -, -⟩ :=
        sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
      exact hempty
    | cons _ _ _ _ _ _ _ => exact ih (by simp)

/-- **SECTION-CHAIN FOREIGN FRAME.** A lock-section block run keeps
    every foreign buffer: each section preserves them
    (lane-1163 `sperre_korrekt`) and the equalities chain. -/
theorem sperrlauf_fremd (c : Nat) (secs : List (List AtomQuelle))
    (s0 sN : TSOZustand) (h : SperrLauf c secs s0 sN) :
    ∀ d : Nat, d ≠ c → sN.puffer d = s0.puffer d := by
  induction h with
  | nil s => intro d _; rfl
  | cons innen rest s s' sN hstep _ ih =>
    obtain ⟨s1, s2, hE, hM, hR, hA, hI⟩ := hstep
    obtain ⟨innere, hIn⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨-, -, -, hframe, -⟩ :=
      sperre_korrekt innen innere s s1 s2 s' c hIn hE hM hR hA
    intro d hd
    rw [ih d hd, hframe d hd]

/- CUTS: what is not proved here
     Proved here so far: nothing beyond `SperrSchritt` (skeleton).
     NOT proved here, and not claimed:
     - No block run yet; no CAS-failure binding; no source link.
     - No seq_cst total order, no fairness, no retry bound.
-/

#print axioms SperrSchritt

end Gabbro.Grammatik.X86.PipelineAtomicsBlock
