/-
  File:      Grammatik/Speichermodell/Atomar.lean
  Subject:   UNGUARDED ATOMIC COMMUNICATION OVER MACHINE W -- the MEMORY half of OFFEN O25
             (Opus lane O25, 2026-09-26). Standalone: `Zielsatz/Spec.lean` does not import
             this file, and no premise or leg of the goal theorem changes here.

  THE QUESTION. The DRF theorem of `DRF.lean` (`schwach_ist_g`) holds BY EXCLUSION: the
  checker's footprint component (`FussS`) demands that every carrier a thread's graph reads is
  thread-local or lock-guarded -- `atomic` carriers included. So a flag, a spin, a counter read
  by a monitor thread and the fold of a per-core accumulator are refused, and W's non-SC
  outcomes never occur on an accepted program. What happens when the refusal is lifted for
  ATOMIC carriers only?

  THE ANSWER PROVED HERE (`schwach_ist_gA`, `ga_aus_w`): on every program whose footprints
  satisfy `FussSA` -- `FussS` with ONE more disjunct, "the carrier is an `atomic` global"
  (`AtomarAusgenommen`) -- machine W still reads the NEWEST message at every NON-atomic
  carrier, so a W step is a step of G on a memory that agrees with G's at every plain carrier
  and differs, if at all, at atomic carriers only. Those steps form MACHINE GA
  (`RufSchrittGA`): G whose ATOMIC reads may be answered by any value -- the "havoc at an
  atomic read" that OFFEN O25 names as the rely. So:
  * plain carriers stay SEQUENTIALLY CONSISTENT (the DRF theorem, now with racing atomics);
  * atomic reads are answered per W: coherent (`schrittW_kohaerent`) and with release/acquire
    views (`schrittW_erwerb`, and here `schrittW_freigabe`, `hb_uebergabe`: a release write
    carries the writer's view, an acquire read of it hands that view on, and every later read
    of the reader returns a message at or above it -- the happens-before hand-off of a
    `publishes`/`awaits` pair);
  * the thread-local invariants of G hold on every GA run -- the trace invariant `SpurInv`
    (memory safety of the trace), the frame read bound `OrteInvG`, the feature invariant
    `MerkInvG` and lock EXCLUSIVITY (`gaInv_*`): none of them reads memory.
  Every G run is a GA run (`ga_aus_g`) and `FussS` implies `FussSA` (`fussSA_of_fussS`), so
  every program `schwach_ist_g` covers is covered here, with the stronger conclusion there.

  WHAT IS NOT HERE (and why O25 stays open, narrowed -- `messung/OPUS-O25-ATOMICS.md`):
  the CONTRACT legs of `Ziel` (`VertragAmOrtG`, `SperrInvG`, `InvAmOrtG`, ...) come from the
  REPLAY of the user's sequential proof (`execEndH`, `KoerperGutS`) into G. On a GA run a
  thread reads an atomic value its sequential world does not have; covering that needs the
  sequential semantics to answer a shared atomic read with ANY value of its type (a havoc at
  the read, beside the one `Umwelt` makes at a lock take) and every residue lemma of the
  replay (`ZielOrt*`, `Sperre*`, some 30 000 lines) to carry it. This file gives the replay
  its MEMORY premise -- what a GA step presents -- and nothing more.
-/
module

public import Grammatik.Speichermodell.Atomar.Atomar.Teil1
public import Grammatik.Speichermodell.Atomar.Atomar.Teil2
public import Grammatik.Speichermodell.Atomar.Atomar.Teil3
