# MUSE-REPORT-289: Disjoint byte-memory commutation

## Task
Lane 289: generic commutation of successful `write64` operations at disjoint
footprints over the actual canonical `Speicher`, preservation of `read64`
outcomes under unrelated writes, a source-independent stable-footprint
condition for private spill/ownership optimisation, and a concrete reached
two-store witness. Reuse `read64`/`write64`/`Disjunkt`/`addrOff`; no copies.

## What was done
New file `grammatik/Grammatik/X86/SpeicherKommutation.lean`
(+1 additive umbrella import line in `grammatik/Grammatik.lean`).
Nothing else touched: no canonical `Typen`/`Speicher` edits, no Rust, no
numbers, no central docs.

Definitions:
- `StabilFuss m a snap`: footprint bytes match the snapshot AND the
  footprint stays readable and writable (spill-slot contract, no
  ownership/publication/lock premise by design).
- `zweiSpeicher0`, `zweiWertV` (`0x0102030405060708`), `zweiWertW`
  (`0x1112131415161718`), `zweiNachA/B/AB/BA` (the four reached states).

Theorems (every premise used; `decide` only on concrete probes):
- `mem_Fuss_iff`: footprint membership as `∃ k : Fin 8`.
- `write64_trifft`: a successful store places the word's bytes.
- `schreibbar8_aus_write64`: success proves writability.
- `disjunkt_symm`: `Disjunkt` symmetry.
- `write64_kommutiert`: two successful stores at disjoint footprints
  commute byte-extensionally (`∀ x`), and all six permission fields on both
  orders still read as the pre-state (permissions independent).
- `read64_erst_bleibt`: an already-read value survives a disjoint store.
- `read64_nach_zwei_fremd`: a read survives two stores disjoint from it.
- `stabilFuss_nach_schreiben`: a store establishes `StabilFuss`.
- `stabilFuss_bleibt`: `StabilFuss` survives a disjoint store.
- `stabilFuss_liest`: `StabilFuss` reloads `bytesWort snap`, stays writable.
- `zweiByteV/W`, `zweiDisjunkt` (via `disjunkt_von_intervallen`, `0`/`16`),
  `zweiSchrittA/B/AB/BA` (all four orders reach `some`),
  `zweiWechseltA/B` (both footprints observably change `0x00`->`0x08`/`0x18`).
- `write64_kommutiert_zeuge`: joint witness instantiating EVERY premise of
  `write64_kommutiert` with both change facts and both-orders agreement.

## Verification
- `./lean-probe grammatik/Grammatik/X86/SpeicherKommutation.lean`:
  0 errors; every `#print axioms` is a subset of
  `[propext, Classical.choice, Quot.sound]` (most use only
  `propext`/`Quot.sound`; several depend on no axioms at all).
- `./lean-bau`: exit 0, 369 jobs, "Build completed successfully", 0 errors.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file.

## Findings during the work (for other lanes)
1. Lean's `{ s with field := value }` struct-update syntax does NOT accept
   a newline between `:=` and the value ("unexpected identifier; expected
   '}'"). Long updates must stay on one line (or parenthesise the value).
2. `rw [if_pos rfl]` fails on `if (c = true) then .. else ..` goals: the
   bare `rfl` does not unify with the condition. Use an explicit
   `have hc : c = true := rfl` first (as canonical `Speicher.lean` does).
3. `rw` does not auto-close `≠` goals or goals needing delta-unfolding of a
   `def` state: append an explicit `rfl` / `decide` step.

## What remains open (CUTS, also in the file)
- Sequential target-memory commutation only; no atomicity/tearing/TSO
  refinement (bridge lane's business).
- OPEN and never concluded from disjointness: publication, foreign
  readers, locks, thread-privacy, ownership.
- No decoder/encoder/instruction semantics/ABI/cost/source correspondence.
- Commutation proved for 64-bit `read64`/`write64` only, not the 1/2/4-byte
  or width-indexed forms (same `writeBytesN` shape, not stated).

## Task assessment
Nothing in the task statement looks wrong. The inhabitation requirement is
met at the target level (real operand/memory probes, both footprints change);
no source-syntax premises exist here, so no `_zeuge` over tables was needed.
