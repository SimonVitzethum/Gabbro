# MUSE-REPORT-339: LockedOps (plan A5)

## What was done

New module `grammatik/Grammatik/X86/LockedOps.lean` (521 lines) plus one
additive import line at the end of `grammatik/Grammatik.lean`. No other file
touched. Implements WORK-ALLOCATION.md row A5 exactly as a target-side
extension, reusing canonical vocabulary only.

### New definitions

- `SperrBefehl`: `.xadd64 (addr : Adresse) (delta : Wort)` (single-op LOCK
  RMW, XADD shape) and `.mfence`. No other LOCK form exists.
- `LockEreignis`: per-event access record (`kern`, `lesen`, `schreiben`,
  `gelesen`, `geschrieben`, `istRmw`, `istZaun`), footprints reuse `Fuss`.
- `ausgerichtet8`: declared 8-alignment guard. Only the LOCK form demands
  it; ordinary (possibly unaligned) accesses are untouched.
- `lockSchritt`: RMW bypasses the acting core's buffer and operates on
  canonical memory via `read64`/`write64`, exactly when own buffer is empty,
  the word is readable/writable, and alignment holds; otherwise explicit
  `none`. Fence gates on the empty own buffer and changes no state
  (same gate as `zaunBereit`). No existing `Befehl` form is redefined;
  no second evaluator for the 14 pilot forms exists.
- `casSchritt`: success installs `neu` on match; mismatch returns the
  unchanged state with `false` (stutter, safety-only).
- `lockKosten` (one shape unit per locked op), `casKosten` (retries + 1),
  `RmwForm` (some event in the trace is a locked RMW).

### Theorems (every premise used; proofs use only canonical lemmas)

- `lockSchritt_xadd_erfolg`, `lockSchritt_mfence_erfolg`: step equations.
- `lock_xadd_atomar`: RMW event shape over the full word footprint,
  all three permission maps preserved, frame outside the footprint.
- `mfence_ordnung`: fence changes no byte and no buffer, event is
  fence-only, and afterwards no address forwards from the acting core,
  so later loads there observe canonical memory (full local barrier).
- `casSchritt_erfolg`, `casSchritt_fehlschlag` (equations),
  `cas_erfolg_schreibt` (observably moves the word, with read-back
  difference, permissions, frame), `cas_fehlschlag_stottert`
  (bytes and buffers unchanged).
- `einzel_lock_kosten_eins`: single LOCK op = constant SHAPE unit
  (explicitly not hardware time).
- `cas_schleife_unbeschraenkt`: `¬ ∃ K, ∀ n, casKosten n ≤ K` — proved
  unbounded retry, no constant bound claimed.
- `rmw_nur_mit_lock`: two non-RMW events never satisfy `RmwForm`.
- `kein_lock_nach_w`, `keine_lock_zyklus_schranke`: empty-type
  non-claims (no W/GX refinement here — bridge owns it; no cycle bound
  from the shape — needs named assumptions and transfer).

### Witnesses (joint, concrete, memory-changing)

- `locked_add_zwei_kerne`: core 0 locked-adds 5, core 1 locked-adds 7
  at `lockAddr` (4096, aligned, fully permitted); word moves 0 → 12,
  one RMW event per core (`lock_schritt1/2` by `rfl`,
  `lock_liest_fuenf/zwoelf` and `lock_speicher_aendert_sich` by `decide`).
- `lock_xadd_atomar_zeuge`: all premises of `lock_xadd_atomar` jointly
  on the concrete first step, plus the memory change.
- `mfence_ordnung_zeuge`: fence succeeds on core 0 while core 1 keeps a
  pending store (`zaunStart`, `zaun_schritt` by `rfl`) — a local fence
  drains no foreign buffer.
- `cas_erfolg_zeuge` (expecting 0 installs 9, read back 9),
  `cas_fehlschlag_zeuge` (expecting 5 against 0 stutters, by `rfl`).
- `rmw_nur_mit_lock_zeuge`: split load-then-store built from the REAL
  `zugriff` footprints of a genuine `load64`/`store64` pair
  (`splitLaden`, `splitSpeichern`) carries no RMW shape, for every
  pre-state — the planted refusal, proved concretely.

Note on rule 13: the module takes no premises over source syntax
(`Vertrag`/`Stmt`/…), so the table clause does not apply; the applicable
non-degeneracy (reached run with a memory-changing step) is met by the
two-step locked run above (byte 0 → 12 at `lockAddr`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/LockedOps.lean`:
  `0 error(s)`; all 19 `#print axioms` lines depend at most on
  `[propext, Quot.sound]` (subset of the goal axioms), two on no axioms.
  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- `./lean-bau`: `Build completed successfully (386 jobs)` (last line).
- `gabbro_ziel` probe (scratch file outside the repo, deleted after):
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged.
- No source/checker/Spec/goal/Rust/emitter/doc/friend file touched.

## What remains open (also listed in the file's CUTS block)

Full final-byte/source/hardware correspondence is OPEN: no W/GX
refinement, no silicon atomicity proof for aligned words, no cycle or
latency bound, no progress/fairness from CAS stutter, no XADD
flag/register/RIP effects (TSO state carries none — a lowering consumer
must carry them), no fetch/decode/ABI/image coupling, nothing about
source duties or `gabbro_ziel`. The fence order facts are local to the
new `mfence` step; B4's drain lemmas and the bridge remain the owners
of their sides — this module is built to be reused, not to preempt.

## Remarks on the task (nothing manufactured)

- "Single-LOCK-op = constant-cost shape" is implemented as a syntactic
  shape count (`lockKosten`, value 1), explicitly not a runtime bound;
  a hardware time claim would need named assumptions and transfer.
- "Failure-as-stutter is safety-only" is implemented literally:
  `cas_fehlschlag_stottert` proves only state preservation.
- One parser note: a `{ field := … }` structure literal in the `mfence`
  arm of `lockSchritt` failed to parse at the second comma while the
  identical shape in the `xadd64` arm parsed; I used the positional
  `⟨…⟩` constructor there (and kept it uniform afterwards). No semantic
  consequence.
- Commit for review: the skeleton commit `70c7c34e` plus the pending
  content commit of this report run (exact hash in the merge record).
  Reviewer: lane 377.
