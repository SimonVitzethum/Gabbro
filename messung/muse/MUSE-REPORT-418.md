# MUSE-REPORT-418: Continuous Lean proof reserve — BitScan

Lane 418, branch `muse/418`, clone `/home/simon/Dokumente/gabbro-muse/a418`.
Owned files only: `grammatik/Grammatik/X86/BitScan.lean`,
`grammatik/Grammatik.lean` (one additive import), this report.

## What was delivered

New module `grammatik/Grammatik/X86/BitScan.lean` (444 lines): zero-aware
bit-scan helpers over the canonical fixed-width word, for the future
performance profile's bit-test/loop lowering. No new word/register/state
types, no `Befehl` form, no `schritt` change, no native-form claim.

- **Defs (8):** `bitGesetzt` (set bit of `trunc b w`, reuses `Wort.trunc`),
  `bsfVon`/`bsfIdx` (ascending fuel search, least index, `none` on zero),
  `bsrVon`/`bsrIdx` (descending fuel search, greatest index, `none` on zero),
  `scanZF` (zero flag: `decide (trunc b w = 0)`), `BsfGueltig`/`BsrGueltig`
  (validity shapes a future native form must present), `scanSondenSpeicherNach`.
- **Correctness (2+6):** `bsfVon_korrekt`, `bsrVon_korrekt` — one induction
  each proving range ∧ set-bit ∧ extremality jointly; `bsfVon_schranke`,
  `bsfVon_bit`, `bsfVon_min`, `bsrVon_schranke`, `bsrVon_bit`, `bsrVon_max`
  are tactic-free projections. `bsfVon_alle_null`, `bsrVon_alle_null`
  (no bit in interval → no hit) are proved and kept as the admission-check
  shape; the zero snapshots use direct per-width evaluation instead.
- **Zero behaviour (6):** `bsfIdx_null_ist_none`, `bsrIdx_null_ist_none`
  (zero → `none` at every width, by `cases b <;> decide`; never a fabricated
  `some 0`), `bsfIdx_some_nichtnull`, `bsrIdx_some_nichtnull` (an index
  proves nonzero), `scanZF_heisst`, `scanZF_null_kein_index`,
  `scanZF_index_nichtnull`, plus `bsfIdx_gueltig`, `bsrIdx_gueltig`.
- **Probes (6, all `decide`):** `probe_bsf_eins`, `probe_bsf_hoch`
  (`0x80..00` → 63), `probe_bsf_null` (zero → none/none/flag),
  `probe_bsf_schmal_ignoriert_hoch` (`0x100` at `.b8` → none: bit 8 is
  outside the operand, fixed-width evidence), `probe_bsr_schmal`
  (`0x81` → 0/7), `probe_bsf_mitte` (`0x10` → 4).
- **Memory witness (1):** `bitscan_speicher_zeuge` — scanned index `4` of
  `0x10` through permission-checked `write64`/`read64` on `zeugenSpeicher`,
  with observable byte change; value, flag and memory change pinned jointly
  on a nonzero word.
- **Hygiene:** no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no
  `Prop`-typed premise, no `intro _`/`have _ :=` discards, every premise used
  (checked by hand over all 34 theorems), English only, `CUTS` block present,
  `#print axioms` for every main theorem. All names are new to the tree
  (collision grep clean). No source-syntax premises → no `_zeuge` required
  by rule 13; the §4 probes + §5 witness are the concrete zero/nonzero
  boundary witnesses the task asks for.

## Check results (exact lines)

- `./lean-probe grammatik/Grammatik/X86/BitScan.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0` (verified 4×, last after
  every edit). Every `#print axioms` reports `[propext, Quot.sound]`
  (subset of the `gabbro_ziel` standard set; `breite_bits_pos` axiom-free).
- `grammatik/.lake/build/lib/lean/Grammatik/X86/BitScan.olean` built by
  `./lean-bau` at 14:57 (460552 bytes) — the module itself compiles in-tree.
- `./lean-bau` full-tree result: **red only at target `Grammatik`**
  (the 395-import umbrella): `Lean exited with code 134`,
  `failed to create thread`. Proven environmental, not caused by this lane:
  with my one-line import stashed, the **pristine umbrella crashes
  identically**; lane 350's independent log shows the same crash on
  `AtomicPayload` in the main checkout. Sibling big modules (`MulDiv`,
  `ShiftLogic`, `Wort`) probe green right now. The umbrella olean never
  existed in this clone.
- `gabbro_ziel` axiom re-check via full build: blocked by the same
  environmental failure (goal modules themselves replay green; the added
  file contributes no axioms).

## Repair attempt after the integration gate failure (no merge)

The integration gate failed with `RuntimeError: Lean merge build failed`.
Its own log exonerates this lane's module and repeats the environmental
failure:

- In the merge build, `Grammatik/X86/BitScan.lean` elaborated **successfully**:
  all 7 probe `#print axioms` lines printed
  (`probe_bsf_eins` … `bitscan_speicher_zeuge`, each `[propext, Quot.sound]`).
- The failure is again exactly one step: `[397/398] Building Grammatik`
  (the ~400-import umbrella) with
  `failed to create thread`, `Lean exited with code 134` — the same crash
  the pristine umbrella (my import stashed) shows in this clone, and the
  same crash lane 350 logged on an unrelated module.

Local re-verification on this repair turn (no code change, nothing to
repair): `./lean-probe grammatik/Grammatik/X86/BitScan.lean` →
`== 0 error(s) …; exit 0`; `./lean-bau` → still red only at `Grammatik`
with the identical thread-creation crash. The owned diff (new module + one
additive import line, 460 KB olean that builds) cannot reduce the
umbrella's import-loading cost, and rule 5 forbids restructuring the
umbrella, so no owned-file change can address the gate failure.

Concrete blocker for the merger/integration owner: the build host cannot
elaborate the full `Grammatik` umbrella under current machine load
(thread creation fails while loading ~400 oleans), independent of this
lane's change. Retrying the merge build at a quieter moment, or relieving
host memory/thread pressure, is the only remedy on this evidence. This
report change alters the commit hash, so a fresh independent review is
required; the Lean content is byte-identical to the reviewed candidate.

## Second repair turn (same gate failure, same evidence)

The integration gate failed again with a byte-identical log: all 7
`BitScan` probe axiom lines print in the merge build, then `[397/398]
Building Grammatik` aborts with `failed to create thread` (exit 134).
Local re-verification this turn: module probe green (`exit 0`),
`./lean-bau` still red only at the umbrella target. No owned-file change
exists that addresses a host-side thread-creation failure hitting the
pristine tree identically; Lean content unchanged since the accepted
candidate, only this report entry is new, so fresh review is required
again. No acceptance of the full source/binary chain is claimed.

## What remains open (also in CUTS)

- Full `./lean-bau` green + `gabbro_ziel` axiom gate: needs a machine-level
  retry by the merger; nothing in this lane's diff can fix a thread-creation
  failure that hits the pristine tree identically.
- Totality on nonzero operands (`trunc ≠ 0 → ∃ i, scan = some i`) is NOT
  proved (only zero → none and some → nonzero); a consumer needing the
  defined-when direction must prove it or keep the refusal.
- No `Befehl` wiring, decoder/image bytes, TSO bridge, source lowering, cost
  transfer, or silicon verification — the helpers are stated executable
  semantics; `BsfGueltig`/`BsrGueltig` name the evidence a future native
  form (BSF/BSR/TZCNT/LZCNT) must present.
- Only ZF is modelled; all other flags of a future form stay unconstrained.

## Notes on the task / findings

- The task asks for "returned index range and bit/minimality" — delivered as
  the joint `*_korrekt` lemmas with projection API, so there is exactly one
  induction per direction rather than three.
- Two genuine proof bugs were found and fixed along the way (both would have
  been Lean errors, not crashes): `cases h` on `some s = some i` substitutes
  in an unpredictable direction (replaced by `injection`+`subst` with
  name-independent closers), and an over-applied induction hypothesis in the
  minimality/maximality branches.
- Early `./lean-probe` runs printed `0 error(s)` while the process had in
  fact aborted (old wrapper format hid the crash); the current wrapper
  reports `exit 134` honestly. Intermediate "green" readings from the old
  format were re-verified after every edit — the final file is green under
  the honest wrapper, 4 consecutive clean runs.
- Nothing in the task statement looks wrong; the scope (helper + proofs +
  witnesses + explicit CUTS, no native/source/timing claims) was followed.

## Files changed

- `grammatik/Grammatik/X86/BitScan.lean`: new (skeleton committed as
  `7f7b0680`, full module in this commit).
- `grammatik/Grammatik.lean`: +1 line `import Grammatik.X86.BitScan`
  after `AccessList` (additive only).
- `.tmp/probe*.lean`, `.tmp/cum*.lean`, `.tmp/t*.lean`: private bisection
  scratch, removed before commit.
