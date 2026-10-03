# MUSE-REPORT-1005: Exact review of author 855 (loader-bias closing)

Lane 1005, clone `/home/simon/Dokumente/gabbro-muse/a1005`, branch `muse/1005`
(verified: `git rev-parse HEAD` = `b040b155159f47629542b0083e2f0a8a607f2b4c`,
matching snapshot `base`; branch `muse/1005`).
Report-only review: I own only this file. No source, no live controls, no
Lean/Rust changes in this clone.

## CANDIDATE / VERDICT

CANDIDATE: 855 ee4d636541703a413a6b285b5e6f0aff7b3df6a5

VERDICT: ACCEPT

Bounded acceptance: the candidate closes exactly what it claims — one
file-offset/virtual-address/bias/operand site through the checked step
`loaderBiasOk` to the executed `call32` target — with a generic connection
theorem, a joint non-degenerate witness with a reached memory-changing run,
planted refusals, and precise CUTS naming the remaining owners. No repairs
required. Not claimed and not granted: source correspondence, silicon
correspondence, whole-binary validation, TSO/GX bridge, abs64/rel8/data-field
site classes, termination.

## What was reviewed

Snapshot `.tmp/review/author-855/` (pinned HEAD, base, 3 files), `OWNER-TASK.md`,
`MUSE-REPORT-855.md`, `BUILD-EVIDENCE.json`, full text of
`grammatik/Grammatik/X86/ComposeLoaderBias.lean` (431 lines), the one-line
`Grammatik.lean` diff (`import Grammatik.X86.ComposeLoaderBias`, line 514,
append-only), and every reused producer by name in this clone at the snapshot
base. Local Intel reference
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt` line 43355
(`E8 cd CALL rel32, displacement relative to next`) confirms the next-RIP
equation the candidate threads through `patchSite_ziel`.

New definitions/theorems by the author (none added by this reviewer):
`loaderBiasOk`, `loaderBiasOk_wohlgeformt`, `loaderBiasOk_site`,
`loaderBiasOk_transfer`, `ComposeLoaderBias_verbindung`,
`loaderBias_disp_aussen`, `loaderBias_loch_verweigert`, witness image
`lbCode/lbZielSec/lbStapel/lbDatei/lbBild`, `lbSite`, `lbD`, acceptance facts
`lb_wohlgeformt/lb_patch/lb_transfer/lb_ok/lb_mem/lb_bias/lb_site/lb_find/
lb_backed/lb_b0..lb_b4/lb_disp/lb_gleich/lb_fit/lb_next/lb_ziel`,
`lbReg/lbZustand`, `lb_call_speichert`, `lb_loch`, `lb_disp_verweigert`,
`ComposeLoaderBias_verbindung_zeuge`.

## Evidence

- Mechanical hygiene: grep over the candidate file finds no `sorry`, `admit`,
  `axiom` declaration, `native_decide`, `unsafe`, `intro _` or `have _ :=`
  (only the substring "admit" inside English "admits/admitted" in comments).
  Every premise of `ComposeLoaderBias_verbindung` (16) is used in its proof;
  no premise has type `Prop`; no conclusion restates a premise. `hgleich` is
  carried as an explicit premise though implied by `hok`; that is redundancy,
  not weakening, and the witness instantiates it jointly (`lb_gleich`).
- Producer reuse, all confirmed present with matching signatures at base:
  `Bild.wohlgeformt/abteilFinden/dateiByte/ladenByte/effBias/geladen/wxOk`,
  `LoadedExecution.wohlgeformt_wx/wohlgeformt_ausr`,
  `Relokation.rel32Passt`, `BranchLayout.dispSigned`,
  `RelocatedExecution.PatchSite/siteStart/siteNext/patchSiteOk/
  patchSiteOk_disp_aussen/patchSite_ziel/bildSite_ruf_dekode/fenster5/
  relocBytes/relocLen/RelocArt/siteArtOk/aussen_verweigert/innen_verweigert`,
  `ValidatorSkeleton.transferOk`, `Byteschritt.byteschritt/ausgangByte/
  ausgangRip/witnessFlags`, `Codec.natByte`, `ControlFlow.direktZiel`.
  The zeuge reuses `aussen_verweigert`/`innen_verweigert` at exactly their
  stated types; nothing is re-proved, no second loader/decoder/executor/ISA.
- Byte arithmetic checked by hand: `call +4091` at `0x1000`:
  `0x1000 + 5 + 4091 = 0x2000` (listed target); `4091 = 0x0FFB`, LE bytes
  `FB 0F 00 00`, matching `lbDatei`. Stack: `rsp = 0x3008`, 8-byte push of
  `0x1005` lands low byte `5` at `0x3000` (zero before), inside writable
  non-executable `lbStapel` (`0x3000`, len 8); `rip` lands on `0x2000`.
  `rel32Passt 4091 = true`; `dispSigned` two's-complement reads `4091`.
  File extents (`0+5`, `5+8`, `13+3 <= 16`), disjoint sections, entry in code:
  consistent with `lb_wohlgeformt` by `decide`.
- Architecture: `E8` form, next-RIP-relative target, 5-byte length, push
  width, and stack-slot effect all agree with the local Intel reference;
  `siteStart = bias + vaddr + off` never equates file offsets to virtual
  addresses directly. Single-step `byteschritt` over `geladen` memory (not a
  hand-fed `schritt`); refusal is absence of a successful transition with an
  explicit no-termination-claim CUT. No flag/MXCSR/feature/interrupt gate is
  touched by this form and none is claimed. No TSO/concurrency content; the
  bridge stays with lanes 567/573-574 by name.
- Witness quality: three-section image (code + listed executable target +
  writable stack — the non-degenerate case), joint instantiation of all 16
  premises plus `lb_ok`, the reached memory-changing run
  (`lb_call_speichert`: byte `5` stored, zero before, `rip = 0x2000`), and 4
  planted refusals in the zeuge (out-of-range site, interior target,
  unlisted transfer `0x1800`, composed-step refusal). Negative mutations also
  exist as standalone theorems (`lb_loch`, `lb_disp_verweigert`).
- Build evidence is genuine: `BUILD-EVIDENCE.json` shows real iteration
  (an intermediate 4-error `write64`-unfolding attempt, matching the report's
  process note, then green), final `./lean-probe` 0 errors with
  `ComposeLoaderBias_verbindung[_zeuge]` on `[propext, Classical.choice,
  Quot.sound]` and projections/refusals on `[propext]`, and `./lean-bau`
  `Build completed successfully (511 jobs)`. Staged files were exactly the
  two owned Lean paths plus the report.
- Scope: no diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, friend-reserved optimiser files
  untouched. `gabbro_ziel` files untouched; the author honestly notes the
  `#print axioms gabbro_ziel` line was not re-run (classifier-blocked) and
  defers to the merge gate — acceptable, and I did not re-run it either
  (no Lean files touched in this clone; see below).

## What remains open

With the candidate (per its CUTS, which I endorse as accurate): source
correspondence, silicon/hardware correspondence, whole-binary/multi-site
theorems, patched-site re-decoding beyond the one call site (owner: rel32
lane 561 via `patchSiteOk`), data-field/abs64/rel8 classes (extension codec
lanes), TSO/GX bridge (lanes 567/573-574), termination. Nothing of this is
claimed by the candidate.

## Review method and build note

No `./lean-bau` was run in this clone: as a report-only reviewer I added no
Lean files, so there is nothing new to build here; verification is by exact
snapshot inspection, producer signature cross-checks at the snapshot base,
hand-checked byte/address arithmetic, and the candidate's build evidence
(which shows a real red-to-green iteration, not a pasted green). No queued
wrapper reproduction was needed: no suspicious case survived the static
checks. The merge gate's source build, axiom, and emission checks remain
authoritative at integration.

## Task remarks

Nothing in the owner task proved wrong. The ZEUGE requirement (joint,
non-degenerate, memory-changing reached run) is met in full, including the
composition-specific demand that a conjunction of checks is not counted as
execution.
