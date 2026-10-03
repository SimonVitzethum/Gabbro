# MUSE-REPORT-919: Exact review of author 769 (jump-table certificates)

## CANDIDATE

769 `97150eb9c1114488ac154db51855c8099da69c8a` (base `56537272a31df3de5d9b7898bbade91c3de817b8`, clean)

## VERDICT: ACCEPT (bounded)

Bounded acceptance: the candidate proves exactly what its CUTS block claims --
a validator-tracked jump-table certificate over the reused canonical
fetch/step vocabulary, with a joint reached witness and explicit refusals.
Full hardware correspondence, whole-image validation, the per-access
target-to-W/GX bridge, source/contract/cost/time claims and fault delivery
stay OPEN per its CUTS and are not accepted here.

## What was reviewed

Exact pinned snapshot `.tmp/review/author-769/` against task `OWNER-TASK.md`:
`grammatik/Grammatik/X86/JumpTableCert.lean` (601 lines),
`grammatik/Grammatik.lean` (import line only), `PATCH.diff` (3 files:
report, import, new file -- clean scope, no source/checker/Spec/goal/emitter
touch, no new diagnostic/gift/example/CLI numbers, no MARKE_EMIT change),
`MUSE-REPORT-769.md`, `BUILD-EVIDENCE.json`, and the official local
reference record `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
(Intel SDM 325462-093US, September 2026, sha-pinned; AMD snapshot
unavailable and not claimed -- consistent with the file's canonical-subset-only stance).

## Verification (independent, reproduced)

- `./lean-probe .tmp/review/author-769/grammatik/Grammatik/X86/JumpTableCert.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` -- reproduced twice on the
  exact snapshot bytes (probe resolves the base package imports; candidate
  file itself unmodified).
- `./lean-bau` on this clean base clone: `== exit 0; 0 error line(s) in the
  COMPLETE output`. Author's recorded candidate build: exit 0, 485 jobs.
- `#print axioms` (reproduced): every theorem within
  `{propext, Classical.choice, Quot.sound}`; the TARGET
  `JumpTableCert_verbindung` and companion `JumpTableCert_verbindung_zeuge`
  use only `[propext, Quot.sound]`; `Classical.choice` enters only via two
  reused adapter round-trip lemmas and is disclosed. No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` (grep: only benign `admitted`/`admits`
  substrings and `#print` lines); no `intro _` / `have _ :=` discards.
- Every reused interface name verified present in the base with matching
  shape: `jmpMemSchritt`, `jmpMemSchritt_erfolg`/`_verweigert`, `indSchritt`,
  `fetchInd`, `fetchInd_erfolg` (author's `.2.2.1` projection is the
  `laengeOk` conjunct -- correct), `indByteschritt`,
  `indByteschritt_weiter`, `indirektZielOk` + `indirektZielOk_garantiert`,
  `indAdapterDecode`, `indAdapter_indirekt`, `pilot_verweigert_indMem`,
  `roundtrip_indMem_jmp`, `far_erweiterung_verweigert`,
  `modus0_verweigert`, `zaehler_verweigert`, `adrKlasse_daten_gp`,
  `leseErfolg_kein_fehler`.

## Architecture (not just Lean green)

- Byte form: pinned `48 FF A0 00 00 00 00` (`REX.W FF /4`, mod=2, rax) by
  `decide` on `encodeIndMem`; dispatches through the common
  `indAdapterDecode` with proved pilot separation, no second decoder.
  Matches the cited SDM Vol.2A JMP r/m64 heading; provenance string names
  the local snapshot file.
- Widths/registers: 8-byte slots (`read64`), stride 8; rax base, disp32.
  Flags kept (no claim beyond preservation -- sound for JMP).
  No invented determinism over undefined state.
- Memory order/permissions: target word read from the pre-state before
  control moves (inherited from `jmpMemSchritt_erfolg`); slot read gated
  by `read64`/`lesbar8`, code by `fetchInd`/`ausfuehrbarN`; faulting slot
  observes `#PF` (pinned permitted member) with a no-speculation refusal
  reusing the accepted lemma.
- No-forge (M140 shape): `jtGeschmiedetB` proved both ways (genuine table
  words pass, foreign words refuse); certificate admission is DERIVED from
  `jtZertOk` via `jtZertOk_eintrag`, never assumed -- no desired-simulation
  premise.
- TSO: load-only framing only (buffer untouched, canonical memory
  unchanged); no whole-word atomicity or W/GX leg claimed -- honestly OPEN.
  No feature/MXCSR/interrupt gates apply to JMP; canonical-address gate
  pins present (example + `#GP` reuse). No guarantee weakened anywhere.

## Witness and negative evidence

- Joint companion `JumpTableCert_verbindung_zeuge`: all six TARGET premises
  on joint concrete values (two-slot table at 8200 holding 4200/4208,
  fetched `JMP [rax+0]` at 4096), all eight conclusion conjuncts through
  the fired connection, plus a memory-changing run (data cell 8300 zero to
  42, read back, bytes differ). Non-degenerate and reached; fetched step
  from actual bytes (`jtS0_fetch`, `jtS0_schritt`).
- Negative mutations: three neighbour refusals (far `/3`, `mod=0`, `E3`
  counter family), two certificate refusals (unreadable slot, foreign
  target), out-of-bounds index refusal, no-read step refusal.

## What remains open (per its CUTS, endorsed)

No hardware correspondence (canonical subset, self-consistency only);
`decodeExt` unified-admission stays with the dispatcher owner; decoded-start
production and patched-site re-decode stay with their owners; no per-access
target-to-W/GX simulation; no source/contract/cost/time/termination claim;
no fault delivery (class observation only).

## Assessment of the task

The owner task is sound as written; nothing in it needed weakening, and the
author's one judgment call (deriving rather than assuming admission) is the
stronger direction. No finding against the task.
