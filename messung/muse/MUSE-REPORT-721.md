# MUSE-REPORT-721: Exact review of author 720 (integer bytes on shared TSO execution)

Lane 721, report-only review. Owned file only: `MUSE-REPORT-721.md`.

CANDIDATE: 720 39bb46bd9a49663b2c37ba1135ba1d8d895c0a98
VERDICT: ACCEPT

## Scope

Pinned snapshot `.tmp/review/author-720` (SNAPSHOT.json: author 720, head
`39bb46bd9a49663b2c37ba1135ba1d8d895c0a98`, base
`9fc15bf411e3dd7061a5bec2b79f54f0ee9722c3`, files `MUSE-REPORT-720.md`,
`grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/ConcurrentIntegerExecution.lean`, clean true;
re-verified unchanged this turn) reviewed against owner task `lanes/720.md`.
PATCH touches exactly the three owned files: new 2047-line module, one additive
umbrella import (`grammatik/Grammatik.lean` line 485), report.
`HardwareExecution.lean` unedited (layered over, as tasked). No checker, Spec,
goal, emitter, Rust or optimiser edits. This clone (`muse/721`) holds no
candidate Lean changes: review-only lane.

## Evidence (pinned-source inspection, full 2047-line module read)

- Addresses: `ConcIntOp` load/store at explicit `Breite` via base plus disp32;
  `concAddr` is the accepted pilot `effAddr` on the pre-state file.
  `concAddr_prestate` lifts `effAddr_prestate`; `concAddr_alias_beispiel`
  proves non-injectivity (no alias claim); `concAddr_basisForm` /
  `concAddr_store_basisForm` bridge to selected `adrEff` via accepted
  `adrEff_basisForm` (symmetric). No second address model.
- Bytes: `entriesOf` issues exactly `b.bytes` canonical little-endian
  `wortByte` entries, oldest first; `entriesOf_laenge`,
  `entriesOf_b64 = wortEintraege`, `entriesOf_b8_pin` (`decide`),
  `entriesOf_in_fuss`. The 64-bit list reuses the accepted group.
- Admission and issue: `concAdmitted` is `kanonisch48` plus no-wrap range
  plus per-direction `lesbarN`/`schreibbarN`, with refusal splittings;
  `concIssue` gates first, then folds accepted `issueListe`/`issueByte`.
  Append-only buffers (`concIssue_haengt_an`), memory-identical
  (`concIssue_mem`), permission preservation, gate stability,
  `issueListe_erreichbar` (one TSO step per byte), `issueListe_anderer_kern`.
- Loads: `concLoad` routes every footprint byte through accepted `loadByte`,
  assembled exactly like `read8/16/32`/`bytesWort`. `concLoad_ohne_eintrag`
  (via accepted `load_ohne_eintrag` per byte) is the no-substitution bridge:
  buffered coincides with sequential only where nothing forwards.
  `neuestens_entriesOf` plus `loadByte_nach_concIssue_leer` plus
  `concLoad_nach_concIssue` prove whole-access forwarding to the accepted
  read-after-write values at all four widths.
- Machine adapters over canonical `HwMaschine`: `concStoreMaschine`
  (pre-state address and value, buffer issue, RIP advance, registers and
  flags kept), `concLoadMaschine` (forwarded value merged via accepted
  `mergeRegNarrow`/`regSet`; `b32_clears` via `mergeRegNarrow_b32_fits`,
  `b64_full` via `mergeRegNarrow_b64`). Length and gate refusals return
  `none` (pre-fault order, no successor). Single-byte `HwSchritt`
  correspondence: `concLoadMaschine_b8_lade` (`.lade`), and
  `concStoreMaschine_b8_gibAus` (`.gibAus` via `issueListe_einzeln`).
  `concDrain` is accepted `flushKern` plus buffer head; `concDrain_spuele`
  gives canonical `.spuele` with `flush_schreibt_kopf`.
- `HwWf` constrains only silicon profiles (never memory or buffers), so the
  well-formedness passthroughs are sound; `concWitM0_wf`
  (`intro c f _; cases f <;> rfl`) exactly mirrors accepted `hwWitStart_wf`
  over the same `basisHw`/`basisBereit`, and is flagged transparently in the
  author report. No repair demanded.
- Word discipline: `concIssue_b64_gruppe` establishes accepted `WortGruppe`
  from an empty own buffer plus `FremdFrei`, with no alignment premise;
  `concWort_liest_zurueck` and `concWort_verflochten_liest` reuse the
  accepted grouped and interleaved read-back proofs with real cross-core
  accesses; `concGruppe_verweigert_lock` keeps LOCK refused on grouped
  states. No single-event claim is derived from alignment.
- Codec boundary: `concDecode` admits pilot `load64`/`store64` (accepted round
  trips) plus narrow `store32` exactly where the pilot refuses
  (`narrow_pilot_verweigert` plus narrow round trip); register-only rows
  refuse. `concDecode_nur_b64_b32` splits every pilot and every narrow
  constructor (exact constructor evidence); `concDecode_laenge_ok` holds on
  both paths via accepted coverage lemmas. 8/16-bit memory rows (and 32-bit
  loads) stay explicit PENDING in CUTS, which the task permits; nothing is
  reinvented or assumed.
- Joint witness `concWit_zeuge`: core 0 fetches a real narrow
  `store32 [rbx], rax` (7 bytes) from executable memory, decodes through the
  boundary, issues width-selected with register, flag and memory discipline,
  forwards to itself while core 1 still reads the old value, then drains to
  `0x04` observed by both cores, with a `TSOErreichbar` existential (reached,
  memory-changing, two-core) beside fetch, permission, canonical-hole,
  wrap-edge, tearing and overlap refusals plus the address alias.
  Non-degenerate.
- Hygiene of the pinned module: precise search for `sorryAx`, ``declaration
  uses `sorry` ``, standalone `sorry`, `admit`, `axiom`, `native_decide` and
  `unsafe` finds no hit in the final file (the intermediate `sorryAx` visible
  in BUILD-EVIDENCE rows was repaired before the final commit). CUTS block and
  61 `#print axioms` are present. Manual provenance is clone-local
  `REFERENCES.json` (Intel SDM 325462-093US) plus instruction-reference
  headings, stated as provenance and never as silicon proof.

## Checks

Author BUILD-EVIDENCE final rows: `./lean-probe` on the candidate module
reports `== 0 error(s)` with exit 0, and `./lean-bau` reports `Build completed
successfully (482 jobs).`; printed axioms stay within `propext`,
`Classical.choice` and `Quot.sound` (`Classical.choice` arrives through reused
accepted round-trip lemmas). No independent wrapper re-run of the candidate
was possible from this review-only clone (the module lives in the author
clone; this tree holds only the snapshot copy, and shell access flapped
during this lane). Integration must re-run all mandatory gates (source build,
axioms including `gabbro_ziel`, tests, emission, key scan) on the exact
candidate hash; a positive review bypasses none of them.

## Open (correctly scoped per CUTS, not claimed)

Per-access TSO-to-W/GX simulation; source, contract and checker
correspondence; missing codec rows; LOCK RMW producer; faults beyond carried
permission, canonical and refusal outcomes; interrupts, timing and liveness;
any silicon correspondence. Consumer interface: `concStoreMaschine` and
`concLoadMaschine` (with preservation theorems), `concDrain`,
`concIssue_b64_gruppe`, `concWort_liest_zurueck`,
`concWort_verflochten_liest`, `concDecode` (with coverage and length), and
`concWit_zeuge`.

## Task feedback

The `lanes/720.md` statement is correct. Location note (shared with the
author report): `DIRECT-COMPILER-DESIGN.md` lives at the repo root, not under
`dokumente/`. No repair items: no wishful successor or refinement premises, no
toy parallel interpreter, no swapped sequential/concurrent memory, no
unsupported opcode priority, no empty witness, no weakened guarantee, no fake
closure. Natural follow-ups, if tasked: further codec rows each with their own
round-trip producers, LOCK RMW, and the per-access target-to-W/GX leg (all
already booked as OPEN).
