# MUSE-REPORT-975: Exact review of author 825 (Composition closing: image-to-fetch closing)

## CANDIDATE

CANDIDATE: 825 cd5b847858b5eb452ec4c67435ec93fa2c3cc3dc

## VERDICT

VERDICT: ACCEPT (bounded: composition-closing interface only; see CUTS below)

## What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json` (author 825, head
`cd5b8478`, base `e7c75908`, clean): `MUSE-REPORT-825.md`,
`grammatik/Grammatik.lean` (one added import line),
`grammatik/Grammatik/X86/ComposeImageFetch.lean` (new, 256 lines).
Supporting material: `.tmp/review/author-825/OWNER-TASK.md`, `PATCH.diff`,
`BUILD-EVIDENCE.json`. Reference manuals: `.tmp/HARDWARE-REFERENCES/`
(intel-instruction-reference.txt/pdf, REFERENCES.json) — consulted for
scope only, since this candidate adds no new byte forms or ISA semantics.
Producer modules were inspected live in this clone
(`LoadedExecution.lean`, `Byteschritt.lean`, `Bild.lean`, `Codec.lean`,
`Ausfuehrung.lean`): every reused name exists with a matching signature.

## Exact new definitions/theorems (all in `Gabbro.Grammatik.X86`)

- `imageSchritt` (def): `byteschritt (bildZustand bild bias rip reg fl)`.
  State memory is forced to `geladen`; only `rip`, registers, flags are
  caller inputs. No second loader/decoder/executor.
- `ComposeImageFetch_verbindung` (TARGET): generic over arbitrary admitted
  inputs (`p`, `bild`, `bias`, `rip`, `reg`, `fl`, `s`, `k`, `n`) with
  checked-map premises (acceptance, member section, section-relative start,
  wrap-free window, file-backed extent, stable section lookup, execute
  permission). Concludes fetched-bytes agreement (via accepted
  `holeFetchAux_geladen`), per-byte execute-permission agreement (via
  accepted `geladenAusfuehrbar_fund`), W^X (via accepted `wohlgeformt_wx`),
  and step identity (`rfl`, definitional).
- `ComposeImageFetch_verbindung_zeuge` (companion): joint instantiation on
  the accepted two-section `bildStore` image (executable code plus writable
  data, `n = 7`), with the composed fetch connection, a reached
  memory-changing run (`ausgangByte … = some (natByte 42)`, zero before via
  `bildStore_schritt_speichert`), and two planted refusals (mutated opcode
  `bildStoreStartMutiert`, data-section start). Non-degenerate: code plus
  data sections, real store execution.
- `imageSchritt_weiter`: success direction through existing `schritt` (via
  accepted `byteschritt_weiter`). This plus the witness is the execution
  leg: the closing step is not a conjunction of checks.
- `imageSchritt_kopf_undurchlaessig`: refusal core for a non-executable head
  byte (via `fetch_leer_ohne_exec`, `decode_nichts_leer`,
  `byteschritt_verweigert_ohne_fetch`; `fetchCap = 15` used as `14 + 1`).
- `imageSchritt_loch_verweigert`: unmapped-start refusal (via accepted
  `ausserhalb_rahmen`, 4th tuple component `.2.2.2` — verified against
  `Bild.lean` line 318: it is `ladenAusfuehrbar = false`).
- `imageSchritt_ohne_exec_verweigert`: non-executable-section refusal (via
  accepted `geladenAusfuehrbar_fund`).
- `fetch_leer_ohne_exec` (helper): fetch headed by a non-executable byte
  takes nothing.

## Architecture checks (independent)

- Byte forms / REX / register / width / flag semantics: no new forms; the
  candidate composes the accepted decoder and `schritt` without touching
  them. Nothing to fault.
- Source/destination/implicit operands, pre-fault effects, memory access
  order: inherited from accepted `byteschritt`/`schritt`; the candidate adds
  no operand handling and claims none.
- TSO/atomicity: correctly NOT claimed; CUTS leaves the TSO/GX bridge with
  its owner. No weak-memory premise is assumed.
- Feature/MXCSR/interrupt gates: untouched, correctly out of scope.
- Undefined hardware state: no new abstraction; fetch runs over the model
  `Speicher` function, stated openly in CUTS (no silicon claim).
- All major premises used: `hmem`/`hwf` in `wohlgeformt_wx`; `hrip`,
  `hfree`, `hdatei`, `hstab`, `hexe` in `holeFetchAux_geladen`; permission
  premise in the per-byte leg. No `intro _` / `have _ :=`; no conclusion
  restates a premise (the `rfl` step-identity conjunct is definitional
  bookkeeping, and the substance — fetched bytes, permissions, W^X,
  execution direction — is proved from producer lemmas).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep over the
  snapshot file hits only English words "admitted"/"admits"). No `Prop`-typed
  premise. No guarantee weakening, no desired-simulation assumption.
- Witnesses: joint, non-degenerate, with a reached memory-changing run and
  negative mutations (mutated opcode still maps clean per
  `bildStore_mutiert_mapping_bleibt`, so the refusal pins decode, not the
  map). Negative direction also covered by three named refusal theorems.
- CUTS precise: no source correspondence, no hardware correspondence, no
  whole-binary/multi-step claim, no termination claim, 15-byte window needs
  a 15-byte file-backed executable extent (generic `n`, witness `n = 7`),
  relocation re-decoding with lane 561 via `patchSiteOk`, TSO/GX with its
  owner. Overlap with lane 560 (`LoadedExecution`) disclosed by the author
  and confirmed: 560 proves the loaded-execution facts; 825 adds the
  reusable single forced-memory closing step, the generic arbitrary-input
  connection, both refusal directions, and the joint witness. No duplication
  of an interpreter.
- Scope hygiene: no diagnostic/gift/example/CLI numbers, no MARKE_EMIT
  changes, no source/checker/Spec/goal/emitter edits, no friend-reserved
  optimiser files. File list is exactly the two source files plus the report.

## Build evidence

- From `BUILD-EVIDENCE.json` (author clone `a825`): final
  `./lean-probe grammatik/Grammatik/X86/ComposeImageFetch.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (one intermediate
  2-error run during development was repaired in-file). `./lean-bau`:
  `Build completed successfully (509 jobs).` Axioms: main theorems
  `[propext, Quot.sound]`, helper `[propext]` — subset of standard, no
  excess. (One intermediate probe line shows an empty-output `0 error(s)`
  with a stale manifest message; the final recorded runs and the full
  `lean-bau` are the operative evidence.)
- Live-clone re-verification: `bash` execution is denied in this review
  session, so `./lean-bau`/`./lean-probe` could not be re-run here and the
  snapshot could not be rebuilt locally. Mitigation: every reused producer
  name/signature was verified live in this clone via search (all 20+
  references resolve: `holeFetchAux_geladen`, `geladenAusfuehrbar_fund`,
  `wohlgeformt_wx`, `ausserhalb_rahmen`, `byteschritt_weiter`,
  `byteschritt_verweigert_ohne_fetch`, `decode_nichts_leer`,
  `bildZustand`, `fetchCap = 15`, `bildStore*` family, `storeReg`,
  `storeFlags`, `ausgangByte`/`ausgangRip`, `natByte`), the full 256-line
  candidate file was read end to end, and the refusal-tuple projection was
  checked against the producer source. No suspicious case requiring a
  queued-wrapper reproduction was found.
- `gabbro_ziel` was not re-checked by the author; accepted as bounded
  because the change is a new leaf module plus one import line, outside the
  goal proof's dependency cone. Full publication checks remain with the
  serial integration watch, not this review.

## What remains open (not this candidate's debt)

Source correspondence, hardware (silicon) correspondence, whole-binary
multi-step validation, entry legality beyond containment, relocation
patched-site re-decoding (owner lane 561), TSO/GX bridge (owner lane),
termination, timing/interrupts/caches/TLBs, and the full 15-byte window
equality beyond file-backed executable extents — all explicitly in the
candidate's CUTS and untouched by this verdict.

## Task assessment

Nothing in the task appears wrong. The ZEUGE requirement (jointly
inhabited, non-degenerate, memory-changing reached run) is met by
`ComposeImageFetch_verbindung_zeuge`. The "conjunction of checks is not
execution" bar is met by `imageSchritt_weiter` plus the 42-store run
through the closing step.

## Session note

Report-only lane: no source files touched; live tree holds only this
report besides the commit. Shell access was briefly gated mid-session
(one denied call) then restored; producer references were verified live
via search. Commit: add `MUSE-REPORT-975.md` only (done).
