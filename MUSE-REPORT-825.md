# MUSE-REPORT-825: Composition closing: image-to-fetch closing

## What was done

Created `grammatik/Grammatik/X86/ComposeImageFetch.lean` (new file, owned)
and appended `import Grammatik.X86.ComposeImageFetch` to
`grammatik/Grammatik.lean`. The file closes the checked-image to actual
instruction-fetch interface by composing already-accepted producer modules,
reusing their definitions and lemmas by name. No producer fact is re-proved;
no second loader, decoder, executor or ISA model is defined.

## Exact new definitions/theorems

- `imageSchritt` (def): the one checked closing step,
  `byteschritt (bildZustand bild bias rip reg fl)`. State memory is forced
  to the canonically loaded `geladen`; only `rip`, registers and flags are
  caller inputs.
- `ComposeImageFetch_verbindung` (TARGET theorem): generic over arbitrary
  admitted inputs (`p`, `bild`, `bias`, `rip`, `reg`, `fl`, `s`, `k`, `n`)
  with checked-map premises (acceptance, member section, section-relative
  start, wrap-free window, file-backed extent, stable section lookup,
  execute permission). Concludes fetched-bytes agreement (via accepted
  `holeFetchAux_geladen`), per-byte execute-permission agreement (via
  accepted `geladenAusfuehrbar_fund`), W^X of the section (via accepted
  `wohlgeformt_wx`), and identity of the closing step with the actual
  fetch-execute step.
- `ComposeImageFetch_verbindung_zeuge` (companion): all premises
  instantiated jointly on the accepted two-section store image
  (`bildStore`, code plus writable data: the non-degenerate case), with the
  composed fetch connection, a reached memory-changing run through the
  closing step (42 into the data cell, zero before), and planted refusals
  (mutated opcode byte, data-section start).
- `imageSchritt_weiter`: success direction through the existing `schritt`
  (via accepted `byteschritt_weiter`).
- `imageSchritt_kopf_undurchlaessig`: refusal core for a non-executable
  head byte (via `fetch_leer_ohne_exec`, `decode_nichts_leer`,
  `byteschritt_verweigert_ohne_fetch`).
- `imageSchritt_loch_verweigert`: unmapped-start refusal (via accepted
  `ausserhalb_rahmen`).
- `imageSchritt_ohne_exec_verweigert`: non-executable-section refusal (via
  accepted `geladenAusfuehrbar_fund`).
- `fetch_leer_ohne_exec` (helper): a fetch headed by a non-executable byte
  takes nothing.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/ComposeImageFetch.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (509 jobs).`
  `Grammatik.X86.ComposeImageFetch` built; whole `Grammatik` built.
- Axioms: main theorems depend on `[propext, Quot.sound]`, helper on
  `[propext]`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
  `gabbro_ziel` was not re-checked (`#print axioms` on it was not run);
  the change is a new leaf module plus one import line, so it cannot affect
  the goal proof's dependency cone.

## What remains open (see CUTS in the file)

No source correspondence, no hardware correspondence, no whole-binary
theorem, no termination claim. Relocation patched-site re-decoding stays
with its owner (rel32 lane 561 via `patchSiteOk`); the TSO/GX bridge stays
with its owner. The full 15-byte window equality needs a 15-byte
file-backed executable extent; the generic connection is stated for an
arbitrary window `n` (the joint witness uses `n = 7`).

## Task assessment

Nothing in the task appears wrong. One overlap to record: lane 560
(`LoadedExecution`) already connects the checked `Bild` mapping to byte
fetch for its store image; this lane adds the reusable composition layer on
top (single forced-memory closing step, generic arbitrary-input connection,
both refusal directions as named theorems, joint witness), which 560 does
not provide as a standalone interface. No numbers, emission counters,
source/checker/Spec/goal/emitter files, or friend-reserved optimiser files
were touched.
