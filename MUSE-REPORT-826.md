# MUSE-REPORT-826: relocation-to-redecode closing

## Clone / branch
- Clone `/home/simon/Dokumente/gabbro-muse/a826`, branch `muse/826`: verified, match.
- Owned files only: `grammatik/Grammatik/X86/ComposeRelocRedecode.lean` (new),
  `grammatik/Grammatik.lean` (one import line appended), this report.

## What was done
Closed relocation patching to re-decoding as one checked composition step.
Delta vs lane 561 (`RelocatedExecution`): 561 connects `relocBytes`
(encoder output) to decode/execution, but never the finite file-byte
patching (`Relokation.patchAt`/`patchRel32`) to re-decoding. This lane
closes exactly that: a successful `patchAt` of canonical site bytes
implies the patched window re-decodes, plus `layoutOk` re-decision.

## New definitions / theorems (exact names)
- `redecodeFenster`: the `len` bytes at file offset `off` of a patched image.
- `patchAt_segment`: a successful patch writes exactly the patch bytes at
  the site window (induction in the shape of `patchAt_stelle`).
- `ComposeRelocRedecode_verbindung` (TARGET): patch success + site equation
  block + `hinweisOk` imply re-decode through canonical `decode` to the
  site instruction at its carried length, `direktZiel` word+Nats equal the
  intended target, the layout hint equals the recomputation with
  `layoutOk = true`, and the accepted relocated call run
  (`ruf_schritt_zeuge`) reaches its target with an observable stack write.
  Every premise is used; no premise is a restated conclusion.
- `ComposeRelocRedecode_verbindung_zeuge` (companion): joint premise
  inhabitation on `siteVor` + `BitVec.ofNat 32 16` + concrete patched bytes
  `[233, 16, 0, 0, 0, 255]` + `zeugenU` (table `konto` written by `setze`)
  with its recomputed layout hint. Non-degenerate throughout.
- `ComposeRelocRedecode_durchgehend`: the closing applied to the witness
  values, exhibiting re-decode, target `0x1015`, accepted layout and the
  reached memory-changing run on concrete bytes.
- Planted refusals: `relocRedecode_innen_verweigert` (bytes patch fine,
  interior target refused), `relocRedecode_aussen_verweigert` (no bytes
  computed, site refused), `relocRedecode_ueberlapp_verweigert` (overlap
  refused on both patch and layout sides).
- Reused by name, never re-proved: `patchAt`, `patchRel32`, `rel32Passt`,
  `rel32Fuer`, `patchZwei`, `sonde_patchZwei_ueberlappung`,
  `relocBytes_decode`, `patchSite_ziel`, `ruf_schritt_zeuge`,
  `hinweisOk_layoutOk`, `ueberlapp_verweigert`, `decode`, `direktZiel`.
  No second decoder, loader, executor, ISA model or IR created.

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeRelocRedecode.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau` last result line: `Build completed successfully (509 jobs).`
- Axioms: helpers `propext`-only or none; the closing and end-to-end on
  exactly `propext, Classical.choice, Quot.sound` (standard).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; English only; no
  diagnostic/gift/example/CLI numbers, no MARKE changes, no
  source/checker/Spec/goal/emitter or friend-reserved file edits.

## Open (explicit CUTS in the file, owning lanes named)
- `valX86_sound` and any source/TSO-GX/concurrency/cost/hardware claim:
  this closing feeds `valX86`/`bildDeckung`/`valLayout`, soundness waits on
  the consumer/validator lanes and shared IR 287.
- Site classes: abs64/data-field, rel8 short, non-jump/call/conditional
  (producer cuts, lanes 291/561).
- Multi-site convergence, fall-through coverage, full `DecodingCoverage`
  (consumer). No loader/entry/OS modelling.

## Note on the task text
Nothing in the task is wrong, but one clarification for the reviewer: the
memory-changing run conjunct is the closed accepted producer witness
`ruf_schritt_zeuge` (same `relocBytes` vocabulary the closing patches),
not a newly executed run -- inventing a second executor is forbidden by
the task itself, so reuse is the correct reading of "through the composed
step".
