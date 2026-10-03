# MUSE-REPORT-974: Exact review of author 824 (decode-to-execution closing)

## CANDIDATE

CANDIDATE: 824 4feb5b9f3bd28b368b043931ac59b4ff3a08edb5

## VERDICT

VERDICT: ACCEPT

## What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json`: base
`e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, head `4feb5b9f...`,
files `MUSE-REPORT-824.md`, `grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/ComposeDecodeExec.lean` (new, 192 lines).
Task: `.tmp/review/author-824/OWNER-TASK.md` (lane 824).
Reference: local Intel SDM snapshot per
`.tmp/HARDWARE-REFERENCES/REFERENCES.json` (325462-093US, Sep 2026;
Intel-profile evidence only, no AMD/silicon claim).
Parent modules inspected in this clone (base side):
`grammatik/Grammatik/X86/ExtendedExecution.lean`
(`decodeExt`/`stepExt`/`fetchExt`/`extByteschritt`, `fetchExt_erfolg`,
`extByteschritt_weiter`/`_verweigert`, `decodeExt_kanonisch`,
`extWitStart`/`extWitBereit`, `extWit_zwei_schritte_speichern`,
`extWit_anfang_null`, `extWit_nachBild_verweigert`),
`Codec.lean` (`roundtrip`, `encode_len`), `Byteschritt.lean` (`geholt`).

## Findings

1. Architecture (not just Lean-green): the candidate defines no new byte
   forms, no executor and no second interpreter. Producer is the accepted
   unified `decodeExt` (pilot + narrow/muldiv/shift/SETcc/CMOVcc/scalar-FP/
   packed-integer), consumer is the accepted unified `stepExt`, connector is
   the accepted `fetchExt` over the actual fetched window `geholt` plus
   `extByteschritt`. REX/register/width/flag semantics, source/destination/
   implicit operands, pre-fault admission (length equation + `laengeOk` guard
   + `ausfuehrbarN` prefix permission), fetch-before-step order and
   feature/readiness gating (`BereitProfil`, carried generically) are all
   inherited by name, never re-decided. `verweigert` is absence of a
   transition (never a termination claim); the divide `halt` is carried, not
   proved. Undefined state is not given invented determinism. No TSO/W/GX,
   LOCK/wider-SIMD, ABI/loader/entry/budget or whole-image-beyond-window
   claim is made; all are explicit CUTS. This matches the task's composition
   contract.
2. Premise use (all major premises used, none discarded): `dispatcher_`
   `erreicht_schritt` consumes `hf` + `hs` via `extByteschritt_weiter`;
   `fetchTrifftDekodierer` is the accepted `fetchExt_erfolg` at the actual
   window; `undekodiertVerweigert` derives `fetchExt = none` from
   `decodeExt = none` (`simp [fetchExt, h]`) then applies
   `extByteschritt_verweigert`; `pilotKanonischErreicht` uses `hwin`
   (window equation), `hexe` (execute permission), `bf`/`suffix` (via
   `encode_len`, `roundtrip`, `decodeExt_kanonisch`, admission) and `b`
   (unified step). `ComposeDecodeExec_verbindung` composes all three legs
   with no added premise. No conclusion restates a premise; no contract
   parameters are quantified away; no `intro _`/`have _ :=` discard.
3. Witness (non-degenerate, reached, joint): `ComposeDecodeExec_`
   `verbindung_zeuge` instantiates the closing at the accepted mixed
   pilot/scalar-FP witness (`extWitStart`, `extWitBereit`) and conjoins the
   accepted reached run (two actual cells read 0 at start via
   `extWit_anfang_null`, read 42 after two dispatcher steps via
   `extWit_zwei_schritte_speichern`, i.e. memory-changing through the
   composed `extByteschritt`/`extSchritt2`) with the planted past-image
   refusal (`extWit_nachBild_verweigert`). Joint inhabitation holds: the
   universal closing plus the concrete run plus the refusal are proved
   together. Negative mutation present (past-image refusal); the generic
   refusal direction (`undekodiertVerweigert`) is proved for arbitrary
   inputs, not just the witness.
4. No fake closure: the generic leg quantifies over arbitrary `ExtInstr`
   (all eight families) at the dispatcher level via the accepted selection
   lemma, so it is not a pin conjunction. The only pin-level reliance is
   for per-family canonical encoder-to-dispatcher legs beyond the pilot,
   which are explicitly NOT claimed and named as CUTS with owning lanes
   (`decodeNarrow`, `decodeMulDiv`, `decodeShift`, `decodeSetCC`/
   `decodeCmov`, `fpDecode`, `decodeVector`). The arbitrary-pilot canonical
   corollary (`pilotKanonischErreicht`, via accepted `roundtrip` +
   `decodeExt_kanonisch` + `encode_len`) is the one encoder leg closed, for
   an arbitrary `Befehl`. Bounded acceptance is the honest reading.
5. Forbidden tokens: inspected `PATCH.diff` and the snapshot
   `ComposeDecodeExec.lean`: no `sorry`/`admit`/`axiom`/`native_decide`/
   `unsafe` in code (grep hits are prose backticks and `#print axioms`
   lines only). In-file `CUTS:` block plus `#print axioms` for all seven
   names present. Axioms per build evidence: five names at
   `[propext, Quot.sound]`, `fetchTrifftDekodierer` at `[propext]`,
   `pilotKanonischErreicht` at `[propext, Classical.choice, Quot.sound]`
   (standard `gabbro_ziel` set; the `Classical.choice` leg comes from the
   accepted pilot codec path, not from a new assumption).
6. Build evidence (author-side, reproduced by reading, not re-run here):
   `./lean-probe` final pass `== 0 error(s) in the COMPLETE output; exit 0`
   with all seven axiom prints as above; `./lean-bau`
   `== exit 0; 0 error line(s)`, `Build completed successfully (509 jobs)`
   including `Built Grammatik.X86.ComposeDecodeExec`. One intermediate
   7-error probe in the evidence log is an in-progress skeleton state,
   superseded by the final green pass and the green full build. This
   report-only review ran no builders (no source owned, no suspicious case
   needing reproduction beyond the accepted `decide` witnesses, whose
   statements were read in the parent file).
7. Hygiene: no diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes,
   no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
   files. `Grammatik.lean` diff is the single registry import line.
   English throughout.

## Bounded acceptance (what ACCEPT does and does not cover)

ACCEPT covers: dispatcher-level decode-to-execution closing for admitted
fetches over arbitrary `ExtInstr` inputs (fetch success carries decoder
agreement + admission; fetched form reaches its unified rule; decoder
refusal on the window is dispatcher refusal), the arbitrary-pilot
canonical corollary, and the joint memory-changing witness with planted
refusal. NOT covered (explicit CUTS, correctly unclaimed): per-family
canonical-byte encoder legs beyond the pilot (general non-shadowing owned
by the extension codec lanes), hardware correspondence, source/IR,
TSO/W/GX, LOCK/wider-SIMD, ABI/loader/entry/budget, whole-image beyond the
fetched window, termination, silicon behaviour of the divide trap.
Admission-failure refusal (decoded but not admitted) follows from the same
accepted `extByteschritt_verweigert` leg but is not separately stated; not
a defect, noted for precision.

## Reproduction / verification performed here

- Read pinned `PATCH.diff` (285 lines), `MUSE-REPORT-824.md`,
  `BUILD-EVIDENCE.json`, `OWNER-TASK.md`, `SNAPSHOT.json` in full.
- Read parent `ExtendedExecution.lean` (829 lines) in full; verified every
  reused name exists with a matching signature (`decodeExt_kanonisch`,
  `fetchExt_erfolg`, `extByteschritt_weiter`/`_verweigert`, `roundtrip`,
  `encode_len`, `geholt`, witness defs/theorems) via targeted reads of
  `Codec.lean` and `Byteschritt.lean` plus grep.
- Grep for forbidden tokens over the snapshot: only prose/`#print` hits.
- No builders run from this review lane (owns only this report; no source
  to check). Lean-green and axiom claims rest on the author's complete
  queued-wrapper evidence quoted above, cross-checked against the PATCH text.

## Open / repairs

None required. Minimal follow-ups (not conditions): a future lane may state
the admission-failure refusal leg explicitly and close the per-family
canonical encoder legs when the owning codec lanes deliver general
non-shadowing.
