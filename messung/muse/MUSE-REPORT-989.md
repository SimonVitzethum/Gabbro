# MUSE-REPORT-989: Exact review of author839 (FP-ledger closing)

## CANDIDATE

CANDIDATE: 839 e67b0b287ffd1d3de151c0be13843bd1dd9b6ac7

## VERDICT

VERDICT: ACCEPT

Acceptance is bounded: scalar-FP ledger gating over the accepted producers,
with the cuts stated in the candidate file (see bounded-acceptance notes).

## What was done

Report-only exact review of the pinned snapshot in `.tmp/review/author-839/`
(task `OWNER-TASK.md`, `PATCH.diff`, `MUSE-REPORT-839.md`, `BUILD-EVIDENCE.json`,
snapshot `grammatik/` copy) against the official local reference snapshot
(`.tmp/HARDWARE-REFERENCES/REFERENCES.json`: Intel SDM 325462-093US,
September 2026, sha256-verified). No source file was modified; this lane owns
only this report. Inspected by name the reused accepted producers in this
clone: `Gleitprofil.lean` (ledger data, `mxcsrGueltig`, `kontextReset`),
`ScalarFloat.lean` (`fpEintritt`, `fpSchritt`, `fpRechne`, `fpSchritt_addsdRR`),
`ScalarFloatCodec.lean` (`fpFetchDekodiert`, `fpByteschritt`, `fpCodecT/T2`,
fetch/read-back/change theorems), `FpControlHardwareForms.lean`
(`mxcsrWitT1`, `mxcsrWit_eintritt`).

## Scope check

`PATCH.diff` touches exactly the three owned files: new
`grammatik/Grammatik/X86/ComposeFpLedger.lean` (350 lines), one appended
`import Grammatik.X86.ComposeFpLedger` at the end of `grammatik/Grammatik.lean`,
and `MUSE-REPORT-839.md`. No diagnostic/gift/example/CLI numbers, no
`MARKE_EMIT` changes, no source/checker/Spec/goal/emitter edits, no
friend-reserved optimiser files. No new definitions/theorems were added by
this reviewer.

Reviewed definitions/theorems (all in `Gabbro.Grammatik.X86`): `FpLedger`,
`fpLedgerSchritt`, `fpLedgerSchritt_ledger_verweigert`,
`fpLedgerSchritt_kreuzung_verweigert`, `fpLedgerSchritt_erfolg`,
`fpLedgerSchritt_schritt`, `fpLedgerByteschritt`,
`fpLedgerByteschritt_hol_verweigert`, `fpLedgerByteschritt_schritt`,
`ComposeFpLedger_verbindung` (TARGET),
`ComposeFpLedger_keineKontraktion`, `ComposeFpLedgerNeg_ftz/_daz/_runde/
_maske/_kreuzung/_nachLaden`, `ComposeFpLedgerWit_schritt`,
`ComposeFpLedger_verbindung_zeuge` (companion, exact ZEUGE names).

## Evidence

- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new
  file (grep over the snapshot copy; only documentation words and the
  required `#print axioms` lines match). No `Prop`-typed premises, no
  discarded premises, no restated-premise conclusions.
- Axioms (from the pinned `BUILD-EVIDENCE.json` probe transcript):
  `[propext, Quot.sound]` throughout, witnesses additionally
  `Classical.choice` -- within the standard `gabbro_ziel` set.
- Build: pinned evidence `./lean-bau` green at 509 jobs; this reviewer's
  own clone (without the candidate applied) builds green independently:
  `Build completed successfully (510 jobs).`
- Premise use: every premise of the TARGET is consumed in its proof
  (`hfp`/`hledger` via the post-step word derivation, `hf`/`hout` via the
  byte-step projection); helpers use all premises.
- Refusal legs independently verified bit-by-bit against `mxcsrGueltig`
  (RNE = bits 13-14 clear, FTZ = bit 15, DAZ = bit 6, masks = bits 7-12):
  `0x9F80` isolates FTZ, `0x1FC0` isolates DAZ, `0x3F80` (RC=01) isolates
  rounding, `0x0F80` isolates the precision mask, `0x1FBF` is admitted
  (sticky set, `mxcsr_sticky_egal_gueltig`) yet refused as scope crossing,
  and `mxcsrWitT1` is the reached LDMXCSR state installing `0x1FBF`, so the
  old ledger entry no longer matches. Six negatives, one varied leg each,
  decided on actual words.
- Witness: joint premises on the accepted `fpCodecT` store image with the
  accepted step, ledger persistence, `+inf` read-back (`fpCodec_liest`)
  and an observably changed byte (`fpCodec_aendert`) -- non-degenerate,
  memory-changing, reached from actual fetched bytes. Satisfies the ZEUGE
  inhabitation rule.
- No guarantee weakening: the guarded step only refuses more (bad ledger,
  crossing, fetch/producer refusal); the proved direction is guarded
  success implies the accepted step ran -- no false converse is claimed.
  No desired-simulation premise is assumed; missing legs are CUTS.
- Sound abstraction: sticky flags stay unmodelled exactly as the accepted
  `Gleitprofil` §2 gap states (reused, not introduced); `fpEintritt` is a
  validator admission, never a hardware fault, per the producer's own
  documented reading. No invented determinism, no zeroed/ignored defined
  effects, no AMD/silicon claims.

## Bounded-acceptance notes (not repairs)

- `fpSchritt` preserves `t.fp` on every current arm (records update only
  `kern`/`xmm`), so the post-step ledger check is currently vacuous and the
  real closing work is done by the entry admission, the scope match and the
  fetch-from-bytes. The post-check is future-proofing for control-changing
  forms, and the file's CUTS honestly state there are no per-form ledger
  frames beyond the successor check. Bounded, not fake: the refused legs
  are real and the theorem states exactly what it proves.
- Out of scope by explicit CUTS: VEX/x87/FMA/packed forms, REX extension,
  TSO/GX leg, validator/image/entry/budget integration.

## What remains open

Nothing in this review lane: the candidate is integrable as-is. The
follow-up work named in the candidate's CUTS (per-form ledger frames,
wider forms, concurrency/validator legs) belongs to its owning lanes per
`DIRECT-COMPILER.md`.

## Task feedback

Nothing in the review task was wrong. The snapshot, owner task, patch and
build evidence were all present and mutually consistent (pinned HEAD
`e67b0b28`, base `e7c75908`, clean tree, 3 files).
