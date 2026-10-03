# MUSE-REPORT-1007: Exact review of author 857 (permission-check closing)

## CANDIDATE and VERDICT

- CANDIDATE: 857 098a0e1bf8013b2727b69a5ddb9c7f4c169aad53
- Base: b040b155159f47629542b0083e2f0a8a607f2b4c (verified equal to this
  reviewer's HEAD via `git log`; author's BUILD-EVIDENCE base matches).
- VERDICT: ACCEPT (bounded; bounds and follow-ups below).

## Task reviewed

Lane 857: close the per-access permission check to the fetch/decode/execute
chain (unchecked access unrepresentable, not merely absent) by composing
already-accepted modules into one checked closing step through the existing
`byteschritt`. ZEUGE: `ComposePermCheck_verbindung` with companion
`ComposePermCheck_verbindung_zeuge`.

## What I inspected

- `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-857/OWNER-TASK.md`,
  `MUSE-REPORT-857.md`, `BUILD-EVIDENCE.json`, `PATCH.diff` (732 lines),
  and the full candidate module
  `.tmp/review/author-857/grammatik/Grammatik/X86/ComposePermCheck.lean`
  (617 lines), read in full.
- Every accepted name the candidate reuses, checked against this clone
  (which is at the candidate's base): `byte_aus_weiter`
  (AccessExecution.lean:43, premise is `byteRealisiert`, definitionally
  `byteschritt s = .weiter s'`, so the candidate's call typechecks),
  `fetchDekodiert_entspricht` (Byteschritt.lean:157, 4-tuple with `hok`
  and `hexe` as destructured), `byteschritt_verweigert_ohne_schritt`
  (Byteschritt.lean:203, argument order as called),
  `read64_braucht_lesbar` / `write64_braucht_schreibbar`
  (WordAtomicity.lean:61/71), `write64_verweigert` (Speicher.lean:266),
  `fuss_mem` (Zugriffe.lean:168), all 14 `zugriff_*` equations
  (Zugriffe.lean:63-162, pure forms `⟨[], [], none⟩`), all 6
  `schritt_*_verweigert` refusal lemmas with matching signatures
  (Ausfuehrung.lean:236ff), `byteschritt`/`ByteAusgang`/`ausgangRip`/
  `ausgangByte` defs (Byteschritt.lean:62-76, 257-264; exactly two
  outcomes, refusal is absence of transition), `lesbar8`/`schreibbar8`
  (all 8 bytes, Speicher.lean:22-33), `read64` (permission-gated,
  Speicher.lean:47-48), `ausfuehrbarN` (execute-only fetch,
  Byteschritt.lean:23-25), `ketteDaten` (8192..8200) / `ketteExec`
  (4096..4128) / `witnessFlags` / `ketteProg` / `ohneExecStart` /
  `ohne_exec_verweigert` (Byteschritt.lean:285-399), `addrOff_null`,
  `natByte`, `stapelOben`, `effAddr`, `ripNach`, `laengeOk`.
- Official reference: local `intel-instruction-reference.txt` line 65678:
  `REX.W + 89 /r  MOV r/m64, r64  MR  Valid  N.E.  Move r64 to r/m64`
  (Intel SDM 325462-093US per REFERENCES.json; Intel-profile evidence
  only, no vendor/silicon claim).
- Patch scope: exactly the three snapshotted files. `Grammatik.lean`
  hunk context (`ComposeDecodeExec`, `ComposeImageFetch` tail) matches
  this clone's file tail; the hunk adds one import line only. PATCH tail
  (CUTS + `#print axioms` + `end`) matches the snapshot module ending.

## Architecture findings

- Byte forms / REX / width: the witness store bytes
  `48 89 83 00 00 00 00` decode as REX.W + `MOV r/m64, r64`,
  ModRM `0x83` = mod 10 / reg 000 (RAX) / r/m 011 (RBX) + disp32 0,
  i.e. `MOV [RBX+0], RAX`, length 7. This is confirmed three ways:
  the Intel reference above, byte-identity with the accepted
  `ketteProg` store encoding (Byteschritt.lean:288), and the
  `decide`-proved fetch-pinning theorems. `laengeOk 7 = true`.
- Source/destination/implicit operands: load/store use `effAddr`;
  push/pop/call/ret use `stapelOben`/rsp footprints with the
  `simpa [stapelOben]` bridge; call pushes the actual next RIP
  (`ripNach`). All match the accepted equations; no operand invented.
- Pre-fault effects: `schritt_* = none` is total (no successor at
  all), `byteschritt` maps it to `verweigert`. No partial architectural
  state on refusal, consistent with fault-suppression semantics of the
  accepted model. Nothing ignored, nothing zeroed.
- Memory access order / TSO / atomicity: footprints stay byte sets;
  the 8-byte checks cover every footprint byte (`fuss_mem` + case
  split). No atomicity, linearisation or visibility claim is made;
  CUTS explicitly leave the TSO/W/GX bridge OPEN. Correct boundary.
- Feature/MXCSR/interrupt gates: the 14 pilot forms contain no FP,
  SIMD, LOCK or interrupt forms; nothing to gate, nothing assumed.
- Canonical execution interaction: the consumer runs only the existing
  `byteschritt`; success decomposes via accepted `byte_aus_weiter` +
  `fetchDekodiert_entspricht`; refusal via accepted
  `byteschritt_verweigert_ohne_schritt`. No second loader, decoder,
  executor or ISA model. No producer internals re-proved.
- No guarantee weakening, no desired-simulation premise: both
  directions derive permissions from executed steps / refusals from
  denied bytes. The pure-form arms are vacuous only over the accepted
  canonical footprint (a cited producer, lane 568 linkage), which is
  legitimate reuse, not an invented premise.
- Witnesses: joint store run changes byte 8192 from 0 to 7 through the
  composed step (footprint pinned `Fuss 8192`); refusal direction is
  derived THROUGH the closing on the write-denied twin (not a bare
  `decide`); execute-denied refusal via accepted `ohneExecStart`.
  Non-degenerate and memory-changing. Negative mutations: data-denied
  twin (fetch still decodes identically, step refused) and
  execute-denied state. Fetch/data permission separation preserved.
- Hygiene: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`
  (grep of the candidate file finds only the English word "admits" in
  comments and `#print axioms` lines); no `intro _`, no `have _ :=`;
  every premise is used (`hok` in the memory arms, `hstep`/`hperm`
  throughout). Axioms per BUILD-EVIDENCE are `[propext, Quot.sound]`
  or `[propext]` for all 15 entry points: within the standard goal set.
- Target statement respected: `ComposePermCheck_verbindung` +
  `ComposePermCheck_verbindung_zeuge` with the exact required names;
  no added premises, no weakened conclusion.

## Bounds of this ACCEPT (not re-verified live)

- Per the lane constraint "Own only MUSE-REPORT-1007.md, no source or
  live controls", I ran no builds: no `./lean-probe`/`./lean-bau` on
  the candidate (that would require placing unowned source into
  `grammatik/`). Green-build evidence is the author's
  BUILD-EVIDENCE.json: final `./lean-probe` 0 errors with all 15
  `#print axioms` lines, full `./lean-bau` `== exit 0`, `Build
  completed successfully (511 jobs)`, including two genuine
  intermediate failures with real diagnostics (undecidable
  `ByteAusgang` equality reworked to the `ausgangRip` pattern;
  `List.Mem` constructor fix). The evidence is internally consistent
  (commit hashes 4a07dec4 + 098a0e1b, clean tree) and every reusable
  name/signature it depends on was independently confirmed above.
- `gabbro_ziel` axioms were not re-printed (author discloses this; no
  wrapper exists). Construction is additive (one import line), and the
  evidenced full build includes the Zielsatz green.

## Follow-ups (minor; none blocks acceptance)

1. `PermGeprueft` is defined but never referenced by any theorem
   statement (only CUTS text + `#print axioms`); the closing restates
   its content inline. Suggest stating the closing through the bundle
   or dropping it in a follow-up.
2. Generic fetch-denied refusal (accepted
   `byteschritt_verweigert_ohne_fetch`) is not composed into the
   closing; only the footprint-failure-on-fetched leg is, plus the
   `ohneExecStart` witness. A fetch-denial conjunct would fully close
   the permission statement; it is a small corollary of accepted parts.
3. The report's "pure forms touch no byte" phrasing rests on the
   accepted `zugriff` completeness (producer lane 568); correctly cited
   as a producer, noted here for the record.

## Review method note

No numbers, counters, source/checker/Spec/emitter files, or
friend-reserved optimiser files are touched by the candidate. This
review touched only this report file. No network, no other clones, no
credentials were used. The two `bash` calls I attempted for branch
listing and patch word-count were refused by the permission
classifier; all verification above used read-only file tools inside
this clone plus the provided `.tmp/review` and
`.tmp/HARDWARE-REFERENCES` inputs.
