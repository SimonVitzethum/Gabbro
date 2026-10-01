# MUSE-REPORT-293: Independent concurrency granularity and target bridge review

*Lane 293, wave A, branch `muse/293`, base `f4958150`. Docs-only lane:
no Lean file, no Rust file, no model/goal/checker/emitter/ledger change,
no new diagnostic/gift/example/CLI/MARKE numbers. Model:
opencode-go/muse-spark-1.3-contributor. No delegation, no network, no
cargo/lake direct calls.*

## What was done

Wrote `dokumente/x86/REVIEW-TSO.md` (owned file, new): independent audit
of `TSO-GX-BRUECKE.md` (lane 274), `IMAGE-ABI.md` (lane 276) and
`IR-VALIDIERUNG.md` (lane 275) against the real definitions
(`grammatik/Grammatik/Speichermodell/*`, `Zielsatz/Spec.lean`,
`RufMaschineG.lean`, `RennfreiVoll.lean`, `Semantik.lean`, `Satz.lean`,
`X86/Typen.lean`, `CTicket.lean`, `Schablonen*.lean`, `treiber.rs`).

## Exact names of new definitions/theorems

None. No Lean code added or changed. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` introduced (nothing introduced at all).

## Verification performed (source inspection, not prose trust)

- 30-row reference table (§1 of the review): every load-bearing
  file:line claim of the bridge document checked against the tree.
  Result: 25 EXACT, 3 immaterial off-by-ones (87 vs 92 for
  `FadenSchrittX`; 287 vs 288 for `segZaehleX`; 454/425 vs 455/426
  for Orakel fields/`einpassen`), 2 CONFIRMED-by-content
  (rule-count shape, treiber-gen-10 + template rows).
- Direction check: `schwach_ist_gX` (`AtomarW.lean:279`) premises
  verified as `(hO hvoll hAbg hWurzel hI hr)` — `KoerperGutSA` indeed
  not needed for `schwach` itself, as the bridge document hedges.
- `FortschrittG` verified verbatim (`Spec.lean:1828–1831`).
- `SchwachX` verified universally quantified over `ord`
  (`Spec.lean:2200–2206`) — O-ord is real.
- `GutO` (`Satz.lean:967–983`) verified to constrain writes/locks/trace
  only, not foreign READ footprint — OBS-5 (i) confirmed at the_defs.
- Pilot `Befehl` enumerated from `Typen.lean:53–72` (no LOCK, no fence,
  no sub-64-bit access) — basis of finding (a).
- No `SCFG.lean` exists anywhere — basis of finding (b).

## Findings (new beyond lane 274's own CUTS)

- (a) Pilot has no target form for RMW/fence/narrow access: bridge
  `rmw`/O-align obligations currently unattachable; sharpest hazard is
  narrow shared carriers (most real flags/atomics are narrow).
- (b) `accessList(rule)` extraction has no single owner (bridge
  O-access vs IR `LowerMap`); recommend one owner, built on
  `zugriffe`/`ereignisse` (`RennfreiVoll.lean:499–502`).
- (c) IMAGE-ABI §11(c) and OBS-5 (i)–(iv) are the same hole (binding/
  kernel contract supply); both documents correctly refuse rather than
  assume. Blast radius: every real hosted image stays refused until
  binding contracts are supplied and proved.
- (d) Guardrail: IR block-stuttering "straight-line, no new back edge"
  must also cover lowering-introduced CAS-retry loops (a retry loop IS
  a machine-level back edge; needs shape-(i) bound or the progress
  argument does not close).
- Concrete two-thread traces given for: interleaved exchange lowering
  (B, plus the two-global-leaf generalisation), store buffering (A),
  tearing via misaligned 8-byte store (C instance).
- Unsupported target forms listed precisely (§7, 9 items); generic
  proof dependencies ordered (§8, 8 steps); no fairness assumption
  found in any of the three documents.

## What I believe is wrong (in the task or the audited docs)

- Nothing materially wrong in the three documents: references check
  out, open items are marked OPEN, no pre-conclusion on `Spec.lean`
  diffs (§6.9 correct).
- Terminology drift to watch: the audited docs say
  `Speichermodell/{Sicht, MaschineW, ...}` while the tree path is
  `grammatik/Grammatik/Speichermodell/*` — same files, path prefix
  differs by checkout root. Used full paths in the review.
- Task asked to "prove by source inspection the direction of claimed
  reuse": done as far as prose + premise-list inspection can prove —
  the actual simulation proof remains wave-B work, as stated in CUTS.

## Last `./lean-bau` result line

Not run: docs-only lane, zero Lean files touched (`git status` shows
only the two owned files). Per the lane task ("no gratuitous full
builds") a full `grammatik/` build to re-prove an untouched tree was
not started. Lean-code lanes own build-green evidence.

## Open / handoffs

- Wave-B order enforced by dependencies: 272-execution/279-decode/271-
  memory → accessList owner (§5.2) → lowering map → L-lemmas →
  `SchwachX` instantiation → legs; SCFG + rule register + vector
  correspondence in parallel once the TSO table exists; binding
  contracts (§11(c)/OBS-5(iv)) as the supply chain unblocking images.
- This lane's files are complete; no follow-up reserved by this lane.
