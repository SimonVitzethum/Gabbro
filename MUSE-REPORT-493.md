# MUSE-REPORT-493: Independent exact-candidate review of 413

Lane 493, clone `/home/simon/Dokumente/gabbro-muse/a493`, branch `muse/493` (verified).
Candidate 413 pinned HEAD `f9c642f0d330bd600308b498d0590a96be491a11`, base `0b3132b7`
(per `.tmp/review/SNAPSHOT.json`). Candidate object not present in this clone
(no network fetch per HARD RULES); reviewed via supplied
`.tmp/review/author-413/PATCH.diff` + file copies + `MUSE-REPORT-413.md` +
`BUILD-EVIDENCE.json`. PATCH touches exactly the two owned files, both new:
`MUSE-REPORT-413.md`, `dokumente/x86/AUDIT-BUDGET-OBSERVATIONS.md` — matches
SNAPSHOT `files` and `clean: true`. No other clone read.

## Task compliance

- OWN ONLY respected: PATCH adds only the audit + its report. No Lean, Rust,
  checker, Spec, goal, emitter, model, or friend file
  (`OptimizationRules.lean`/`OptimizationWitnesses.lean`) touched.
- Audit-only by design; no new definitions/theorems, so no `sorry`/`admit`/
  `axiom`/`native_decide`/`unsafe`, no witness obligation on the candidate.
- English only (checked: 0 umlauts, no German fragments in the 321-line audit).
- No duplicate broad review: §-scope explicitly excludes `REVIEW-GRUNDLAGEN.md`,
  `REVIEW-TSO.md`, `REVIEW-OPT-BINAER.md`, `REVIEW-QUELLE-INVARIANTEN.md` and
  counter-review 308; stays on budget/stops/waiting/observations/stutter.
- Trust boundaries respected: OS/gate access as user logic (D2), admission vs
  hardware fault distinguished (B4), no per-byte-TSO-as-atomicity, no invented
  silicon fault, no closed-lowering / final-byte / speed claim (CUTS §8 states
  doc proves no theorem, validation chain OPEN).
- Report honest about `./lean-bau` NOT run with justification (zero build
  inputs changed; doc-only commit). Acceptable; merger can rebuild cheaply.
- Build evidence (`BUILD-EVIDENCE.json`, 15 commands) shows ordered lane flow:
  probe re-runs, line-number re-verification, truncation repair, commit
  `f9c642f0`. No forged green: probes are private `.tmp/` (git-ignored),
  claimed `./lean-probe` 0 errors each.

## Semantic verification (independent, in this clone)

All load-bearing citations spot-checked against the tree; CUTS pins match
exactly (`InvariantenOpt:517`, `AufrufOpt:255`, `MulDiv:521`, `Byteschritt:452`,
`AccessList:238`, `TSO:551` — confirming the report's correction list):

- A1: `schritt : Decodiert → Zustand → Option Zustand` (`Ausfuehrung.lean:69`),
  `byteschritt : Zustand → ByteAusgang` (`Byteschritt.lean:70`), no budget/cost
  argument on any target step. Confirmed.
- E1 (load-bearing): `casSchritt` failure returns unchanged state + `false`
  (`LockedOps.lean:83-96`); `cas_fehlschlag_stottert` proves byte/buffer
  stutter; `casKosten versuche = versuche + 1` (line 107) is caller-supplied
  with no executed-stutters-to-`versuche` linkage; `cas_schleife_unbeschraenkt`
  (272-277) proves unboundedness; line 82 books stutter as safety-only.
  Real edge, honestly framed, correctly routed to C3 (347/385). Confirmed.
- E2: `lockKosten` has only `.xadd64`/`.mfence` arms (100-104); CAS
  contributes nothing. Real silent-drop edge for any `lockKosten` sum.
  Confirmed.
- E3: check-elimination equalities (`InvariantenOpt.lean:215-268`) carry no
  cost delta; CUTS:517 books cost/ghost-budget transfer OPEN. Same for
  inlining (A3, `AufrufOpt:255`). Real, routed to C3. Confirmed.
- B1/B2/B4/C1/C2/D1/D2: `ByteAusgang` has no halt ctor with both refusal
  directions proved; `hardwareHalt` names-but-does-not-map (header 159-163,
  CUTS:521); admission-never-fault sentence (`AccessList:265` inside CUTS:238);
  no-fairness CUTS (`TSO:551`); `zaunBereit` own-buffer-only with proved
  foreign-drain boundary. All confirmed as correct-within-claim / OPEN.
- Reproduced independently via queued `./lean-probe` (0 errors, this clone):
  `casKosten`/`lockKosten`/`cas_fehlschlag_stottert`/
  `cas_schleife_unbeschraenkt`/`schritt`/`byteschritt` signatures, and
  `md_div_halt`/`verweigert_heisst_halt` proving guard/trap agreement only.
  Probe claims credible. Scratch removed afterwards.
- "No CostSummary/GateStub/FenceDrain/ValidatorSkeleton at base" was true at
  `0b3132b7`; this clone (newer, post-480) now contains `CostSummary.lean`
  and `FenceDrain.lean`. Base drift, not audit error; audit pinned its base.

## Single defect (minor, non-load-bearing, repair direction stated)

§7/P3 "allocation gap": audit claims MulDiv CUTS's "bridge lane 277" has "no
row in `WORK-ALLOCATION.md` and no entry in `DIRECT-COMPILER.md` (grep,
2026-10-01)". Verified against BOTH the candidate base and this HEAD:
`DIRECT-COMPILER.md` DOES list lane 277 ("Generic source and user-duty
bridge", merged, commit `a3fc6f88`) — at base `0b3132b7` line 123 and at HEAD
line 148. `WORK-ALLOCATION.md` indeed has no 277 row (it tracks pending
344-349), so half the sentence is true. The lane exists and is merged; what
stays OPEN is the trap→`hardware` mapping work itself. Repair: one sentence —
drop "no entry in DIRECT-COMPILER.md" and rephrase as "mapping OPEN after
merged bridge 277; no dedicated trap-mapping row in WORK-ALLOCATION.md".
Does not affect E1-E3, verdicts, or C3/433/349 routing. No safety weakening,
no vacuity, no forged evidence, no invented bug for an OPEN bridge.

## Verdict rationale

The precisely delivered bounded claim — adversarial budget/observation audit,
no false theorem, three real edges (E1 load-bearing) landing on pending C3,
all other bridges OPEN and allocated — is materially correct and
independently reproduced. The one defect is a side-remark mis-grep with a
fully specified one-sentence fix, suitable as merger follow-up.

CANDIDATE: 413 f9c642f0d330bd600308b498d0590a96be491a11
VERDICT: ACCEPT
