# Muse Report 485 — Independent exact-candidate review of 405

Clone `/home/simon/Dokumente/gabbro-muse/a485`, branch `muse/485` verified
(`git branch --show-current`). Candidate HEAD `b37ec86673d6cfade192070b649863ddd4e0465b`
is not present in this clone (isolated clones, no fetch); review performed
against the exact supplied `.tmp/review/SNAPSHOT.json`, `author-405/OWNER-TASK.md`,
`author-405/PATCH.diff`, the candidate document, and `BUILD-EVIDENCE.json`,
plus independent reproduction of every concrete claim against actual sources
in this clone via queued `./lean-probe` (temporary probes, removed afterwards).
OWN ONLY this file; nothing else touched (`git status` clean before writing it).

## What was checked

- Snapshot/patch congruence: `PATCH.diff` adds exactly the two snapshot files
  (`MUSE-REPORT-405.md`, `dokumente/x86/AUDIT-MEMORY-RANGES.md`), docs-only,
  no Lean/checker/emitter/goal/IR/ledger path touched. Owner-task scope
  (`dokumente/x86/AUDIT-MEMORY-RANGES.md` + report) respected.
- Every file/line citation verified against actual sources: `Regionen.lean`
  l.50/51 doc+`regionDisjunkt`, `Speicher.lean` ll.52-73/138-146/252-373,
  `Regionen.lean` ll.92-351/372-421/433-442, `SpeicherKommutation.lean`
  ll.64-142 + CUTS tail, `Stapel.lean` l.46 `rahmenOk` / ll.81-88
  `sichereWort`/`ladeWort`, `Zugriffe.lean` l.37 `stapelOben` / ll.540-548
  empty-type closers, `OverlapRefusal.lean` ll.87-98/119/143/229-234.
- Reproduced all six concrete `decide` claims as queued `./lean-probe`
  theorems, 0 errors: F1 empty-interior region `regionDisjunkt = false`;
  F2a wrapped frame `rahmenOk = false`; F2b `schlitzAddr 1 = 0` for
  `{basis := 2^64-8, tiefe := 32}`; F2c `sichereWort` through that frame
  still returns `some` (silent misplacement, permission-gated by the fully
  permissive `zeugenSpeicher`); P2 `fussEnthalten = false` for the wrapped
  top-region footprint; P3 same-set-reversed footprints classify
  `.unbekannt`. Absence claims verified by grep: no `rsp`/frame-linking
  lemma (F3), no interior-offset permission bridge — only the two base
  theorems `initialisiere_schreibbar8`/`_lesbar8` (F4), no `freiReserviere`
  freshness/disjointness theorem (F5).
- Hygiene: English only (German-word grep empty); no `sorry`/`admit`/`axiom`
  (grep hits are prose "admit/admitted"); no invented unaligned-CPU-fault
  claim; no closure/speed/hardware/full-validation claim; `Fuss`-list
  `.gleich` gloss and `freiReserviere_ohne_statik_gebunden` reading are
  accurate; `reserviere` zero-length/zero-alignment refusals and negative
  cases exist as cited. Severity grading is honest throughout (F1 cosmetic,
  F2 pitfall-not-soundness-bug, F3-F6 missing bridges/lemmas, none presented
  as a false theorem). `BUILD-EVIDENCE.json` transcripts are consistent with
  the queued wrappers; skipping `./lean-bau` is legitimate for a
  docs-only lane. One benign nit: `Stapel.lean` is 673 lines in current
  master vs the audit's older base, but every cited Stapel line still holds.

## Defects found

None. No hidden correctness assumption, no vacuity, no forged evidence, no
duplicated IR/executor, no safety weakening, no overclaim beyond the bounded
audit. Repair directions (F2 wrapper-or-obligation, F4 offset lemma, F3
`rspInRahmen` predicate, F5 tiny lemma, F1 one-sentence reword) are sound
and correctly pointed at consumer lanes, not at the audited modules.

## Scope

ACCEPT covers exactly the delivered bounded claim: the three memory-range
modules are correct within their stated claims, with findings F1-F6 and the
consumer-gap table as review evidence. Not covered: TSO bridge, lane-287 IR
interface, image loading — all explicitly excluded by the audit itself.

CANDIDATE: 405 b37ec86673d6cfade192070b649863ddd4e0465b
VERDICT: ACCEPT
