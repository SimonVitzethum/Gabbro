# MUSE-REPORT-977: Exact review of author 827 (entry-to-mapping closing)

CANDIDATE: 827 db00126cff328ab888e7ae8ca2ccf9015f640f46

VERDICT: ACCEPT

## Scope checked

- Snapshot base `e7c75908` matches this clone's checkout; pinned HEAD `db00126c`
  touches exactly three files: `MUSE-REPORT-827.md`,
  `grammatik/Grammatik.lean` (one import line), and new file
  `grammatik/Grammatik/X86/ComposeEntryMap.lean` (287 lines, verified full read).
- No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## What the candidate does

- `composeEntryMap` conjoins three accepted legs: `eintrittZulassung`,
  `valX86`, and `(fetchDekodiert ..).isSome`. A `Bool`, never a fault claim.
- TARGET `ComposeEntryMap_verbindung` (generic over arbitrary admitted inputs):
  closed admission + fetched `(d, rest)` + successful `schritt` yields RIP
  executability through the CHECKED `geladen` mapping AND
  `byteschritt = .weiter s'`, via `zulassung_rip_ausfuehrbar` and
  `byteschritt_weiter`. No decoder/executor duplicated, no internals re-proved.
- Companion `ComposeEntryMap_verbindung_zeuge` instantiates every TARGET
  premise jointly (`.p48`, `valZeuge`, bias 0, `.hostedMain`,
  `zeugenEintrittAusf`, `[schreibTor]`, `(ret,1)`, `[]`, `schrittRet`
  successor via `schritt_ret_erfolg`), derives the conclusion through the
  TARGET theorem itself, and adds: reached source run (`RufErreichbarG`,
  table-writing `(eD.signatur eSetze).schreibt () = true`, `ReqAmEintritt` at
  place, via `vertragStandort_lauf_zeuge`) plus a real eight-byte x86 memory
  change (`write_read_zeuge`, bytes differ). Non-degenerate on both legs.
- Refusals: three generic theorems (unlisted RIP, refused gate member,
  missing decoded start; every premise used) plus four planted `decide`
  refusals (unlisted RIP, clobbered gate, W^X image, and the strongest one:
  mapping+entry+skeleton+gate hold yet closed entry refuses because the state
  memory grants no execute permission, so there is no decoded start).

## Independent reproduction (queued wrappers, read-only)

- `./lean-probe` on the exact snapshot file
  (`.tmp/review/author-827/grammatik/Grammatik/X86/ComposeEntryMap.lean`,
  imports resolving to this clone's base modules): 0 errors, exit 0.
  Axiom printout reproduced exactly and matches BUILD-EVIDENCE: all
  `[propext]`, two with `+ Quot.sound`, joint witness
  `[propext, Classical.choice, Quot.sound]` — every set a subset of the
  standard `gabbro_ziel` axioms.
- `./lean-bau` on this clone (base, report-only lane, no source owned):
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (508 jobs)`. Candidate's evidence reports
  509 jobs green; the delta of exactly one job matches the one new module.
- Grep over the candidate file: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` (only English words "admitted"/"admission"); no `intro _`,
  no `have _ :=`; no `Prop`-typed premises; TARGET statement not weakened
  (fixed shape: admission + fetch + step implies executability + byte step).
- All reused names verified present in base with matching shapes:
  `eintrittZulassung`, `zulassung_rip_ausfuehrbar`,
  `zulassung_verweigert_unlisted/tor`, `zulassung_fetch_ret`,
  `zulassung_schritt_ret`, `zeugenEintrittAusf`, `zulassungSpeicher`,
  `valX86`, `valX86_wohlgeformt`, `valZeuge`, `valWx`, `fetchDekodiert`,
  `byteschritt_weiter`, `schritt_ret_erfolg`, `vertragStandort_lauf_zeuge`,
  `write_read_zeuge`, `schreibTor`, `torAusClobber`, `torOkB`, `geladen`,
  `wohlgeformt`, `eintragGelisted`, `ausgangRip`, `schrittRet`, `laengeOk`.
- Architecture semantics confirmed by reading producers: `fetchDekodiert` /
  `byteschritt` read the STATE memory (`s.speicher`, fetch gated on
  `ausfuehrbarN` of the consumed prefix), while the executability conclusion
  goes through the CHECKED image mapping (`geladen bild bias`). The candidate
  never claims the two memories agree — the conclusion is a conjunction of
  the two legs, and the no-execute witness refusal pins exactly their meeting
  point. No invented determinism, no zeroed/ignored defined effects, no
  desired-correctness premise, no guarantee weakened. Byte forms, REX,
  flags, TSO/atomicity, MXCSR/IF gates: all inherited from accepted modules
  by name; the candidate adds no hardware-semantics claim of its own.

## Precise claim boundary (bounded acceptance)

- Single composed FIRST step only; the witness `ret` changes control state
  (rip/rsp, `ausgangRip = some 0`), while memory-change evidence is adjacent
  (source table write + `write64`/`read64` pair), not through the `ret`
  itself. This matches the task (`ZEUGE` satisfied via joint source run +
  real x86 memory change) and is stated as a bound, not a defect.
- OPEN per file CUTS with owners named: source-to-entry lowering (IR lane
  287, QUELLBRUECKE), per-access TSO/GX simulation (lanes 567/573-574),
  multi-step/relocation/callee-template legs; no hardware, cost/time, or
  termination claims. No fake closure: nothing open is used as a premise.

## Task assessment

Nothing in the owner task appears wrong. The "no second loader" and
"conjunction is not execution" requirements are met: state memory and image
mapping stay distinct legs, and the composed step genuinely executes
`byteschritt` on a fetched instruction rather than restating the conjunction.

## Remaining open (not this lane)

Integration of the candidate (merge + serial publication) belongs to the
coordinator/watch, not to this report-only review. No repairs requested:
no minimal-repair list, candidate accepted as pinned.
