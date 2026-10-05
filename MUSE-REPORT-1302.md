# MUSE-REPORT-1302.md

Lane 1302: independent exact review of candidate 1301 (WC ordering:
cross-core eviction order and CLFLUSHOPT/CLWB).

Candidate: lane 1301, pinned HEAD
`be7b1559194fd2d7fb261e81125d5365e9b736a0`, base
`234f2728a718157cba0e1f9e0ef300874b34ea6a`. Changed files (per
`.tmp/review/SNAPSHOT.json`): `MUSE-REPORT-1301.md`,
`grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/HwWcOrdering.lean` (new, 1382 lines).

## Checks performed

- `./lean-probe` on the delivered candidate file
  (`.tmp/review/author-1301/grammatik/Grammatik/X86/HwWcOrdering.lean`,
  probed in place; a `cp` into the clone was blocked by the permission
  classifier, and the wrapper resolves imports via `lake env` regardless
  of the file's location): `== 0 error(s) in the COMPLETE output`.
- Forbidden tactics: grepped for
  `sorry|admit|native_decide|sorryAx|unsafe|axiom ` — only English
  prose "admitted" (8 matches, all comments). No `intro _`,
  no `have _ :=`, no Prop-typed premises.
- `#print axioms`: every main theorem depends only on `propext`
  (plus `Quot.sound` exactly where the reused 1287 fence lemmas carry
  it: `hwWcOrdZaun_leer1301`, `hwWcOrd_verbindung1301`). Standard.
- Existing files: PATCH shows only the single
  `import Grammatik.X86.HwWcOrdering` line added to
  `grammatik/Grammatik.lean`. Nothing else touched.
- Evaluator lifted, not copied: WC-store/fence steps call
  `HwMemWC1287.wcStoreZugriff` / `wcZaunZustand` by reference;
  eviction/read/flush frames go through `wcSpeicherSchreibe`,
  `wcLesbar`, `wcLinieSpuele`, `inLinie` and the accepted
  bypass/frame lemmas; exact plug agreement
  `adapterEvict_stimmt_ueberein1301` proved.
- Premise usage: verified by reading the proofs. The connection
  theorem `hwWcOrd_verbindung1301` uses all 23 premises (steps
  h1–h6, observations, refusals via hgift1–4, both named pin
  assumptions, the wf chain). Smaller theorems use theirs directly.
- Refusals really refuse (all green under `decide`/rewrites):
  `hwWcOrdEvict_leer_verweigert1301`,
  `hwWcOrdFlush_ohneBit1301`, `hwWcOrdFlush_ohneRecht1301`,
  `hwWcOrdStore_falscherTyp1301`, decoder pins
  (`pin_flush_register_verweigert1301`,
  `pin_clflush_kein_opt_wb1301`, `pin_flush_lock_verweigert1301`,
  `pin_opt_nicht_wb1301`).
- Witness non-degenerate: `hwWcOrd_verbindung1301_zeuge`
  discharges all 23 premises jointly on the reached run
  witM0–witM6: two cores (owner reads 42/43, foreign core reads 0),
  two memory-changing steps (fence installs 42, spontaneous eviction
  installs 43).
- Silicon facts checked against
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`:
  CLFLUSHOPT `NFx 66 0F AE /7`, CLWB `66 0F AE /6` (both memory
  form); ordered wrt fences/locked RMW/older writes, unordered wrt
  other flushes/younger writes; byte-load faults with execute-only
  allowed; #UD without the CPUID bit; WC buffer separate from
  caches/store buffer, not snooped, implementation-dependent
  eviction, weakly ordered with bus reordering allowed. Decoder pin
  bytes verified (ModRM 56 = mod0/reg7, 48 = mod0/reg6; mod3 rows
  248/240 refused). The model claims no cross-core eviction order
  beyond the named count assumption — exactly what the SDM permits.
- CUTS honest: no hardware-correspondence claim, no W/GX claim, no
  source/checker/Spec/goal/emitter correspondence; open items
  (non-temporal stores, PREFETCHW, CLDEMOTE, cross-type read
  ordering) listed.
- `./lean-bau` on this clean clone (candidate not copied in):
  `Build completed successfully (687 jobs).`

## Note (not a defect)

`wcEvictPinsLaenge1301`, `clflushoptZaunPinsLaenge1301` and
`clwbKeep_liest1301` are trivial projections of the three NAMED
assumptions (the task-mandated form for the unsupplied ordering
chapter, disclosed as assumptions in CUTS). They carry no
independent content, but they are presented as assumption plumbing,
not as results, and the connection theorem consumes them openly.
The byte decoders cover exact 4-byte shapes only (no SIB/
displacement); no wider decode coverage is claimed.

## VERDICT: ACCEPT

Candidate 1301 `be7b1559194fd2d7fb261e81125d5365e9b736a0`: ACCEPT.
No unsupported desired-correctness premises, no weakened
guarantees, no fake closure. The claimed scope (lifted WC machine
with oldest-first eviction, same-core WC read ordering, weakly
ordered CLFLUSHOPT/CLWB under named ordering assumptions, two-core
non-degenerate witness) is proved as stated.

## What remains open

Nothing from this review. The candidate's own CUTS (bus-order
beyond the count assumption, cross-type read ordering,
non-temporal/PREFETCHW/CLDEMOTE, W/GX and source correspondence)
stay open for future lanes.
