# MUSE-REPORT-249 — spill-read rule: child reading caller-frame state

Lane 249 (Teil 3 gate, TODO §-1, O-1 open item 2). Branch `muse/249`.
All builds on fisch (this machine); nothing built elsewhere.

## 0. What the task asked, and what this lane delivers

O-1 left one checker hole beside the clone handoff: a `child` block
reading caller-frame state was unchecked. The child runs on the handed
stack, not in the caller frame, so a caller name the gate never handed
is a dead slot on the child path. This lane builds the refusal as a
dataflow over the shared read set vs the caller scope -- not a second
effects system -- in the file O-1 owns (`clone.rs`, yours-alone per the
task), with its sentence in `saetze.rs` in the same commit, and probes
in both directions.

Round 1 built the rule function-wide; review round 1 (lane 368, F1/F2
below) moved it to prefix-handed and Satz-conformant shadowing. The
shipped shape:

- the rule + dataflow (`clone.rs`): `N451` (caller `let`-temporary,
  gate answer with it) and `N452` (caller parameter / loop / match
  binder), each refused by name, against the handed PREFIX (calls
  preceding the region in program order);
- four poison probes (`1113` N451 incl. shadow; `1115`, `1116`, `1117`
  N452) and one positive probe (`1114`, checker-clean,
  `-- erwartet: C185`);
- two narrowed old probes (`1109`, `1110`: incidental caller reads
  replaced by literals, each back on its own code);
- `./cargo-pruef` zero failures, emission ALL PASS, Lean untouched
  and green.

`emit.rs`, Lean, `MARKE_EMIT*` and OS constants untouched, as ordered.
`clone.rs` is the only checker file changed.

## 1. The rule (exact names)

In `crates/gabbro-check/src/clone.rs`, beside `N446`–`N450`:

- `RuferKontext { lets, umfang }` — per enclosing function: `lets` =
  every `let`-family name bound outside any `child` region (`Let`,
  `LetSonst` value + error name, `Alloc`, `AwaitLoad`, `Exchange`);
  `umfang` = parameters + `Traverse.variable` + `MatchZweig.binder`
  outside any region.
- `sammel_anrufer` — caller bindings, stopping at `Child` (a nested
  region binds the handed stack's locals, never the caller's).
- `spill_block` + `sammel_stmt_uebergeben` + `ruf_uebergabe` +
  `expr_uebergabe` + `ort_uebergabe` — the handed PREFIX: each
  statement's stack-gate calls join the set every later region reads;
  each subblock is walked with its own clone, so a call in one branch
  hands nothing to a region in its sibling. The handed slot is the
  bare-place argument at the stack parameter's position (parentheses
  seen through; computed arguments hand nothing, fail-safe).
  Gate map is short-name → stack-parameter index over gates with
  exactly one `stack` clause whose stack register matches a `regs in`
  pair (a faulted gate hands nothing; its own fault names it).
  Predicates carry no handoff (not executed state).
- `spillregion` — the outermost regions `kindpfade` refuses. Read set
  is the shared `crate::emit::benutzte_namen` (the `(void)k;` walker
  O-1 already trusts for the child path) minus the handed prefix;
  the remainder against `lets` → `N451`, against `umfang` → `N452`.
  Region binds are NOT counted off (option (a), Satz-conformant). One
  refusal per offending name per region, at the region span, in name
  order (`BTreeSet`). A write target counts as a mention.
- Mootness: with no stack gate in the unit (`tore_mit_stapel == 0`)
  nothing fires here — `N450` is the fault (verified: `1111` stays
  `N450 allein`).

In `crates/gabbro-check/src/saetze.rs`: `Satz { name:
"klon.spill", kennungen: &["N451", "N452"], … }` directly after
`klon.uebergabe`, with five named edges as `vorbehalt` (faulted gate;
short-name resolution; N450 mootness; post-region/sibling calls;
loop-back-edge).

Reserves verified at start, all free: no `N451`+ in `crates/`,
max gift `1112`. Consumed: `N451`, `N452`; gifts `1113`–`1117`
(`1117` verified free in round 2 before taking it).
Spare and reported: `N453`–`N455`, no gift spare left of the block.

## 2. Probes and narrowings (corpus verdict diff, measured)

| file | verdict before → after | subject |
|---|---|---|
| `beispiele/155`, `156` | clean → clean | handed `stapel` read stays legal |
| `gift/1109` | `N448` + new `N452` → narrowed to `return 1;`, `N448 allein` | return out of the path |
| `gift/1110` | `N449` + new `N452` → narrowed to `let s = 0;`, `N449 allein` | fall-through |
| `gift/1111` | `N450 allein` → unchanged | no gate (mootness) |
| `gift/1112` | checker-clean → unchanged | emitter refusal |
| `gift/1113` NEW | `-- erwartet: N451 allein`, falls once (`ausgang(v)`; round 2 adds the shadow `let v = 7` + reread — both orders refuse under the one code) | gate-answer / return slot + shadowing |
| `gift/1114` NEW | `-- erwartet: C185`, checker silent (worker-call shape) | legal handed read |
| `gift/1115` NEW | `-- erwartet: N452 allein`, falls once (`ausgang(art)`) | unhanded parameter |
| `gift/1116` NEW | `-- erwartet: N452 allein`, falls once | same value, different slot (gate took `s2`, child reads `stapel`) |
| `gift/1117` NEW (round 2) | `-- erwartet: N452 allein`, falls once | handoff call AFTER the region hands nothing |

Every new refusal is real: without its rule the emitted C of `1113`,
`1115`, `1116`, `1117` is valid `cc -Werror` input (each header states the
counterfactual; the `allein` harness checks it). `1116` pins that
handedness is by slot, not by name — a name-matching rule would stay
wrongly silent there; `1117` pins that it is by prefix, not by
function — a function-wide set would stay wrongly silent there.

No other corpus file moved: `jedes_beispiel_geht_sauber_durch` and
`jedes_gift_faellt_mit_seinem_code` green in the full run.

## 3. Measurements (exact lines, round-2 rerun)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (round 1 twice,
  round 2 twice: after the fixes, and after Satz + `1117` + `1113`
  extension).
- `python3 instrumente/pruefe-saetze.py`: exit 0 —
  `425 Kennungen, 176 Saetze, 55 ohne Satz, 0 erfunden`.
- `python3 instrumente/pruefe-kennungen.py`: `KENNUNGEN: ALL PASS`,
  `QUELLENVERTRAUEN: ALL PASS`.
- `python3 instrumente/zaehle-gifttreffer.py`: 734 files (729 + 5 new);
  begleitet 160, **verdeckt 41 — unchanged** (pre-existing drift per
  OPUS-BERICHT-CLONE, none mine); FEHLT 5 → 7 = `1112` + new `1114`
  (the emitter-code class, checker-silent by construction).
  `--lang` confirms `1109`/`1110`/`1111`/`1113`/`1115`/`1116`/`1117`
  sauber. Marks re-booked by the merger, as with O-1.
- `./emission-pruef`: `== exit 0`, `EMISSION: ALL PASS`
  (37 durchgestochen, 286/286). `MARKE_EMIT*` untouched: all five new
  files refuse at CLI level (checker errors / `C185`).
- `./lean-bau`: `Build completed successfully (280 jobs)` (no Lean
  file touched; the line the lane rules ask for).

## 4. The outlining alternative — decided, not deferred

The alternative (OPUS-BERICHT-CLONE open item 2): make the child body
closed by construction — outline it so no caller name is in scope and
the spill question moots itself. **Refused with measurement**, for
three reasons:

1. It is unbuildable inside this lane's scope: closing the body needs
   either a new explicit-handoff syntax (parser + AST, not owned here)
   or refusing ALL caller reads, which orphans the positives
   (`155`/`156`/`1112` all read handed `stapel`) with no legal shape
   left to rewrite them into.
2. No soundness hole is open meanwhile: every `child` block is refused
   at the emitter (`C185`), so no handoff runs while the dataflow holds
   the checker side; the inline-trap lowering (lane 252 queue) is where
   a closed-body requirement would belong if the lowering needs it.
3. The dataflow keeps the corpus green with two literal narrowings,
   while strict outlining would move three clean files to red with no
   replacement shape.

Handoff note for lane 252: if the inline-trap lowering needs the child
body closed (no caller reads at all, handed values as explicit block
parameters), that is a syntax + lowering change, and this rule's
`uebergeben` set is the specification of which names the parameters
must carry.

## 5. What is NOT in this lane (open / for the merger)

- `N453`–`N455`: spare, unassigned. Gift block `1113`–`1117` fully
  spent (`1117` taken in round 2 after re-verifying next-free).
- Docs: `SYNTAX.md` §12.1 and `SATZKARTE.md` §39 still describe
  `N446`–`N450` only — out of scope here (`clone.rs`, `saetze.rs`,
  tests/probes only); the spill sentences belong there at merge.
- Lean: no model change per the task (the handoff premise (d2) is
  O-1's; a spill leg from the lowering is §2 work).
- The `allein` counterfactuals assume the emitter keeps writing the
  child block best-effort beside `C185`; the day it stops, the four
  poison probes ask to be re-classified (same mechanism as `662`).

## 6. Review round 1 (lane 368) — F1/F2, both fixed here

- **F1 (handed set function-wide):** reproduced (`0 errors` on the
  post-region handoff), fixed by carrying the handed PREFIX down
  `spill_block` — sibling branches cloned, region reads only what
  precedes it. Pinned by new probe `1117`; `155`/`156`/`1114`
  re-verified silent (their handing calls precede their regions).
- **F2 (shadowing):** reproduced (pre-definition read silent), fixed
  with option (a) — region binds not counted off, exactly what the
  (already-merged) vorbehalt (4) promised, so claim and code agree
  without a sentence change in that leg. The benign shadow pays the
  same refusal (soundness first); pinned by extending `1113` with
  both orders under the one code. Option (b) declined: it needs a
  parallel position-tracking walker beside `benutzte_namen`, and this
  tree's own lesson (`emit.rs`, W7) is that two implementations of one
  question drift.

## 7. What I believe is wrong in this task

- Nothing load-bearing. Two notes: (a) the wave preamble says the lane
  is an independent reviewer that changes no file, while §-1 and the
  lane task order the rule built — I built it, since the task's
  deliverable and reserves are explicit; (b) the reserves (`N451`–`N455`
  for a two-code rule) are generous — two codes sufficed, and the spare
  half is booked above rather than spent.
