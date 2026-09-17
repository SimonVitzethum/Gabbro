# MUSE-REPORT-208 — Rust checker vs Lean checker Bool `Akzeptiert` (TODO §1.2)

Lane 208, branch `muse/208`. Task: implement the missing `Akzeptiert`
components in Rust (call-graph closure, lock floors, `sperrOrte`,
`einzeln`, then whatever the diff shows), with sentences, probes and a
measured corpus diff.

## Result in one paragraph

No new checker rule was needed, and none was built -- deliberately, not
from reticence. Of the nine `Akzeptiert` components, five are decided by
existing Rust rules with zero disagreements, and the other four
(`abg`, `stufen`, `sperrOrte`, `antworten`) are vacuous on every exported
program BY CONSTRUCTION of the exporter, so a Rust rule for them could
never fire; building one would be decorative. What this lane delivers
instead: (1) the vacuity mechanism of each, verified against the code and
recorded in the measure itself; (2) a coverage table in
`instrumente/pruefe-akzeptiert-diff.py` that reports the denominator
honestly; (3) two committed positive agreement probes on concurrent
shapes outside the previous 17; (4) the finding that the
`stufen → N294` mapping in the script was wrong (different properties)
and that `N317`-`N319` are phantom codes; (5) -- round 2 -- a
MACHINE-CHECKABLE pin of each vacuity (`pruefe_konstruktion`, K1-K4,
exit 2 on drift) instead of prose. Disagreement count
before/after: **0 → 0** (`compared=19 skip=182 partial=1 findings=0
not-measured=0`, identical verdict logic).

## Round 2 (review findings F1-F3, all addressed)

- **F1 (blocking): vacuity unpinned.** Taken as option (b): no
  never-firing rules. New function `pruefe_konstruktion(export, parsed)`
  in the diff script asserts the four cited construction facts on EVERY
  export that parses, before any verdict:
  - K1 (`antworten`): `Ax := Empty` and `Reg := Empty` in the export
    text -- no answer site exists (`lean_g.rs`:4571,4576).
  - K2 (`sperrOrte`): `S.orte` vs `D.braucht`/`D.gbraucht` name the same
    guards in BOTH directions, parsed off the `orte`/`braucht`/
    `gbraucht` arms.
  - K3 (`stufen`): where locks exist, every `boden :=` is `some` --
    `resolve_floors` (`lean_g.rs`:1826-1858) never writes `none`
    (full minimality is decided by the Lean `stufen` probe itself).
  - K4 (`abg`): every `GFn.X` named anywhere is a declared member --
    no call leaves the member list (the premise the `reachB`
    fixpoint closure needs).
  Any violation prints `KONSTRUKTION: <file> -- <K...>` and the run
  exits 2: the measure no longer measures, and no verdict above may be
  read as agreement. Negative-tested on mutated exports (each Kn fires
  on its drift, baseline silent -- see verification). Plus a `pin:`
  tally: every component evaluated `true` on 18/18 comparable programs.
- **F2 (blocking): uncommitted evidence.** Both scratch shapes are now
  committed as positive agreement probes (NOT gifts -- they are not
  refusals): `messung/proben/probe-akzeptiert-diff-guarded.gab`
  (guarded write-write, `sperrOrte`/`renn` non-trivial with guards)
  and `messung/proben/probe-akzeptiert-diff-deepchain.gab` (3-deep
  chain, the 124 shape, second lock). Both read
  `rust=accept lean=accept agree` in the committed run. Denominator
  ownership checked: the chain count walks only `beispiele/*.gab`
  (`zaehle-kette.py`:526), the emission script runs a named file list
  only, and no Rust test enumerates `messung/proben/*.gab` top level
  (`fmt_views.rs` walks beispiele/gift/fragmente; `korpus.rs` only
  `zeugnis-c2/`) -- so neither the chain count nor any emission
  counter moves. The old `.tmp/` scratch section below is superseded
  by these two files.
- **F3 (minor): `stufen` row.** Code list set to `None` (vacuous, like
  `abg`/`sperrOrte`); `N294` stays listed only under `fuss`. Third
  tuple element is verdict-inert (read as `_`), confirmed by the
  re-run: same `compared=` line shape, selbsttest ok both directions.

## What was changed (three files)

- `instrumente/pruefe-akzeptiert-diff.py`:
  - `pruefe_konstruktion` (K1-K4, round 2) + `KONSTRUKTION:` output +
    exit 2 on drift + `pin:` per-component tally (see Round 2 above).
  - `stufen` row codes `["N294"]` → `None` (F3).
  - `KOMPONENTEN` comments now record the lane-208 vacuity mechanism per
    component (fixpoint / minimum-floor / one-source / no-Ax-Reg-sites).
  - `stufen` row corrected: `N294` decides the signature-held take rule
    (the `H006` shape, also enforced at export by `tr_locks`/`LG004`),
    NOT `stufenB` -- `stufenB` proper is vacuous by the minimum-floor
    construction.
  - `AKZEPTIERT_CODES` comment: `N317`-`N319` are phantom codes
    (reserved, implemented nowhere, firing on nothing); kept in the set
    so a future rule is read with no script change.
  - New coverage block: per compared program
    `deckt: <file> (starts=… locks=… tables=… fns=…)` plus aggregates --
    `wurzeln(>=1 start)`, `einzeln/renn/fuss-thread-legs(>=2 starts)`,
    `stufen/sperrOrte(>=1 lock)`, `renn(>=1 table)` -- and a line stating
    `abg`/`antworten` are vacuous on every export. Verdict logic, exit
    codes and the `compared=` line are byte-identical (no consumer parses
    the new lines; grepped, only the script itself mentions them).

- `messung/proben/probe-akzeptiert-diff-guarded.gab` (new): committed
  positive agreement probe, 6 items, 0 errors, `rust=accept lean=accept
  agree` (F2).
- `messung/proben/probe-akzeptiert-diff-deepchain.gab` (new): committed
  positive agreement probe, 10 items, 0 errors, `rust=accept
  lean=accept agree` (F2).

No new definitions, theorems, diagnostic codes or sentences.
`saetze.rs` untouched. Forbidden files untouched (`lean_g.rs`,
`obligations_g.rs`, `gegenbeispiel.rs`, `emit.rs`, `MARKE_EMIT*`,
`beispiele/124-two-threads-private.gab`). No Lean file touched. No
reserved code or gift number used (`N317`-`N319` phantom, `N324`-`N329`
and gift `989` stay free).

## Per-component findings (the actual lane work)

| component | Rust side | finding |
|---|---|---|
| `frag` | `LG004` export refusals (+`N293` indirect leg) | exporter-enforced; nothing to build |
| `abg` | none | VACUOUS: `reachB` runs `fs.length` rounds of `erreichSchritt` over `ruftB`, the same relation `rufM` closes over (`ZielOrtMehrfaden.lean`:95-147) -- every computed graph is closed on every export |
| `fuss` | `N290`-`N294` | real rules; agree. `Getrennt` ≡ `N301` over unordered pairs; Rust graphs OVER-approximate Lean's at indirect calls (whole address-taken pool vs sig-matching subset, `fusswache2.rs`:278-302) -- the safe direction |
| `stufen` | none for `stufenB`; `N294` is the held-take rule | VACUOUS: `resolve_floors` (`lean_g.rs`:1826-1858) writes each floor as the minimum rank taken anywhere in the reachable set, so `mE (bodenM f)` holds per body by construction |
| `sperrOrte` | none (`LG005` for unknown `protects`) | VACUOUS: `S.orte` and `D.braucht`/`D.gbraucht` are built from the one `LockModel.guards` set (`read_lock`, `lean_g.rs`:1765-1791; emission `:4520-4558`) |
| `wurzeln` | `N302`/`N303` | complete per-start checks; agree |
| `einzeln` | `N304` (busy) + `N315` (idle) | complete; agree. Gift 976 pins the refuse direction (never exports, by design) |
| `renn` | `N300`/`N301` | agree on exports. Atomic/per-core exemptions are vacuous there: atomics never export (`atomar := fun _ => false`, `Accumulates` is `LG...`), so the Lean side never sees an exempt carrier the Rust side skips |
| `antworten` | `N310`-`N316` | VACUOUS on exports (axiom calls write `Ax := Empty`, register accesses have no `Reg` form -- both export refusals); refuse direction pinned by gifts 972-977, not by the diff |

## Agreement probes (committed, round 2 -- supersedes the round-1 scratch)

- `messung/proben/probe-akzeptiert-diff-guarded.gab`: two starts writing
  one guarded table under the lock. Rust: 6 items, 0 errors. Lean: all
  10 checks `true`. AGREE (exercises `sperrOrte`/`renn` non-trivially
  with guards present).
- `messung/proben/probe-akzeptiert-diff-deepchain.gab`: 3-deep call
  chain (`start_a → mittel → tief`, lock taken at top, held by
  signature below -- the 124 shape) plus a second lock. Rust: 10 items,
  0 errors. Lean: all 10 checks `true`. AGREE (exercises `abg` over
  longer chains, `stufen` over transitive floors).
- The round-1 `.tmp/` files of the same shapes are deleted; they were
  never committed.
- Incidental observations (out of scope, not acted on): `gabbro lean-g`
  exits 0 with empty stdout on checker-refused files (e.g. gifts 964,
  976) instead of nonzero -- the diff's `ABBRUCH: export parses not`
  tripwire would fire if such a file were ever walked; and a transitive
  `locks L` in effects without take-or-hold refuses at export (`LG001`),
  which forced the E4 restructure and confirms the discipline is
  exporter-enforced.

## Verification (round 2 numbers)

- `python3 instrumente/pruefe-akzeptiert-diff.py --selbsttest`: ok (both
  directions, re-run after the F3 edit).
- Full diff: `compared=19 skip=182 partial=1 findings=0
  not-measured=0`, no `KONSTRUKTION:` line (K1-K4 hold on all 19
  exports); coverage of 18 comparable: `wurzeln: 4 |
  einzeln/renn/thread-legs: 4 | stufen/sperrOrte: 6 |
  renn-with-table: 11`; `pin:` every component true on 18/18.
- Tripwire negative test (mutated scratch exports, function level):
  baseline silent; each Kn fires on its drift (Ax gone → K1;
  braucht mismatch → K2 both directions; `boden := none` → K3;
  undeclared `GFn.*` → K4).
- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, all `test
  result: ok`, 0 failed; re-run round 2 -- no Rust change, but two new
  corpus files).
- `python3 instrumente/pruefe-englisch.py`, `pruefe-saetze.py`: green
  (re-run round 2).
- Lean: no Lean file added or changed, so no `./lean-bau` impact; Lean
  evidence is the selbsttest plus the 19 `lean-probe` runs above
  (18 comparable + 1 partial), all green.

## Reservations: collision, and what I used

The task reserves diagnostic codes `N320`-`N329` and gift numbers
`980`-`989` for this lane. Both ranges are TAKEN in this tree by the
2026-09-16 mixed-stand merge (`N320` section-at-function, `N321`
never-asm, `N322` syscall-costs, `N323` lock-primitive-contract;
gifts 980-988). `AGENTS.md` §7 (next free `N320`/gift `980`) is stale
for the same reason. I used NONE of these numbers and built no rule, so
no collision results; free for future transfer work are `N317`-`N319`
(phantom, in the diff's accept set), `N324`-`N329` and gift `989`.

## What I believe is wrong (in the task or around it)

1. The task's component list ("call-graph closure, lock floors,
   `sperrOrte`, `einzeln`") presupposes all four lack Rust counterparts
   and need building. `einzeln` is fully built (`N304`/`N315`, lane 196);
   the other three need no rules for the structural reasons above. A
   verdict that says "built" for them would be false; this report says
   "not needed, with mechanism" instead (rule 4: plain statement).
2. The wave-5 preamble of the lane prompt declares this lane an
   independent reviewer that must not change any existing file -- while
   the lane-208 task itself orders code changes, sentences and probes.
   The specific task wins over the generic preamble; I followed the
   lane-208 task and changed exactly one instrument file. If the
   reviewer reading was intended, this report still serves as the
   verdict file: the verdict is "the goal-side correspondence holds on
   the measured denominator, with the four vacuity arguments above".
3. The `compared=19` denominator is still the real weakness, and the
   rest belongs to exporter coverage (lane 198), not to this lane: 182
   of 202 walked files never export. This lane added two probes under
   `messung/proben/` (chain count walks only `beispiele/*.gab`, emission
   runs a named list) -- that was the most that could be done without
   moving another guardian's denominator, and it doubled the thread-
   component denominator (2 → 4).

## Open

- Raise the comparable denominator via exporter width (lane 198): every
  newly exporting concurrent program automatically lands in this diff.
- If a future transfer rule takes `N317`-`N319`, the diff reads it with
  no change; it then owes sentence + poison/positive probes per rule 14
  of the lane family.
- `lean-g` exit-0-on-refusal (above) is worth a lane of its own; I did
  not touch it (`lean_g.rs` forbidden).
