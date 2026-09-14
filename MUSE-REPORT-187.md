# Lane 187 — refusals that ship the fix (PLAN-EINFACHHEIT.md lever 4)

Written 2026-09-14. The rule of this wave (`dokumente/PLAN-EINFACHHEIT.md` §0): a
simplification is accepted only if the ceremony count goes DOWN (`gabbro zeremonie`)
and the pass register stays CONSTANT (every guarantee with its enforcing code,
`saetze.rs` / `messung/PASSREGISTER.md`). Both numbers are booked before and after
below; a change that moves the register is refused whatever it saves.

## 0. The booking (both numbers, before and after)

All figures name the command that recomputes them. The toolchain is present
(`./cargo-pruef`, `./lean-bau`, `./lean-probe` all ran green this lane -- see
§6), so every after-figure below is measured by running. The before-figures for
the binary-driven instruments are recomputed by same-method static counts (the
lane-167 precedent in `messung/PASSREGISTER.md` for the reading half), plus the
invariant that this lane changes no verdict -- the full `cargo test` is green,
including the clean-and-gift corpus in both directions -- and touches no `.gab`
file.

| figure | before | after | command |
|---|---|---|---|
| codes in the checker | 395 | 395 | `python3 instrumente/pruefe-kennungen.py` (green both ends) |
| sentences | 160 | 160 | `./target/debug/gabbro paesse` says `SENTENCES: 160 over 12 passes` (after); `saetze.rs` untouched, static struct count 161 both ends (one struct unattached -- predates the lane) |
| codes without a sentence (ratchet) | 55 | 55 | `./instrumente/pruefe-saetze.py` says `55 ohne Satz, 0 erfunden` (after); static replication before: 55 |
| refusal constructors (`Absage::fehler\|hinweis`) | 458 | 458 | static count over `crates/*/src/*.rs` minus `saetze.rs`, both ends |
| ceremony (clause sites over 119 files) | 1818 | 1818 | `./instrumente/zaehle-zeremonie.py` says `1818 Stellen` (after; 131 ableitbar, 0 redundant, 1577+96 tragend); before identical -- no `.gab` touched, corpus verdicts unchanged |
| mutation anchors alive | 382 of 409 | 382 of 409 | anchor census replicated statically, both ends; 27 dead before and after, 0 caused by this lane |

The register is constant: no new diagnostic codes, no new sentences, no moved
guarantee. `emit.rs` is untouched (not in the diff), so `MARKE_EMIT` is out of reach
by construction.

The §0 reading, stated openly: the ceremony count did NOT go down. This lane
removes no clause and demands none; it lowers the cost of a refusal, not the
clause count. Lever 4's value is on the machine-author side ("learn at once from
an applicable correction"), and the task's refusal rule -- book both numbers, and
refuse whatever moves the register -- is satisfied exactly. Whether that counts
as acceptance under §0's conjunction is for the wave owner; the numbers above
are what the decision is made on.

## 1. Measurement first: what fires on the gift corpus

Method: first-line `-- erwartet:` scan over `beispiele/gift/*.gab` (668 files),
same contract the corpus tests read. Head of the frequency table:

| code | gift probes | fixable here |
|---|---|---|
| C001 | 40 | no -- the emitter's unknown-form refusal names no edit |
| M104 | 17 | no -- which bound or narrow is a judgement |
| M101 | 14 | no |
| E008 | 13 | no -- a multi-entry hull obligation, not one named entry |
| M147 | 13 | no -- the re-read text is not determined |
| M103 | 12 | no |
| K001 | 12 | yes |
| P001 | 10 | yes |
| N030 | 7 | no |
| D012 | 7 | no -- restructuring the call, not an edit |
| N041 | 7 | no -- the replacement name is not determined |
| M109 | 7 | no |
| H012 | 6 | no |
| N240 | 6 | no |
| V001 | 6 | no -- the counterpart is elsewhere |
| N046 | 5 | no -- the full-line replacement would drop `effects` (measured against `cnamen.rs` rows) |
| N042 | 5 | no -- which side renames is a judgement |
| H022 | 5 | no -- the measure is unknown |
| H013 | 5 | no -- the declaration is elsewhere |
| N001 | 5 | no -- which declaration goes is a judgement |
| N069 | 5 | no |

The most frequent codes are overwhelmingly NOT uniquely fixable -- that is the
measurement result, and it is why the 20 below are not the top 20 by frequency.
Seventeen of the 20 fire on the gift corpus (all fixable firing codes the survey
found); three (`E003`, `L001`, `L004`) fire nowhere in the corpus and are covered
by inline sources in the tests, each noted as such.

## 2. The 20 fixes

Format: a diagnostic carries `fix: start..end -> replacement` (byte offsets into
the checked source; rendered under the refusal by `Absagen::zeige`). An empty
span inserts, an empty replacement deletes. `gabbro pruefe --fix <file>` applies
all fixes rear-to-front (ten rounds, early stop when a round applies nothing),
re-checks, and reports each applied edit plus the plain-run summary. `--fix`
with `--unit` or `--with` is refused (exit 2): both move spans out of the file
they would be applied to.

| code | gift probes | fix | probe used | post state |
|---|---|---|---|---|
| K001 | 12 | bound expr -> computed body cost | `34-kosten-ueberschritten.gab` | bound holds |
| P001 | 10 | insert expected token before token found | `623-statement-without-semicolon.gab` | parses (then `E005` fixes itself in the next round) |
| A005 | 3 | arch -> the single declared machine | `462-annahme-fuer-fremde-maschine.gab` | machine declared |
| F002 | 3 | insert `rounded` after literal | `84-literal-still-gerundet.gab` | rounding declared |
| E005 | 2 | append `writes ort` (replaces lone `pure`) | `28-pure-schreibt.gab` | entry declared |
| E010 | 2 | append `reads ort` (replaces lone `pure`) | `62-lesen-ohne-reads.gab` | entry declared |
| N016 | 2 | append `Has(m)` to `requires`, else fresh clause before `effects` | `127-axiom-merkmal-ungetragen.gab` | demand carried |
| S001 | 2 | label -> the single label in scope | `10-marke-fehlt.gab` | target exists |
| E006 | 1 | append `locks [shared] ort` | `30-sperre-nicht-erklaert.gab` | entry declared |
| E007 | 1 | `locks shared X` -> `locks X` | `41-geteilt-erklaert-exklusiv-genommen.gab` | declaration covers body |
| E011 | 1 | append `writes/reads ort` to `touches` | `117-touches-deckt-nicht.gab` | entry declared |
| E002 | 1 | delete second `pure` (comma goes with it) | inline (`pure, pure`); gift `13` pins the manual arm, see §3 | single `pure` |
| K012 | 1 | arch -> the single declared machine | `696-frist-ohne-maschine.gab` | machine declared |
| P033 | 1 | delete stray `;` | `624-block-form-with-trailing-semicolon.gab` | token gone |
| N202 | 1 | effects clause -> `effects { pure }` (present clause only) | `872-translator-with-effects.gab` | translator pure |
| N036 | 1 | delete uncarryable entry (lone entry -> `pure`) | `243-fnzeiger-verspricht-locks.gab` | type promises only what crosses |
| G002 | 1 | bare condition -> `TESTBUILD` | `312-when-auf-etwas-anderem.gab` | known build |
| E003 | 0 | append `diverges` (clause present only) | inline divergent fn | word carried |
| L001 | 0 | insert closing `"` at scan stop | inline `reason` | string closed |
| L004 | 0 | `0X`/`0B` -> `0x`/`0b` | inline `return 0X7;` | prefix known |

Shared machinery: `crates/gabbro-check/src/fix.rs` (`append_effect`,
`append_item`, `delete_entry`, `entry_spans`, `apply_fixes`, `fix_to_stable`).
No pass reads a fix back -- verdicts are identical with or without them.

## 3. Refused fixes (the safety rule at work)

Each of these was examined and gets no fix, with the reason. The standing cases:
`E001` (the hull content is unknown at the site -- inserting `pure` would be a
guess); `E002` contradiction arm (its own text offers two directions; gift probe
`13-pure-und-schreiben.gab` is pinned by a test to stay fix-free); `M148`
(`return` without value vs declaring a result -- two directions in its own
note); `N046` (the `cnamen.rs` `form` rows carry no `effects`; a full-line
replacement would drop the divergence promise); `K002`/`K004`, `H011` (the repair
sits in a declaration elsewhere); `S002`, `N212`, `H022`, `K008`, `S008`, `O010`
(the branch/proof content is unknown); `M107`, `M106` (values unknown);
`M125`/`D005` (the `exhaustive` word belongs on a declaration elsewhere);
`N035`, `N035`-adjacent, `N037`, `N061` (payload/region unknown); `G001`, `G003`,
`N038`, `N039` (which side moves is a judgement); `A006` (rewriting the machine
would change the subject under test); `H007`, `H020`, `H013`, `U003` (the guard
form/site is not unique text); `M104`, `M101`, `M103`, `M150`, `M141`, `M142`,
`M159/M160`, `R005`/`R006`, `R008`/`R013`, `L105`, `V001`/`V002`/`V007`,
`O001`/`O003`/`O004`/`O006`, `D004`, `D011`, `D012`, `D018`, `D025`, `D027`,
`N007`, `N011`, `N025`, `N040`, `N052`, `N054`, `N056`, `N063`-`N068`, `C180`,
`P002`, `P008`, `P034`, `P043`, `P044`, `L002`, `L005`-`L007`, `K003`, `K005`,
`K009`-`K011` (no unique mechanical edit at the site).

Designed but cut to hold the 20: `N026` (append `memory` to a non-empty
`clobbers` list) -- clean and conditional, first spare if the count is ever
raised. Deliberately unbuilt: `E008` (compositional hull -- many entries, no
single named one), `M147` (re-read text unknown), the `(void)`-style discard and
the unused binding from the assignment examples (no such refusal exists -- the
emitter lowers `(void)` itself and unused `let` is refused nowhere by decision,
so there is nothing to attach a fix to).

## 4. Tests

`crates/gabbro-check/tests/fix.rs`: 21 tests for the 20 codes (the `E002`
contradiction arm gets its own pinning test). Each fix test asserts three
things: the code fires before (or the probe drifted and the test says so), the
firing diagnostic carries a fix, and after `fix_to_stable` (ten rounds, the same
driver the CLI uses) the code fires no more -- clean or a different diagnostic.
What no test asserts is silence. No new gift files; the three inline sources are
marked as such in the file header.

## 5. Guardian impact (all measured)

- `pruefe-kennungen.py`: green, `395` codes before and after, no new literals.
- `pruefe-saetze.py`: full run green -- `395 Kennungen, 160 Saetze, 55 ohne
  Satz, 0 erfunden`. (One earlier run aborted on a stale binary after a `touch`
  during warning-hunting; rebuilt, re-run green -- the guardian was right.)
- `./instrumente/zaehle-zeremonie.py`: `1818 Stellen` over 119 files (131
  ableitbar, 0 redundant, 1577+96 tragend).
- `./cargo-pruef`: exit 0, 0 failing tests across all suites, including the 21
  new `fix` tests and the `fahnen` completeness test with the registered
  `--fix` flag. One warning in `certstmt.rs` (`DeclInfo` privacy) predates the
  lane -- the file is untouched.
- `./lean-bau`: green, 222 jobs, 0 errors. `./lean-probe
  grammatik/Grammatik.lean`: exit 0, 0 errors. (No `.lean` file touched; the
  probe is a smoke check.)
- `pruefe-vergabe.py`: `32` -> `35` candidates, `88` -> `93` probes, booked with
  dated entries in the file. Cause measured: no new refusal constructors
  (`458` on both trees); the lane's fix lines pushed the second `E002`/`E005`/`E010`
  arms out of their first arms' 600-character windows, un-merging three pairs
  the instrument used to read as one stelle each. The pairs were always two
  messages under one code; the old number was too small.
- Mutation anchors: 409 total, 27 dead before and after, 0 caused by this lane
  (one anchor broken mid-lane by a block placement and restored the same day;
  the census is re-run after every edit).
- `fahnen.rs`: `--fix` registered (English-only, no pair, no liveness argv --
  the flag rewrites its input, so no committed file may serve as its liveness
  probe).
- `pruefe-englisch.py`: aborts at the legacy-bulk stage before and after (7940
  vs 7943 German comment lines of ~35600); the lane delta contributes 0 German
  comment lines, measured with the tool's own `deutsch()`.
- `pruefe-klauseln.py`: red before and after in the same way (outdated table);
  it counts the new `fix.rs` as a 66th AST-reader file with an unchanged verdict.
  `pruefe-todo.py`: 12 findings before and after, byte-identical to HEAD
  (stale TODO/DONE figures from other lanes' corpus drift, e.g. 665 vs 668
  gift probes; needs `~/.cargo/bin` on PATH for its `cargo` call).
  `pruefe-aufloesung.py`: red before and after in the same way.
  `pruefe-deckung.py`, `pruefe-konstrukte.py`, `pruefe-reichweite.py`,
  `pruefe-gruende.py`: byte-identical output before and after.

## 6. What is owed

The full `abnahme.py` (server-scale runs: the mutation loop over all 409
anchors, the emission gate, the second corpus). Everything else ran green this
lane: `./cargo-pruef` (build + `cargo test --no-fail-fast`, 0 failing),
`./lean-bau` (222 jobs), `./lean-probe` on the grammar root, and every runnable
static guardian above, each re-run after the last edit.
