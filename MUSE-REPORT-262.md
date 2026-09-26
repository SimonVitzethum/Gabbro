# MUSE-REPORT-262 — Close OFFEN O23 (gate argument preconditions)

Lane 262, branch `muse/262`. Task: O23's four rows — the NUL path as an
unchecked named obligation, `N464` covering `syscall` only, example 96's
`pure` gate over a syscall, gift 1067 borrowing the write assumption —
plus the Lean single-call bridge.

## What was done

### 1. The NUL path is checked where the program builds the buffer (`N507`)

**New module `crates/gabbro-check/src/nulpfad.rs`** (wired in `lib.rs`
behind `rahmenlaenge::pass`, same column, no pass number), new sentence
`gate.nulpfad` (in `M1`):

- At every call whose callee requires `path_nul_terminated(p, n)` (last
  path segment, two bare names, read through conjunctions like
  `rahmenlaenge::bounds`), three shapes answer:
  - **forwarding**: both actuals are the caller's own parameters under the
    caller's own identical clause (`beispiele/149`'s `oeffnen` stays clean);
  - **a proved buffer**: the pointer is a byte array built in this body
    (same-module `static` or `let` `[u8; M]`, direct spelling, readable
    length) with `buf[L-1] = 0` dominating the call for a constant length
    `L`, or an untouched zeroed buffer for any length;
  - everything else in these two shapes falls (`N507`): forwarding without
    the clause, a built-here buffer with no proof.
- A pointer the pass cannot see built (lone parameter, field, computed
  pointer, foreign static) keeps its named `V` obligation and **nothing
  falls beside it** — never silently dropped, per the task.
- Flow discipline: straight-line `buf[k] = 0` proves (constant `k`, `=`
  only); stores under branches/loops/error continuations never prove but
  still kill (except a maybe-`0`, which changes nothing either way); any
  call taking the buffer kills every cell; copies (`let ab = buf;`) track
  on. Representation is a full/empty flag plus an exception set — no cell
  is ever materialised, so large arrays cost nothing.
- Strings: no shape checked, and deliberately so — a `string max N` never
  reaches a `ptr<u8>` parameter (`N465`, no lowering under `C001`). Lane
  261's representation has no path into this rule.

**Names** (new definitions/theorems in Rust): `NulBuffer`
(`is_zero`, `all_zero`, `set_zero`, `set_unknown`, `kill`), `NulClause`,
`as_nul_clause`, `clauses_in_pred`, `nul_clauses`, `calls_in_expr`,
`is_byte_array`, `buffer_from`, `Walker` (`check_calls_in_expr`,
`check_calls_in_place`, `kill_for_expr`, `kill_for_call`,
`record_store`, `check_call`, `walk`), `pass`.

**Probes**: gifts `1253` (`N507`: filled buffer, the byte the gate reads
is no NUL), `1254` (`N507`: forwarding without the clause); ten twins in
`crates/gabbro-check/tests/nulpfad.rs` (unproved buffer, wrong index,
cleared proof, branch store, forwarding with/without the clause, proved
store, untouched zeroed buffer, copy, unseen pointer).

### 2. The frame-length rule covers `extern fn` buffers (`N506`)

`rahmenlaenge::pass` (new, wired behind `syscall::pass`): an `extern fn`
parameter pointing at numbers (`u8`/`i8` pointee) **beside a length
parameter** carries `requires x <= lenof(p)` or falls (`N506`) —
`N464`'s twin at the other foreign shape. The call-site half (`N463`)
already held for every callee, proven by a new twin
(`n506_extern_ruf_ueber_dem_feld_faellt_n463`). A lone object pointer
with no length beside it (`beispiele/22`'s `melde_roh`) is one object,
not a transfer, and stays silent. Sentence `syscall.rahmenlaenge`
widened to `N463`/`N464`/`N506`.

**Corpus measurement (task 2's tightening rule)**: exactly **one**
accepted program fell — `beispiele/64`, whose `write` now carries
`n <= lenof(p)` beside its ceiling (its call decides clean under
`N463`). Nothing else falls; `cargo-pruef` green is the measurement.
Probes: gifts `1251` (no clause), `1252` (word buffer); six twins in
`tests/rahmenlaenge.rs` (incl. the length-less exemption).
`tests/gestalt.rs`'s decay pin now draws `N506` at the declaration (the
decay itself stays silent) — the pinned silence moved because the rule
is new, not because the decay changed.

### 3. Example 96: fixed, not refused

The write gate said `effects { pure }` while the kernel reads `len`
bytes from `buf`. **Fixed**: the gate says `effects { reads buf }` (the
read gate of `beispiele/150` says `writes buf`), and
`push`/`flush`/`fill`/`writer_demo` plus the flush loop carry
`reads WINDOW` (`E008` held each level until it did). A rule against
pure-with-buffer was considered and rejected: it would also hit
`beispiele/74`'s fiction and widen the corpus diff for no new
knowledge. The file checks clean (0 errors).

### 4. Gifts 1067/1068 name the read assumption

Both gates take a descriptor and a count but borrowed
`linux_write_contract`. Both now name `beispiele/150`'s pair
(`linux_read_contract`/`sonde_read`, `N024` neutral). **No new
assumption name was minted**: a row without a program would break
sondendeckung's `MARK_QUOTE` ratchet (21/54), and a program-grade probe
for two refusal scaffolds is F5-scale work for no new knowledge. Both
still fall with exactly their code (D004, D003 — measured).

### 5. Lean: the bridge lifted to call sequences (§10 of `FremdRuf.lean`)

- `rufFolgeWirkt` (fold an oracle over a gate-call list threading
  worlds), `RufFolgePflicht` (the caller's obligation at every call),
  `mitVorbedingung_folge_gleich` (both folds agree under the obligation;
  induction with `mitVorbedingung_gleich` at the head),
  `fdFolge`, `fdFolge_offen_pflicht`, `fdFolge_lesen_pflicht`,
  `mitVorbedingung_folge_gleich_zeuge` (joint premises on `fdObad`).
- Deliberately **not** a program run: no `Stmt`/`execStmt`/`bindAxiom`,
  nothing called a semantics (hard rule 4c). The machine-level run
  coincidence still needs the F-machine residue shape — in CUTS.
- Fixture widening toward example 150 judged **not cheap** (a `buf`/`len`
  gate needs a third `Ax` value — today `Ax := Bool` — changing every
  environment and fit; opacity is unmodelled per G10) and recorded in
  CUTS. `Spec.lean` untouched.
- `lean-bau`: **319 jobs, build completed successfully** (last result
  line). New theorems depend on `propext` only.

## Verification

- `./cargo-pruef`: **1352 passed, 0 failed, 1 ignored** (exit 0).
- `./emission-pruef`: **ALL PASS — 40 run, 291 of 291 compile**
  (`.tmp/emission.log`). `MARKE_EMIT*` untouched: no new emitting file
  (four refused gifts), 96 still emits. **Delta 0.**
- `./lean-bau`: 319 jobs green (above).
- Text guardians: `pruefe-saetze` exit 0 (448 codes, 187 sentences, 0
  invented); `pruefe-kennungen` exit 0; `pruefe-englisch` exit 1 on the
  three pre-existing reds only (7965/37/5, same numbers as FIX-F5 —
  plus one burst seam of mine, fixed: a merged line in `lib.rs`);
  `pruefe-zahlen` exit 1 with 37 findings, `pruefe-todo` exit 1 with 16
  — same counts as FIX-F5, none naming this lane's artifacts;
  `pruefe-sondendeckung` rc 2 at its speech test, as on the base.
- New `src/` identifiers are English (hard rule 7); test names follow
  the German convention of their files (tests are outside the
  identifier scan).
- Corpus verdict diff: **0** besides the reported tightening (64) —
  `beispiele` + `gift` suites green, `zertifikate` green (no register
  rewrite needed).

## What remains open (O23 narrowed, closed on none)

Recorded in `OFFEN.md` O23's status paragraph: the NUL for unseen
pointers (still `V`-only); the run coincidence above the oracle layer
(`bindAxiom`, `AxPre` export); `lenof` of a pointer decided only where
an array decays.

## Where I believe the task is wrong, or had to choose

- **"or a string from lane 261's representation"**: no such shape
  exists — strings cannot flow into `ptr<u8>` parameters (`N465`).
  Reported as not applicable, not built.
- **96 "fix or refuse"**: fixed. A refusal rule would punish the honest
  shape (150's `writes buf` is equally "impure") and drag in 74.
- **1067/1068 "their own assumptions"**: read as the read family's own
  (vs the borrowed write one), not two brand-new names — new names
  without programs break a guardian ratchet by construction.
- **Fixture widening "if cheap"**: it is not cheap; proved the
  sequence lift instead and said so in CUTS.
- **Reserved codes used**: `N506`, `N507`; gifts `1251`–`1254`.
  `N508`–`N510` and gifts `1255`–`1260` untouched. `MARKE_EMIT`
  untouched. `child`/`start` lowering and strings internals untouched.
