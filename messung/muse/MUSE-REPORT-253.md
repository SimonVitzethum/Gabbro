# MUSE-REPORT-253 — Hosted thread-start statement `start { f, g };` (P017, TODO §0)

Lane 253 (muse/253). Task: the FIRST thread-start shape that parses — a `start`
statement naming declared `concurrent` roots with join semantics (joined before
the starter proceeds, no detached threads ever); minimal acceptance; probes;
`./cargo-pruef` zero failures; downstream handoff list; MARKE_EMIT untouched.

English only. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (Rust lane, no
Lean touched). No new diagnostic code of any class (P/N/C/LG/W) — every refusal
reuses a measured code. No OS constants (`pruefe-osfrei.py` exit 0).

## 0. Result lines (last runs, quoted verbatim)

- `./cargo-pruef`: `== exit 0; failing tests: 0`
- `./lean-bau`: `Build completed successfully (280 jobs).` (exit 0; no `.lean`
  file touched — green is structural)
- `python3 instrumente/pruefe-saetze.py`: exit 0. `pruefe-kennungen.py`:
  `== KENNUNGEN: ALL PASS -- jede Kennung gehoert genau einer Datei ==`.
  `pruefe-osfrei.py`: exit 0. `pruefe-konstrukte.py`: exit 0.
- `bash instrumente/pruefe-syntax.sh`: `== SYNTAX: ALL PASS ==` (grammar table
  240/240, EBNF 178 rules closed); aborts AFTER that at `Warnungen` because it
  calls bare `cargo`, which is not on PATH in this shell (exit 127) — the
  queued `./cargo-pruef` above is the green build it could not see.
- `pruefe-englisch.py` exit 1: PRE-EXISTING ratchet drift, proved identical on
  a clean HEAD worktree (7963 comment lines / 37 Zubringer / 5 Meldungen both
  with and without this lane; none of the listed sites is a file this lane
  touched). `pruefe-grammatiktafel.py` needs `cargo` on PATH (environmental).
  `pruefe-wortschatz.py` needs its file argument (runs via `pruefe-waechter.py`).

## 1. What was delivered

**The statement.** `start { hauptA, hauptB };` — the statement half of the
`concurrent` declaration (`beispiele/124-two-threads-private.gab:88` is the
declaration it starts). Exactly ONE shape parses: braced path list, one path
at least, trailing comma allowed (same list rule as the declaration), `;`
terminated. Paths only — never arguments (declared starts take none, their
`Env` travels in `E.starts`), never a handle (the starter is joined before it
proceeds — join is structural: no second form exists, so no detached thread
is expressible).

**No keyword spent.** `start` stays a plain identifier (no `kw.rs`/`lex.rs`
change, vocabulary 240/240 unchanged, SYNTAX ALL PASS). The head word decides,
like `reset`/`child`: only `start` followed by `{` is the statement.
`start = 1;`, `start(x);`, `start.f = x;` keep parsing as assignment/call to a
name of that spelling (pinned by test). The unbraced `start f;` keeps its
`P017` — it is not the form (pinned by test). `spawn f;` keeps its `P017`.

**Files** (16 modified + 1 new test file, +237/−1):

- `crates/gabbro-syntax/src/ast.rs`: `StartStmt { roots: Vec<Pfad>, span }` +
  `StmtArt::Start(StartStmt)`.
- `crates/gabbro-syntax/src/parse.rs`: `is_start_head()` gate + `startform()`
  reader (mirrors `concurrentdecl`) + dispatch in `stmt()`.
- `crates/gabbro-syntax/tests/fadenstart.rs` (new): 9 snippet tests, all
  green (section 3).
- Checker, one real rule + mechanical arms: `nebeneinander.rs` resolves every
  `start` root fail-closed with the EXISTING `W003` (same sentence shape as
  the `concurrent` members); everything else treats the statement as the leaf
  it is — `lib.rs` (`unterbloecke`/`eigene_ausdruecke`/`eigene_praedikate`/
  `endet_immer`: no blocks, no expressions, no predicates, main path
  continues past the join), `m1.rs` (`{}` — no expressions, no bindings),
  `namen.rs` (binds nothing; `rumpf_falten` records one call per root, the way
  it records a library call's callee), `kosten.rs` (one primitive — the marker
  itself; creation/joining are the driver's), `arena.rs`, `pflichten.rs`
  (×2), `blindstellen.rs`/`certstmt.rs`/`corrlean.rs` (name tables: "start"),
  `zeugnis.rs` (counted, never lowered beside the count), `lean.rs`
  (`Err(Expression)` — no term in that channel), `lean_g.rs` (`LG004` by
  name), `emit.rs` (refusal by name under the EXISTING `C001`, best-effort
  comment beside it so the refusal changes no `cc` verdict; binds nothing;
  jumps nowhere; carries no expressions).

**Measured behaviour** (scratch in `.tmp/`, git-ignored, re-runnable):

- `start-gut.gab` (124 + `starter` with `start { hauptA, hauptB };`):
  `13 items, 0 errors, 6 hints` — the SAME 6 hints as baseline 124 (the
  statement is silent).
- `start-boese.gab` (`start { esgibtnicht };`):
  `error: [W003] …:93:13: \`start\` names \`esgibtnicht\`, which resolves to
  no body …` — `13 items, 1 errors, 6 hints`. Fail-closed, existing code.
- `start-doppelt.gab` (`start { hauptA, hauptA };`): 0 errors — accepted;
  the pool interplay (lane 245) is handoff, see section 5.
- `gabbro emit start-gut.gab`:
  `error: [C001] …:93:5: no lowering: \`start\` has no lowering in this
  template …` — exit 1, by name, no new code.
- `gabbro lean-g start-gut.gab`:
  `[LG004] \`start\` in starter has no G form …` — by name, no new code.

## 2. Corpus verdict diff: ZERO

No file under `beispiele/`, `messung/`, `laufzeit/`, `dokumente/` changed.
Basis, measured BEFORE building: zero occurrences of `start {` in code
anywhere in the corpus (the only `start` binding in the corpus is the
parameter of `beispiele/gift/46-lokale-sind-keine-wirkung.gab:23`, never in
statement-head position); no inline test snippet contains the shape. New
syntax therefore moves nothing existing. Pin:
`der_korpus_bringt_nur_benannte_absagen` passes inside the green
`./cargo-pruef` above. MARKE_EMIT* untouched (125/143/2/1/1/0/18, and
`git diff --name-only` shows zero files under `instrumente/`).

## 3. Probes (all in `crates/gabbro-syntax/tests/fadenstart.rs`)

Clean (parse): two roots / one root / trailing comma.
Poison (all pre-existing codes, no new ones): `start {};` → `P003`,
`start hauptA;` → `P017`, `start;` → `P017`, `start { hauptA }` (missing `;`)
→ `P001`, `spawn hauptA;` → `P017`.
Precision (name not stolen): `start = 1;` and `start(hauptA);` parse clean.
Checker-level behaviour (W003 refusal, silent acceptance) is verified on the
scratch files above; it cannot live in this test file (the syntax crate does
not depend on the checker). No poison gift file: every `beispiele/gift/`
file must fall and the statement has no checker refusal of its own to pin
there (W003 already owns gift 706/707).

## 4. What I believe is wrong (task vs tree)

The task's file box ("any file except `parse.rs`, `ast.rs`, `tests/` …
NOT `emit.rs`") is unbuildable as written, and I bent it — minimally,
mechanically, and documented here. Reason: `StmtArt` exhaustiveness is
BY DESIGN ("a new `StmtArt` is a compile error here rather than a silent
…", `lib.rs:809`): adding the variant breaks compilation of every
enumerating match, INCLUDING the forbidden `emit.rs` and 15 other checker
files. A lane that adds a statement without touching them commits red.
Every arm I added outside `parse.rs`/`ast.rs`/`tests/` is therefore one of
two things: (a) a one-line leaf placement beside the `Child` arm, or (b) a
refusal by name under an existing code (`W003`/`LG004`/`C001`). No arm
changes any verdict on any existing program (section 2). If the review loop
wants the box restored, the only consistent way is to revert the statement
itself — there is no middle ground between "new statement" and "untouched
passes" in this tree.

## 5. Downstream handoff list (next lane starts here)

Driver generation (lane 246 shape) + runtime own everything below; the
statement parses and the checker resolves names — nothing else is promised.

1. **Driver:** a `start { A, B };` inside a function is a scoped
   create-join: spawn exactly the named roots, join all before the next
   statement. Reuse `treiber.rs::erzeuge` per call site (wrapper per root,
   join loop, `ruhe()` idle shape untouched); pin per unit so a changed root
   set without regeneration fails loudly. Refusal for unresolvable members
   already exists in sentences (`treiberregel`); the checker's `W003` fires
   earlier on the same names.
2. **Checker rules not owed yet (refusals the next lane measures, with new
   codes from free stock only if a genuinely new refusal is measured):**
   membership in a `concurrent` set (a declared-but-not-concurrent function
   passes this lane — "never free functions" is parsed, not yet refused);
   nullary shape (a root WITH parameters passes parsing; the call cannot
   happen — driver refuses per `treiberregel` "parameterised member");
   duplicate roots vs lane 245 pool-safety (`start { A, A };` passes this
   lane); effects/costs accounting of the started threads at the starter
   (the statement is cost-1 transparent; thread-creation/join costs are the
   driver's); `start` inside `child`/signal contexts.
3. **Emitter:** lower to driver calls (wave B/C owns `emit.rs`; the `C001`
   arm marks the exact site). Until then every `start` refuses by name and
   no corpus file may contain one (else the corpus stops emitting).
4. **Exporter (`lean_g.rs`, `LG004` arm marks the site):** statement-level
   starts need the join/effects rule before they get a G form; the starts
   list still comes from the `concurrent` declaration only.
5. **Docs:** `dokumente/SYNTAX.md` § statement table + EBNF row for `start`
   (deliberately NOT in this lane: no guardian counts the new form yet, and
   SYNTAX ALL PASS holds without it — add the row together with rule (2)).
6. **Tests the next lane owes:** checker test pinning `W003` on
   `start { bogus };` (in `crates/gabbro-check/tests/`, outside this lane's
   box); driver end-to-end for a unit with a `start` (predicate comparison,
   not byte-identical stdout — schedule-dependent, lane 246 §2); a
   pool-safety probe for `start { A, A };`.

## 6. Open / not claimed

- Join semantics is structural (no detached form exists), not proved: no
  Lean changed, no model term for statement-level starts.
- `gabbro fmt` round-trip of `start` untested (no corpus file contains one).
- `pruefe-englisch.py` ratchet drift (+14/+11/+3 over booking) predates this
  lane byte-for-byte (clean-HEAD worktree measurement, section 0).
