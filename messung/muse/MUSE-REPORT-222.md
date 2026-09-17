# MUSE-REPORT-222 — Syntax: integer match arms + traverse subrange domain

Lane 222 (TODO §-1, wave A). Scope: `parse.rs`, `lex.rs`, `kw.rs`, `ast.rs`.
No new keywords, no new tokens, no new Lean, no checker/emitter/doc changes.

## 1. What was built

**Integer match arms (full delivery).** `match` over an integer scrutinee
with exact and range arms: `3 =>`, `-1 =>`, `0xFF =>`, `0 .. 255 =>`,
`0 ..< 256 =>`. Bounds are integer literals only (decimal/hex/binary,
`_` separators folded by the lexer, optional leading `-`); a computed
bound belongs to `narrow` or a guard, not to dispatch. An arm opening
with a literal or `-` is an integer arm; a variant arm opens with a
name; the two never compete for one token. Mixed arms parse (the parser
cannot know the scrutinee type) and every mix is refused downstream by
an existing rule (matrix in §3, all measured with the shipped binary).

**Traverse subrange domain (recognition + named refusal).**
`traverse i over slots of T from <start> count <len> by …` (bm13: start
plus length). Both words are contextual vocabulary, so the word list
does not move; the decision is positional (after a complete domain only
`by` or `from` may stand), so no program that parsed before changes
meaning. The shape is validated precisely (full start/length
expressions, full tail) and then refused with the pre-existing code
**P001** plus a handoff note naming lanes 229/234. No `Traverse` is
built, so nothing downstream can meet a window it cannot see. Why
refusal, and why no new code: there is no AST home for the window that
keeps the checker compiling — a new `Domaene` variant breaks its
exhaustive matches (e.g. the emitter's `traverse` lowering ends in an
8-arm exhaustive match producing the refusal sentence), and a new
`Traverse` field breaks its literal constructions
(`emit.rs::zaehlstelle`). Carrying the window silently as a
whole-table walk (or hijacking `of`/`decreases`/`touches` for it) is
the one thing the reader must not do. Lanes 229 (checker) and 234
(lowering) lift the refusal; §6 gives them the exact AST design.

**Printer + round-trip.** New module `print.rs`: `int_pattern` /
`int_bound` render an integer arm pattern canonically (`0xFF` → `255`).
Round-trip tests print a pattern inside a fixed scaffold and re-parse to
an equal pattern; two spellings of one value print to one text.

**TIEFE_MAX measurement.** The parser now reports its true deepest
nesting (`parse_with_max_depth`, one assignment beside the refusal, no
verdict change). Measured over the corpus: deepest file nests **8** over
**117 files** — 32 = 4×8 exactly, so 32 stands, with zero margin left.
Note: `parse.rs` still documents the old census (max 7); the corpus grew
since. No bump (a bump is a constant plus fuzz evidence, never a
redesign), but the next depth growth needs it.

## 2. Exact new names

- `ast.rs`: `IntPat::{Exact, Range{lo,hi,exclusive}}`,
  `IntBound{negative,value,span}`, `MatchZweig.intpat: Option<IntPat>`
  (`None` on every variant arm; while `Some`, `variante` is a
  placeholder carrying the printed pattern, `binder` always `None`).
- `print.rs` (new): `int_pattern`, `int_bound`.
- `parse.rs`: `is_int_arm`, `int_bound`, `int_arm`, `window`,
  `parse_with_max_depth`, `Parser::max_depth`, window refusal under
  pre-existing `P001` (no new code, no sentence owed).
- Tests (`sprechprobe.rs`, all English names): `lane222_int_arms_parse`,
  `lane222_int_arm_poison_keeps_existing_codes`,
  `lane222_int_pattern_prints_and_round_trips`,
  `lane222_windowed_traverse_refused_by_name`,
  `lane222_window_malformed_keeps_existing_codes`,
  `lane222_depth_stands_fourfold_over_corpus`.
- Untouched as required: `crates/gabbro-check/`, `emit.rs`, all Lean
  files, `MARKE_EMIT*`, `lex.rs`, `kw.rs`, SYNTAX.md, no corpus/gift/
  example files.

## 3. Downstream refusal matrix (all measured, shipped binary)

| form | `gabbro pruefe` | `gabbro emit` / other |
|---|---|---|
| int scrutinee + int arms | 0 errors, bodies checked (M1 100%) | C001 ``match` over something other than an `option index into T` `` |
| tagged + int arm | 0 errors (D005 checks missing-only; pre-existing, typo arms behave the same — verified) | C001 exactness (``must name every variant exactly once`` — verified with a `Tippfehler` arm) |
| option + int arm | 0 errors | C001 ``needs exactly `Some` and `None` `` (code-read, same shape) |
| reason + int arm | **M123** invented-name (verified with a `GibtsGarNicht` arm) | — |
| int + variant arm | 0 errors | C001 same as first row (verified) |
| windowed traverse | **P001** + handoff note (parser; precise span over `from … count …`) | — (never reaches downstream) |
| `gabbro lean` on int match | prints `(.onReason g …)` (reason branch) | model: non-reason subject → `.stuck` (`programmlogik/Gabbro/Coverage.lean`, ``honest outcome, not a silent fall-through``); lane 228 owns the proper form |
| `gabbro lean-g` / `gegenbeispiel` on int match | — | **LG004** by name, no panic |
| obligations/zeremonie/zeugnis/costs/alias | all run clean | no panics anywhere |

Malformed new shapes keep existing codes: `-x =>` → P004, `0(k) =>`
→ P001, `0 .. =>` → P004, `from a` without `count` → P001
(`count` expected), window over non-`slots` domain → P001 as before.
`lean.rs` also counts an int match as `match (tagged)` in `zeugnis`
(measurement label only, verdict-neutral; one-line wave-B follow-up).

## 4. Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, includes
  the corpus verdict tests `korpus.rs`/`beispiele.rs` — corpus verdict
  diff ZERO: no new syntax fires on any corpus file; window/int arms
  are absent from the corpus).
- `pruefe-wortschatz.py dokumente/SYNTAX.md`: 240/240 green (no new words).
- `pruefe-englisch.py`: my additions contribute zero German (verified by
  file grep); its broken ratchets (comment lines 7961 vs 7949 booked,
  sinks 5 vs 2) are pre-existing in files I did not touch.
- `pruefe-saetze.py`: **exit 0** —
  `55 ohne Satz` at booked mark 55 (no new code issued: the window
  refusal reuses P001, which owns its sentences).
- `pruefe-kennungen.py`: **ALL PASS** (trust surface ALL PASS).
- `emission-pruef` not run: no emitter/doc/counter changes exist to
  move it; corpus emission is covered by `beispiele.rs` in cargo-pruef.

## 5. What remains open (wave B/C)

- 228: exhaustiveness over integer arms + Lean match semantics (replace
  the `onReason` shape); 227: `switch` lowering; 229: window checker
  (effects + S001 early exit); 234: window lowering (evaluate start/len
  once into temps, `for (i = start; i < start+len; …)`).
- Wave-B AST design for the window (recommended): `Domaene::Window{ort,
  start, len}` (or a `Traverse` field) plus fixing every exhaustive
  `Domaene` match and the `Traverse` literal in `emit.rs::zaehlstelle`
  — all checker files, hence wave-B scope, not this lane's.
- The `parse.rs` TIEFE_MAX ledger line is fixed to the measured 8 in
  this round (was 7); SYNTAX.md has no window/int-arm section (doc
  lane's business; EBNF untouched so `pruefe-syntax.sh` closure is
  unaffected).

## 7. Requests to the dispatcher (round 3 — F1 resolved unilaterally)

- **F1 resolved without any checker touch** (review round 3, option
  F1(b)): the window refusal reuses pre-existing P001 plus a handoff
  note, so no sentence is owed and `pruefe-saetze.py` stays green. The
  earlier P045 sentence-exception request is withdrawn. No
  checker/Lean/emitter file is touched on this branch.
- **F2 ruling still requested**: (a) accept the P001+handoff refusal as
  the wave-A handoff with lanes 229/234 lifting it (my recommendation
  — the code is already that), or (b) grant a scoped wave-B exception
  (AST window home per §5 + sentence) for me to implement. Do NOT want
  silent acceptance.
- This branch currently touches **no** checker/Lean/emitter file; the
  F2 ruling is the only scope question left on the table.

## 6. Where this lane deviates from the task letter, and why

- Deliverable 2 asks for a checker-or-C001 code per form. For integer
  arms it holds (C001 + M123/LG004, §3). For the windowed traverse no
  checker/C001 code can fire correctly without checker changes (proven
  above: no green-build AST home), so the probe shows a parser refusal
  instead — a defined starting point with the handoff in the note,
  rather than a silence or a misleading code.
- "Parse + AST + print/parse round-trip for both forms": the AST and
  round-trip cover the integer patterns (both sub-forms: exact and
  range); the window has a fixed shape but no AST node yet (§1, §5).
- TODO §-1 table reserves examples 147–148 for lane 222, but the task
  text says snippet tests, not corpus files — followed the task text;
  no example numbers consumed (pool untouched for downstream).
- No new diagnostic codes at all: the well-formed window is refused
  with pre-existing P001 plus a handoff note (review round 3, option
  F1(b)) — no sentence owed, no new code, no gift files. An earlier
  revision of this branch issued P045 for the same shape; it was
  replaced precisely because a new code owes a sentence in
  `saetze.rs`, which is outside this lane's scope.
