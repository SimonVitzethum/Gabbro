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
expressions, full tail) and then refused with the new code **P045**,
naming the wave-B handoff. No `Traverse` is built, so nothing downstream
can meet a window it cannot see. Why refusal and not AST: there is no
AST home for the window that keeps the checker compiling — a new
`Domaene` variant breaks its exhaustive matches (e.g. the emitter's
`traverse` lowering ends in an 8-arm exhaustive match producing the
refusal sentence), and a new `Traverse` field breaks its literal
constructions (`emit.rs::zaehlstelle`). Carrying the window silently as
a whole-table walk (or hijacking `of`/`decreases`/`touches` for it) is
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
  `parse_with_max_depth`, `Parser::max_depth`, refusal `P045`.
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
| windowed traverse | **P045** (parser; precise span over `from … count …`) | — (never reaches downstream) |
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
  diff ZERO: no new syntax fires on any corpus file; P045/int arms are
  absent from the corpus).
- `pruefe-wortschatz.py dokumente/SYNTAX.md`: 240/240 green (no new words).
- `pruefe-englisch.py`: my additions contribute zero German (verified by
  file grep); its broken ratchets (comment lines 7961 vs 7949 booked,
  sinks 5 vs 2) are pre-existing in files I did not touch.
- `pruefe-saetze.py`: **exit 1** —
  `FUND: 56 Kennungen ohne Satz, gebucht sind 55` — the delta is exactly
  P045, which has no `Satz` yet. Fixing it means one entry in
  `crates/gabbro-check/src/saetze.rs`, which is outside this lane's
  scope: **scoped exception requested from the dispatcher** (see §7;
  entry drafted and ready to apply on grant, P043/P044 pattern).
- `pruefe-kennungen.py`: ALL PASS (P045 belongs to exactly one file,
  `parse.rs`; trust surface ALL PASS).
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

## 7. Requests to the dispatcher (round 2 — nothing below is applied)

- **F1 scoped exception**: one `Satz` entry for P045 in
  `crates/gabbro-check/src/saetze.rs`, P043/P044 pattern
  (`parser.bibliothek-nutzlast`/`parser.bibliothek-rumpf`), placed
  directly after the P044 entry. Draft ready to apply on grant:
  name `parser.traverse-window`, `kennungen: &["P045"]`,
  `aussage`: windowed `traverse` is read precisely and refused at the
  reader so no pass meets a window it cannot see;
  `vorbehalt`: shape rule of the parser only, typing/lowering belong
  to lanes 229/234 which lift the refusal;
  `stand: Satzstand::Gemessen`,
  `gemessen_an`: snippet tests
  `lane222_windowed_traverse_refused_by_name` +
  `lane222_window_malformed_keeps_existing_codes` (no gift numbers
  consumed per the task text),
  `fundstelle`: `parse.rs` (`traverse`, `window`).
  Precedent: the P042 entry arrived with its code in the same commit
  (quoted in `pruefe-saetze.py` itself); the mark stays 55.
- **F2 ruling**: (a) accept P045 as the wave-A handoff with lanes
  229/234 lifting it (my recommendation, and the reviewer's — the code
  is already that), or (b) grant a scoped wave-B exception (AST
  window home + sentence) for me to implement. Either way the F1
  sentence stays in scope. Do NOT want silent acceptance.
- This branch currently touches **no** checker/Lean/emitter file; the
  two requests above are the only scope changes on the table.

## 6. Where this lane deviates from the task letter, and why

- Deliverable 2 asks for a checker-or-C001 code per form. For integer
  arms it holds (C001 + M123/LG004, §3). For the windowed traverse no
  checker/C001 code can fire correctly without checker changes (proven
  above: no green-build AST home), so the probe shows **P045** instead
  — a defined starting point with the handoff in the sentence, rather
  than a silence or a misleading code.
- "Parse + AST + print/parse round-trip for both forms": the AST and
  round-trip cover the integer patterns (both sub-forms: exact and
  range); the window has a fixed shape but no AST node yet (§1, §5).
- TODO §-1 table reserves examples 147–148 for lane 222, but the task
  text says snippet tests, not corpus files — followed the task text;
  no example numbers consumed (pool untouched for downstream).
- No diagnostic codes were planned, but the well-formed window is a
  measured new refusal need (must not parse silently, cannot reach
  downstream): took next free P per the maintainer rule — **P045**
  (P031/P032/P042 retired or allowlisted-only; P043/P044 taken) — with
  sentence plus snippet probes, no corpus/gift files.
