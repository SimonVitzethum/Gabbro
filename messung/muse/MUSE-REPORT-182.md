# MUSE-REPORT-182: Source trust — homoglyphs and bidi (lane 182)

Lane 182. Gabbro's promise is that a HUMAN reads a body and proves its logic
("written by hand and read by a person"); a program that reads differently to a
human than to the parser breaks exactly that premise: a Cyrillic `а` in an
identifier, a bidi control character that reorders a line (Trojan Source,
CVE-2021-42574). The tree had zero hits for homoglyph/bidi/confusable. It now
refuses all four classes, on both implementations, with a guardian watching the
tree itself.

## 1. Measurement: what the corpus actually holds

Measured 2026-09-14 over **992 `.gab` files** (every `.gab` in the tree outside
`.git`/`target`), identifiers split from strings and comments the way the lexer
splits them (`"..."` strings, `--` comments):

| Position | Distinct | Non-ASCII |
|---|---|---|
| Identifiers in code | 3807 | 0 |
| Strings | — | `« » — „ …` only (quotation/dash typography) |
| Comments | — | table below |

Non-ASCII in comments (all prose, none executable): `§ « ¬ · » Ö × Ü ß ä ö ü`
(German text), `σ → ∅ ∧ ∩ ⊕ ⟨ ⟩` (math prose), `– — ‚ " „ …` (typography), plus
one `䀀` (U+4000, the pre-existing gift probe 163) and one `U+202E` (the new
probe 960, inside its own comment — that is the probe working).

Bidi set (U+202A–202E, U+2066–2069, U+200E/200F, U+061C) and invisible set
(U+200B–200D, U+FEFF): **zero** in all `.gab`, and zero in all 127 `.rs` and
308 `.lean` files (which legitimately carry Greek and math symbols in comments).

Every `gabbro` block of `FRAGMENTE.md`, `SYNTAX.md`, `SPRACHE.md`, `README.md`,
`MEMO-GLEITKOMMA.md` and `TUTORIAL.md` was measured the same way: clean.

**Decision on the allowed set:** it stays exactly what `SYNTAX.md:145` already
says — ASCII letters, digits, `_`, plus `ä ö ü ß Ä Ö Ü`. The corpus uses no
non-ASCII identifier in code position at all, so ASCII-only would also pass;
dropping the documented umlauts would narrow the grammar for no measured
reason. No grammar change, no `SYNTAX.md` change.

## 2. The Rust gate (`crates/gabbro-syntax/src/lex.rs`)

`quelltext_pruefe` runs first in `zerlege` and only ADDS refusals:

- **P060** — bidi control/format character ANYWHERE (raw source, comments and
  strings included).
- **P061** — identifier-like run with a character outside the allowed set
  (one foreign script).
- **P062** — identifier-like run mixing two scripts (twelve-family UTS#39
  approximation in `schrift`; the run predicate `ist_laufzeichen` is shared
  character-for-character with Lean).
- **P063** — invisible character (U+200B–200D anywhere; U+FEFF anywhere except
  offset 0, which the main loop now also skips instead of `L006`-ing).

Runs skip strings/comments exactly as the main loop does; a run glued to a
digit (`0䀀`, gift 163) stays `L003`/`L006` territory and is not double-reported.
**P064 is booked with the lane and stays unissued** (spare; four classes, four
codes, four gifts — see §3).

## 3. Codes, probes, tests

Reserved codes used: **P060–P063** (P0xx was free above P044). Gift numbers
used: **960–963**, one poison file per class, no clean examples:

- `beispiele/gift/960-bidi-override.gab` → P060 (override inside a comment)
- `beispiele/gift/961-cyrillic-name.gab` → P061 (whole name Cyrillic)
- `beispiele/gift/962-mixed-script-name.gab` → P062 (Latin `p` + U+0430)
- `beispiele/gift/963-zero-width-space.gab` → P063 (U+200B in code)

Each probe carries exactly its code and nothing else (verified). Inline tests
in `crates/gabbro-syntax/tests/sprechprobe.rs` pin the same four over
`\u{...}` escapes — no literal poison in the `.rs` source — plus the
counter-directions: umlaut identifiers pass, foreign prose in comments passes,
`0䀀` stays `L006`-only, a leading BOM passes. One sentence covers all four in
the pass register (`quelle.zeichenvertrauen` in `saetze.rs`), so the
`pruefe-saetze.py` ratchet stands still at 55 by construction (+4 issued, +4
claimed).

## 4. The guardian (`instrumente/pruefe-kennungen.py`)

`quellvertrauen()` scans every `.gab` (except `beispiele/gift/`, poison on
purpose — the same exclusion `korpus.py` makes), every `.lean` and every `.rs`
minus build/worktree dirs, with the lexer's four classes (identifier runs on
`.gab` code only; bidi/invisible everywhere on all three — `.rs`/`.lean`
legitimately carry Greek/math in comments). Speech probe in both directions
runs every time; empty population aborts (W17). Today: 760 files, ALL PASS.

## 5. The Lean gate (new file, `Lexer.lean` untouched)

`grammatik/Grammatik/Parser/LexerVertrauen.lean` (new) + one import line in
`Grammatik.lean`. `lexVertrauen` refuses first, lexes second; eleven
`decide` theorems pin the four refusals, the four counter-directions, the
codes, and one clean end-to-end lexing. Agreement was fuzzed, not asserted:
40000 adversarial inputs over both implementations — same first code outside
two named corners ((a) exotic letters past the twelve families, (b)
family-range non-ASCII digits), and **zero acceptance holes** (1768
gate-level divergences, all in (a)/(b); every such input still refuses on both
sides, at worst under `L006`/`.unbekannt`). The fuzz caught two real bugs
before they shipped: a leading BOM opening a Lean run, and over-wide Lean run
starts — both fixed, both documented in CUTS.

## 6. What ran

- `./lean-probe` on `LexerVertrauen.lean`: first run 9 errors (termination
  failures in `codeZeichen`/`pruefeLaeufe`, hence `sorryAx`, hence every
  `decide` stuck). Fixed with fuel like `scan`; re-probe: exit 0, 0 errors,
  `#print axioms` standard only.
- `./lean-bau`: exit 0, `Build completed successfully` (207 jobs), new module
  built.
- `./cargo-pruef`: exit 0, 0 failing tests (full suite incl. the new
  `sprechprobe.rs` cases and gifts 960–963 through the gift harness).
- `pruefe-saetze.py`: RC 0, 55 of 395 without sentence — the ratchet stands
  (+4 issued, +4 claimed, 0 invented).
- `pruefe-kennungen.py` RC 0 (395 codes, 760 files), `pruefe-vergabe.py`
  RC 0 (marks 32/88 held).
- `pruefe-englisch.py` stands at 28/26 (red) — measured identical on the base
  tree without this lane's changes (`git stash` probe): a pre-existing broken
  Zubringer ratchet, and none of its findings point at the new refusal texts.
- `pruefe-emission.sh` not run: the emitter is untouched (lexer-failing gifts
  never emit), and `MARKE_EMIT` is not touched. The Rust/Lean agreement sims
  above are Python-faithful cross-checks, not compiler runs.

## Files

- `crates/gabbro-syntax/src/lex.rs` — gate (`P060`–`P063`, BOM skip)
- `crates/gabbro-syntax/tests/sprechprobe.rs` — four test functions
- `crates/gabbro-check/src/saetze.rs` — `quelle.zeichenvertrauen`
- `beispiele/gift/960-bidi-override.gab`, `961-cyrillic-name.gab`, `962-mixed-script-name.gab`, `963-zero-width-space.gab`
- `instrumente/pruefe-kennungen.py` — `quellvertrauen` guardian
- `grammatik/Grammatik/Parser/LexerVertrauen.lean` — new; `grammatik/Grammatik.lean` — one import line
