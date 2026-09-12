# MUSE-REPORT-64: library call syntax `@<library>#<function>` (lane E1)

Branch `muse/64`. Rust lane (parser) + `SYNTAX.md`. No Lean changes
(`grammatik/` untouched); rule 13 (inhabitation) is vacuous — no theorems
added. Last `./lean-bau` result line:
`Build completed successfully (36 jobs).` (0 error lines).

## What was built

`@<library>#<function> ( args ) { region }` in statement and binding
position, per `PLAN-ERWEITUNG.md` §6 lane E1. The region is captured as a
brace-balanced token tree WITHOUT interpreting it; semantics per §0b
(run-time call, region compiled at translation time into a payload) is
documented as **not implemented yet**. Lane E2 does not exist in this tree
(only unrelated "payload" words), so the checker refuses every library call
with the controlled diagnostic — never a crash, never a silent acceptance.

Exact new names:

- `lex.rs`: `Z::Hash` (`"#"`) beside `Z::At`; punctuation, deliberately no
  `Kw` entry — the closed vocabulary (224 words) does not move. Measured:
  no bare `#` stands in any `.gab` of the tree or any ```gabbro block of
  the documents (every hit is inside a `--` comment or a string), so no
  existing program re-lexes.
- `ast.rs`: `LibraryCall { library, function, args, region, span }`,
  `RawToken { text, span }`, `StmtArt::LibraryCall`, `ExprArt::LibraryCall`
  — one struct for both positions so no pass reads one and misses the other.
  (English names: the guardian's German-stem ratchet, `NAMENSMARKER`, flags
  `Ruf`; `LibraryCall`/`RawToken`/`Hash` match nothing.)
- `parse.rs::library_call()`: names, plain positional args, brace-balanced
  region. Malformed shapes fall with ordinary codes, never silently:
  missing `#`/`)`/`}` or unbalanced region → `P001`, empty library name →
  `P003`, labelled argument → `P036`. Wired into `stmt()` (`@` branch,
  `;` required like `exprstmt`) and `letform()` (`=` branch); elsewhere
  `@` still falls with `P011`. `let … else` over a library call falls with
  the existing `P016`.
- Shared walkers (`lib.rs`): `unterbloecke` (leaf), `eigene_ausdruecke`
  (statement args), `eigene_praedikate` (leaf), `endet_immer` (returns,
  `false`), `unterausdruecke`/`alle_orte` (args, not a place). Every pass
  that walks these sees the arguments; the region is raw tokens and stays
  out everywhere.
- `namen.rs`: `library_call_not_checked` issues `N057`
  ("library calls are parsed but not yet checked", naming
  `@library#function`, argument and region-token counts) once per call in
  both positions; `lane_e2_checks_calls` (answers `false`) is the hook
  where lane E2 retires the rule.
- Honest arms everywhere the compiler demanded (`cargo check` enumerated
  14 sites): M1 types arguments (`Unbekannt`) and kills facts at calls in
  them; costs counts arguments plus `Unbekannt` with reason (never zero);
  effects reads argument places; emitter refuses by name (`C001`, belt and
  braces behind the checker); Lean channel maps to the existing
  `CallStatement` refusal (no new `LeanReason`, so `pruefe-deckung.py`
  stays green); certificate counts `library call` with an `EINORDNUNG`
  entry (`Traegt::Fremd`, stating the refusal); blind-spot table names the
  form; `domaene`, `pflichten`, `refinement` descend or refuse by name.
- `SYNTAX.md`: `libcall`/`libregion` productions wired into `stmt`
  (`libcall ";"`) and `letstmt` (`"=" libcall ";"`), plus a
  `### Library calls` subsection with semantics and the not-implemented
  statement. Measured: 163 EBNF rules defined, 0 open, 0 unreachable from
  `program`; vocabulary still 221/221 both readings — `@`/`#` are
  punctuation, invisible to the vocabulary guardian by its own terminal
  pattern, so no guardian pattern needed changing (verified, not assumed).
- Probes: `beispiele/gift/802` (unbalanced region → `P001`),
  `/803` (missing `#` → `P001`), `/804` (empty library name → `P003`),
  `/805` (`N057` in both positions, plus honest `K003` for the unknown
  cost); seven `library_call_*` tests in `paesse.rs`; one AST-shape test
  in `sprechprobe.rs` (`library_call_reads_names_args_and_region`: names,
  one arg, region `["dispatch","{","nested","}","0"]`); `N057` in
  `BENANNT`; new Satz `namen.library_call` in `saetze.rs`.
- Registers recomputed with dated entries: PASSREGISTER.md (118 sentences,
  110 measured, 6 conjectured, 304 codes, 249 claimed), TODO gruende line
  (139 tragend — `N057` states its obligation — 7 verdächtig, 107 unklar),
  TODO Absagekennungen (304), TODO Sätze line (118).

`./cargo-pruef`: exit 0, zero failing tests (final run after all edits).

## What remains open

E2 (checked call), E5 (translation stage), and everything after E1 by
design. Deliberate E1 decisions a later lane should know: positional args
only (`P036` on labels); the blind-spot table axis NOT extended — a form
refused in every program has no closable cells, and its measurement is the
`N057` probes, not blind cells; `lane_e2_checks_calls` is a named `false`
until E2 declares library functions.

## What I believe is wrong (in the task or around it)

1. Pre-existing reds, all verified at `ce312f0` (clean worktree) or proven
   by diff to predate this lane — none is mine, my delta on each is zero:
   `pruefe-vergabe.py` (21 candidates / 75 affected vs booked 20/68),
   `pruefe-saetze.py` without-sentence count (55 vs 53; `M152`+`V012` landed
   sentenceless), `pruefe-englisch.py` (comment/Zubringer/sink/message
   marks — my 134 comment lines are all English, my 6 identifiers match no
   stem), `pruefe-zahlen.py` (13 BEFUNDs, all drift or broken search paths;
   my three entries — Sätze, Absagekennungen, tragend/unklar — now green),
   `zaehle-gifttreffer.py` (19 verdeckt vs 8; none is 802–805, mine are
   sauber/begleitet), `emission-pruef` (beispiel19 stage-8 speech test:
   the gift sed `s/; i++)/; i += 2)/` predates the emitter's `{v} += 1`
   template — both identical at `ce312f0` and HEAD).
2. `pruefe-vergabe.py` episode (mine, healed): two noted `P001` sites
   pushed `P001` under the similarity bound (new candidate). The refusals
   are bare now; the `P036` note shares the existing note skeleton
   (similarity 0.71 vs bound 0.45). Lesson: new sites under old codes must
   reuse the old text shape.
3. `pruefe-zahlen.py` needs `cargo` on `PATH` (it crashed with
   `FileNotFoundError` otherwise); `pruefe-syntax.sh` likewise (exit 127).
   Both pass with `PATH` set (`SYNTAX: ALL PASS`, null warnings).
4. The `Sätze über (\d+) Codes` gauge matches inside strikethrough: a
   `~~old~~ new` figure keeps matching the old number — history there must
   be dropped, not struck (done at TODO:4241).
5. `blindstellen` counts 79 blind of 285, byte-identical before/after:
   it skips refused files, so the always-refused form contributes no
   cells. If a later lane wants the form in the axis, every cell needs a
   `keine_zelle` entry (`N057` in every position) or the blind count
   grows by unclosable cells.

## Merge with master (reviewer-started, resolved by this lane)

Two conflicts, both resolved without touching the other side:

1. `crates/gabbro-syntax/tests/sprechprobe.rs`: kept both tests complete,
   one after the other — `library_call_reads_names_args_and_region`
   (lane E1) then `syscall_faellt_mit_einem_namen` (lane S1, `P042`).
   Both pass (`--test sprechprobe`: 21 passed, 0 failed).
2. `dokumente/SYNTAX.md` EBNF-rules row: both sides had written 163 with
   different additions. Re-measured via `pruefe-syntax.sh`: **167**
   defined, 0 open (master added `syscalldecl`, `errmap`, `nonzero`,
   `uint`; lane E1 added `libcall`, `libregion`) — the reviewer's guess
   of 165 was short by two, the measured number stands.
3. Poison probes renumbered: master took gift 796–801, so mine moved
   796→802, 797→803, 798→804, 799→805 (`git mv`); references updated in
   `saetze.rs` (`namen.library_call` entry), the gift module names, and
   this report. `./cargo-pruef` green (exit 0, 0 failing),
   `pruefe-wortschatz.py` green (226/226 both readings).

Co-Authored-By: muse-agent-64 <muse-agent-64@noreply.invalid>
