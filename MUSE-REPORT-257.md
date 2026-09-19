# MUSE-REPORT-257 — max/grow syntax for dynamic arenas (TODO §-1 wave D, unblocks the emitter arm)

Lane 257, 2026-09-19. Scope as tasked: `max M` ceiling clause on arena
declarations + `grow` statement with boolean discipline, parsed into AST
that says what they mean; the checker accepts exactly what 240's rule
already decides and refuses the rest by name; snippet tests; no corpus
files; `emit.rs` untouched except the named refusal; no Lean files touched
(read-only); `MARKE_EMIT*` untouched.

## Verdict in one line

**BUILT — the parser gap lanes 240, 242, 243 and 248 recorded is closed
for the exact clause syntax the lowering needs.** `arena … max M` and
`grow A by n else B` parse into `ArenaDecl::max` and `StmtArt::Grow`,
the checker holds the ceiling (`N210`), the commit (`N426`, one new code
from the returned 240 reserve) and the name (`N213`), every other pass
sees the form (costs, effects, phases, certificates) or refuses it by
name (emitter, G exporter). `./cargo-pruef` zero failures,
`./emission-pruef` exit 0, `./lean-bau` exit 0, corpus verdict diff zero,
`MARKE_EMIT` delta +0.

## 1. What was built

**Syntax (`crates/gabbro-syntax`, mine alone per task).**

- `kw.rs`: `Grow => "grow", ctx` with the reason block (one new word;
  `max` and `by` already exist as `ctx`). `grow = 1;` stays an assignment
  through the existing `wort_ist_anweisungskopf` guard; `grow(x);` stays
  unwritable, the documented one-form residue shared with `reset`.
- `ast.rs`: `ArenaDecl::max: Option<Expr>` (`None` = the static form,
  ceiling `hi` by construction); new `StmtArt::Grow(GrowStmt)` with
  `GrowStmt { tisch: Ident, mehr: Expr, sonst: Block }`.
- `parse.rs`: `arena()` reads an optional `max M` between `hi` and `of`,
  so the static prefix `arena A capacity lo .. hi` reads byte for byte as
  before; the `Grow` arm reads `grow A by n else { … };` with a MANDATORY
  `else` (boolean discipline: the grammar has no branchless form, so a
  missing `else` is `P001` at the reader, never a checker question).
- `SYNTAX.md`: EBNF `arena` + new `growstmt` (179 rules, 0 open),
  `stmt` alternation, §9.1 prose + example, attribute-table rows,
  vocabulary `grow` (241 terminals both readings; 244 words, 17 reserved,
  227 contextual). `instrumente/zaehle-wortschatz.py`: ledger entry
  `243 -> 244` + `MARKE_WOERTER = 244` (guardian pattern before the
  document, per rule).

**Checker minimal (`crates/gabbro-check`).**

- `umgebung.rs`: `ArenaSig::max: Option<i128>` + both collection sites
  (`None` = no clause, or no constant — the pass tells them apart at the
  AST, where the clause presence stands).
- `arena.rs`: `Laeufer::decke` (ceiling per arena: the clause where usable,
  else `hi`) via `deckenwert()`; `N210` holds `hi <= max`, constantness
  and `u32::MAX`; `N213` for `grow` out of an undeclared arena; **new
  `N426`** for the two shapes no code says — a non-constant (or negative,
  or huge) `by` amount, and a commit the checker sees reaching past the
  ceiling, branch or no branch (past the ceiling there is no commit, only
  the stop; the runtime aborts it as a bypass). The `Grow` walk bumps the
  path's committed prefix, capped by `M`, and joins the `else` like
  `alloc`'s. `N212` is UNCHANGED (still held against `lo`; re-pointing at
  the committed value is the checker-rules lane's, stated inline).
- Costs: `Grow` = 1 + amount + `else` (the `Alloc`-shaped arm 242 named;
  rides `sperrbloecke` with zero new machinery). Effects: `grow` writes
  its arena, reads its amount (needs `writes A`). Phases: the `else` is an
  exit path like every other. `m1`/`m2`/`namen`/`domaene`/`clone`/
  `pflichten`/`zeugnis`/`fusswache2`/`lean`/`certstmt`/`corrlean`/
  `blindstellen` walk the amount and the `else` or bind nothing, each
  named inline. `lib.rs`: `unterbloecke` gains the `else`,
  `eigene_ausdruecke` the amount, `endet_immer` the fall-through shape.
- Fail-closed, by name: `emit.rs` refuses every `grow` (comment-only
  emission, no `cc` verdict move — the Start precedent, including the
  empty name set: a lowering and its name set are one change, the arm
  lane's); `lean_g.rs` refuses with `LG005` (the committed prefix is
  checker flow; the model builds the static `ArenaForm`), footprint walks
  the counter half like `reset`.

**Sentences + probes (same commit as the code).**

- `saetze.rs`: new `arena.wachsen_commit` (`kennungen: &["N426"]`).
- `beispiele/gift/1088-arena-grow-ueber-decke.gab` (`-- erwartet: N426`,
  past-ceiling commit WITH the branch; measured sauber).
- `paesse.rs`: `arena_grow_ueber_decke_n426` (poison + clean twin),
  `arena_grow_menge_unkonstant_n426` (parameter amount + `const` twin),
  `arena_grow_unbekannt_n213` (poison; the effect line names the same word
  so no second rule fires, the 888 precedent).
- `crates/gabbro-syntax/tests/arena_dynamisch.rs`: 6 parse snippets (ceiling
  in the tree, static form stays `None`, `grow` in the tree, missing `else`
  is `P001`, `grow`/`max` stay names elsewhere).

## 2. Arm-lane handoff (deliverable 2 — the exact input the lowering sees)

248's SPEC (§4 of MUSE-REPORT-242.md) applies verbatim, with these
bindings fixed by this lane (no second design needed):

- **Declaration shape.** `ArenaDecl { name, oeffentlich, lo, hi, max:
  Option<Expr>, element, span }`. Dynamic iff `max.is_some()` (then `hi <=
  M`, both constant, already held). Static arenas are untouched: same
  struct, `max: None`, same lowering as today.
  ```gabbro
  arena Log capacity 2 .. 8 max 64 of u16;
  ```
- **Statement shape.** `StmtArt::Grow(GrowStmt { tisch: Ident, mehr: Expr,
  sonst: Block })`. The amount is a translation-time constant (already
  held: non-constant never reaches the lowering). The `else` always
  stands. `committed + n <= M` already held; the lowering needs no second
  check, only the call.
  ```gabbro
  grow Log by 8 else {
      return 0;
  };
  ```
- **Lowering coordinates (unchanged from 242 §4).** `emit.rs` `fn arena`
  dynamic arm iff `max` present (descriptor `{0, sizeof, M, hi, 0, hi}` +
  two `_Static_assert`s, no `buf[M]` storage); `StmtArt::Grow` beside the
  `Alloc` arm as `if (gabbro_arena_grow(&Log_desc, n)) {} else { <else> }`;
  `ResetArena` unchanged. Checker-clean programs reaching the lowering
  need no re-validation of `n` or the ceiling — that is what `N426` buys.
- **Test obligations (the arm lane's).** Executed grow past the old `hi`
  with read-back (370/1004 shapes reusable); poison over-`max` extends
  gift 1088 (no new code); `-O0`/`-O2`/UBSan + stage-9 `-c`.
- **What the lowering must NOT redo.** The `N212`-vs-committed re-pointing
  and `R-max` belong to the checker-rules lane, not the arm lane; this
  lane changed neither.

## 3. Verification (last lines, this tree)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full build + test,
  incl. 6 new syntax tests, 3 new `paesse` tests, 7 `wachstumstests`
  incl. the new `deckenwert` faces).
- `./emission-pruef`: `== exit 0 (full log: .tmp/emission.log, 694
  lines)` (288/288 emit — the refused gift is not emitted, no new
  emitting root).
- `./lean-bau`: `== lake exit code: 0`, `0 error line(s)` (no Lean file
  touched; the run is the machine check behind that claim).
- Corpus verdict diff: ZERO — no existing file parses differently (every
  `grow`/`max` in the corpus is comment prose; no `.. max` bound stands
  anywhere; `cargo-pruef` green over the identical tree, gifts included).
- `MARKE_EMIT` delta: **+0** (script untouched; the merger bumps nothing).
- Guardians: `pruefe-wortschatz.py` 241/241 both readings;
  `zaehle-wortschatz.py` 244 words, marks 244/212/17 hold;
  `pruefe-saetze.py` 426 codes, 177 sentences, 0 invented;
  `pruefe-kennungen.py` ALL PASS; `pruefe-grammatiktafel.py` RC=0;
  `pruefe-syntax.sh` SYNTAX ALL PASS (EBNF 179/0 open).
- Codes/gifts/examples consumed: **one code (`N426`, from the returned
  240 reserve `N426`–`N430`)**, **one gift (`1088`)**, no examples (demos
  need emission — deferred, stated, not taken).

## 4. What I believe is wrong in the task (three frictions, one deviation)

1. **"table/arena declarations".** The merged sentence
   `arena.wachstum_sichtbar` (240) reserves a `max` clause on tables as
   future syntax — "not parsed, not refused, not built". I built
   arena-only and kept that sentence true. If tables want the clause, that
   is a Spec diff with its own lane, not a quiet widening here.
2. **242's "no new code expected".** 242 §4 says over-`max` growth refuses
   "with no new code expected" (extending gift 1087/`N212`). Measured
   against the sentences: `N212` says the `else` is OWED past the
   reservation — it cannot carry a refusal of a request that HAS its
   branch without lying about what the code means. `N426` owns the two
   genuinely new shapes (uncountable amount, past-ceiling request) with
   one rule and one sentence, the `N210` precedent. One code, not zero.
3. **Preamble vs task** (as in 240/242): the wave preamble says
   "independent reviewer, change no existing file"; the lane task orders a
   syntax + checker + probe build. I followed the specific task.
4. **Stale prose left standing.** `beispiele/153-arena-waechst.gab`'s header
   says the `max`/`grow` syntax "is not in the tree yet" — false since
   this lane. Left byte-identical on purpose (corpus diff zero); the
   orchestrator may want a comment-only touch-up pass over 153/154.

## 5. Open (not mine)

- The emitter arm (248's SPEC §4, bindings in §2 above).
- The checker-rules lane: `R-max` above `hi`, `N212` re-pointed at the
  committed value where it exceeds `hi` (both marked inline in
  `arena.rs`); the Lean dynamic form (`ArenaDyn` refinement of the static
  `ArenaForm`).
- `zaehle-gifttreffer.py` reports DECKE 41 vs mark 24 and 7 FEHLT on this
  tree — all in other lanes' probes (start-exclusivity `N240`/`N303`,
  syscall emitter codes `C180`/`C185`, H/K pairs); no `N21x`/`N426`/arena
  probe is non-clean, and 1087/1088 are sauber. The marks predate waves of
  merges (229/235/245/249/253/O-1); re-booking them is the orchestrator's,
  with those lanes' reports. `pruefe-syntax.sh`'s `Warnungen` stage aborts
  here (it calls bare `cargo`, not on PATH — lane rules forbid it); the
  stage replicated through the slot shows zero warnings in any file this
  lane touched.

## Names added

- `gabbro-syntax`: `Kw::Grow`; `StmtArt::Grow`, `GrowStmt { tisch, mehr,
  sonst }`; `ArenaDecl::max`; `parse.rs::arena` max clause, `Grow` arm.
- `gabbro-check`: `ArenaSig::max`; `arena.rs::deckenwert`,
  `Laeufer::decke`, `Laeufer::grow`, `wachstumstests::
  decke_ohne_klausel_ist_boden_mit_klausel_ist_max`; `saetze.rs::
  arena.wachsen_commit`; codes `N426`; gift `1088`; `paesse.rs::
  arena_grow_ueber_decke_n426`, `arena_grow_menge_unkonstant_n426`,
  `arena_grow_unbekannt_n213`; `arena_dynamisch.rs` (6 tests).
- No Lean definitions, no theorems — no rule-13 `_zeuge` owed on the Lean
  side; the inhabitation burden is carried by execution instead: the
  `N426` poison and its clean twins jointly instantiate every new premise
  on a non-degenerate program (a written table, a reached run whose
  `grow` commits storage).
- Last `./lean-bau` result line: `== lake exit code: 0`.
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`.
- Last `./emission-pruef` result line: `== exit 0 (full log:
  .tmp/emission.log, 694 lines)`.
