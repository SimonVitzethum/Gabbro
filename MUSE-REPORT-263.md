# MUSE-REPORT-263 — OFFEN O12 half (2): the checker refusal at a release

Lane 263, branch `muse/263`. Scope: close OFFEN O12 half (2) — refuse a locked
section whose invariant does not follow at its exits. No Lean theorems added
(the model correspondence is stated in a comment and in O12, per the task's
fallback); no `emit.rs` lowering, atomics or linking touched; `MARKE_EMIT`
untouched (emission delta: none — `./emission-pruef` ALL PASS, see §5).

## 1. What was built

**`N511` — the release refusal** (`crates/gabbro-check/src/freigabe_pruef.rs`,
`pass`, wired in `lib.rs::pruefe` beside `sperrinv`). At every exit of a
`locks L { … }` section (`release`, early `return`, `leave`, `next`) the lock
invariant must FOLLOW from three premises, and nothing else:

1. the invariant at acquire (the frame: a conjunct no write in the section may
   have touched still holds),
2. the section's own direct writes (`cell = <const>` establishes
   `cell == const`; compound assignment, `publish`, `exchange`, `alloc`,
   `reset`, `grow` kill without establishing),
3. what the section's callees PROMISE — the `==` equalities of their `ensures`,
   with parameters substituted by constant arguments — never their bodies.

Decided per `&&`-conjunct over cells and constants: equalities close by
union-find (shared value or shared root), constant-against-constant computes,
same-cell `<=`/`>=` holds. `old(..)`, calls, quantifiers, disjunction and
anything unresolvable cannot be shown and stay on the obliging side (refuse).
The diagnostic names the invariant (source-near clause text), the lock, the
exit (`release`/`return`/`leave`/`next` with its span) and the cells whose
value is not determined.

**One shared analysis, no second copy.** `freigabe::beurteile` returns the
structured verdict (`Abschnitt::{Unbekannt, OhneInvariante, OhneZellen,
Urteil}`; `AbschnittUrteil::{funktion, sperre, braucht, rufer, gruende,
ausgaenge}` with per-exit `Ausgang::{art, span, fehlt}`). Both the
`RELEASE HOLDS` rows (`freigabe_abschnitt`, read by `obligations_g` and
`gegenbeispiel`) and the `N511` refusal read it — row and refusal agree by
construction, pinned by `freigabe_zeile_und_n511_stimmen_ueberein`.

**What the shared analysis learned since F7** (all inside `freigabe.rs`):

- `ptr`-parameter-to-carrier resolution: `k.slots[0].x` with
  `k : ptr<normal, rw> A` IS `A.slots[0].x` — for kills, promises, effects
  (`writes k.slots`) and facts alike. Before, such a write killed everything
  (`Toetet::Alles`) and promised nothing.
- named `const`s read as their values; unconditional `let x = <const>` binds
  them (re-bound or conditionally written locals lose the binding).
- literal-index direct writes kill cell-exactly (siblings' facts survive);
  every other kill stays carrier-wide or global. (`ort_exakt`: all indices
  are literals.)
- conditional calls never promise and conditional writes never establish,
  while their kills still count (unchanged from F7).

## 2. Why 119 is silent (the measured false positive, closed without weakening)

Lane 204 measured that a promises-only refusal falls on `119`. It does not
fall here, and the program is genuinely fine: `auffuellen`'s
`k.slots[0].x = 40` through `k : ptr<normal, rw> A` establishes
`A.slots[0].x == 40`, and `40 <= GRENZE` (`GRENZE == 100`) re-establishes the
bound `A.slots[0].x <= GRENZE`. The rule reads the write (through the
parameter) and the constant (through the `const`) instead of demanding a
callee promise that does not exist. No premise was weakened to buy this: a
direct write of one cell of an equality still falls (gift 1264), and a write
through a computed index establishes nothing (`ort_exakt`).

## 3. Names of new definitions/theorems

No Lean theorems (no `ZEUGE:` line in the task; the executable witnesses are
the probes and the agreement test below). New Rust items:

- `freigabe_pruef.rs`: `pass(baum, absagen)` (the `N511` refusal).
- `freigabe.rs`: `beurteile(tree) -> Vec<Abschnitt>`, `Abschnitt`,
  `AbschnittUrteil::{haelt()}`, `Ausgang`, `beurteile_abschnitt`,
  `welt_bauen`, `ProgrammWelt`, `Konjunkt`, `konjunkte`, `Norm`,
  `norm_expr`, `traeger_von_typ`, `param_traeger`, `ziel_zelle`,
  `ort_exakt`, `konst_wert`, `vergleich_text`; `Lauf` gained
  `{konjunkte, params, fakten, beruehrt_traeger, alles_beruehrt, lokal,
  ausgaenge}` and `{merke_gleich, nimm_versprechen, nimm_konjunkt, gilt,
  folgt, kanon, folgt_cmp}`; `Gerufener` gained
  `{ensures, parameter, param_traeger}`; `Welt` gained `konstanten`;
  `toetet_von`/`ziel_toetet` take the callee's/section's `ptr`-parameter map;
  `toete` takes the exact cell; `menge_text` is `pub(crate)`.
- `saetze.rs`: sentence `sperren.freigabe` (`N511`); the `sperren.invariante`
  vorbehalt now records that the release shape is discharged (as `N511`,
  not the once-reserved `N279`).
- Tests: `n511_119_haelt_durch_direkten_schreibzugriff`,
  `n511_124_und_157_schweigen`, `freigabe_zeile_und_n511_stimmen_ueberein`
  (in `tests/obligations_g.rs`); `geprueft` helper in
  `tests/gegenbeispiel.rs`; updated `o12_*`/`f7_*` tests to the refusal world
  (UNPROVED snippets now fall with exactly `["N511"]`, HOLDS snippets stay
  at zero errors).
- Probes: `beispiele/gift/1261` (124's old weak `setze` shape),
  `1262` (callee overwriting a promised cell), `1263` (early `return` after
  the breakage — the `release` holds again after the restore, so only the
  `return` exit fires), `1264` (direct write of one cell of an equality).
  Each falls with `N511` alone (1 error). Positive probes: `beispiele/124`
  and `beispiele/119` (existing files, pinned silent in tests).

## 4. Measurements

- `./cargo-pruef`: `== exit 0; failing tests: 0` /
  `== total: 1345 passed, 0 failed, 1 ignored` (baseline before the lane:
  1325 passed in F7's report; the delta is this lane's new tests plus merges
  since).
- Corpus verdict diff: **no clean `beispiele/*.gab` file newly falls**
  (checked file by file: every summary reads `0 errors`; `N511` fires only
  on the four new gifts). The one verdict that moves is informational:
  `beispiele/119`'s release row moves `UNPROVED` → `HOLDS` (the direct write
  now establishes the bound — the false positive, fixed in the analysis
  rather than in the file).
- `./emission-pruef`: `== exit 0` /
  `== EMISSION: ALL PASS -- 41 durchgestochen, 297 von 297 uebersetzen ==`
  (ASan not run on this machine, as documented by the script itself).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (322 jobs; includes the regenerated certificates below).
- `instrumente/pruefe-saetze.py`: exit 0 (448 codes, 189 sentences; the
  `N511`-without-file FUND it prints before the commit resolves once
  `freigabe_pruef.rs` is tracked — it only counts `git`-tracked files by
  design).
- `pruefe-todo.py`: 16 findings (= F7 baseline); `pruefe-englisch.py`:
  7965 German comment lines (= F7 baseline, no new German).
- `tests/zertifikate.rs` regeneration: the changed release header text made
  23 certificates STALE (comment text only, plus 119's row flip); regenerated
  via `GABBRO_ZERTIFIKATE=schreiben ./cargo-pruef` per the test header
  (`GenOblig104/108.lean` + 21 files under `Zertifikat/`), green afterwards.

## 5. What remains open

- The bridge from the Rust verdict to the G term: `N511` discharges the
  release half of `SperrWechselG` with the acquire half as frame premise
  (stated in `freigabe_pruef.rs` and OFFEN O12, not proved — same standing
  as every checker sentence against its leg). A proved bridge would need the
  analysis formalised over `RufMaschineG` memories.
- Decided-never-proved corners, all in the `sperren.freigabe` vorbehalt:
  inequality promises beyond constants, arithmetic between promised cells,
  aliasing beyond declared carriers and `ptr` parameters, `const`-vs-literal
  index name mismatch (fail-closed), conditional-call purity (a conditional
  pure call no longer vetoes a hold — more precise than F7, sound by the
  carrier kill model).
- Reserved but unused: `N512`–`N515`, gifts `1265`–`1270`.

## 6. Notes on the task

- Nothing in the task turned out to be wrong. One design point needed a
  decision the task left open: the task asks that the row and the refusal
  agree, and the old row verdict (promise-cells + veto reasons) disagrees
  with entailment in both directions (119: row UNPROVED/refusal silent;
  covered-cells-wrong-relation: row HOLDS/refusal fires). I made the shared
  verdict entailment-based and kept the old reasons as informational row
  text — agreement holds by construction, and no pinned row string changed.
- Two implementation findings, both fixed in-lane: (a) a literal-index
  direct write must kill cell-exactly, or the second of two establishing
  writes wipes the first's fact (caught by the agreement test); (b) an early
  return *before* any write is harmless (the frame still covers it) — gift
  1263 returns *after* the breakage instead, so exactly the `return` exit
  fires.
- Lean side: no new file. Formalising the rule would be a second project,
  not a cheap lemma; the task's fallback (comment + O12 correspondence)
  is what stands.
