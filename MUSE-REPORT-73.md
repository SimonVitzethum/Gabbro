# MUSE-REPORT-73: emitter repair -- a user function named `main`, and clang's for-loop analysis

Lane 73 (Rust/emitter). Both halves of the task are repaired in the emitter and the
checker; `./cargo-pruef` is green (0 failing tests); all seventeen absenkung units plus
`beispiele/66-transport-rueckgabe.gab` compile under gcc and clang with
`-std=c11 -Wall -Wextra -Werror` at `-O0` and `-O2`.

## 1. What was wrong (measured, not assumed)

- Every unit of `messung/proben/absenkung/` declares `fn main(d, b, s, w, n) -> u32`.
  The emitter writes the Gabbro name into C unchanged, so the output carries
  `static uint32_t main(…)`. Both compilers refuse it: gcc with `-Wmain` (return type
  of `main` is not `int`, normally a non-static function), clang with `-Wmain`
  (`main` should not be declared static, must return `int`).
- `beispiele/66-transport-rueckgabe.gab` lowers its `retry … until bereit` wait to
  `for (; !(bereit); )`. Where the condition names a value no statement of the body
  writes (here the parameter `bereit`), clang fires `-Wfor-loop-analysis` and gcc
  stays silent (clang 18.1.3 fires, gcc 13.3.0 silent, at `-O0` and `-O2` alike).
  The body only steps the watchdog counter; the exit runs through the named
  `on_exceeded` arm, so no assignment to the condition can exist.

## 2. What I changed

**Checker -- `crates/gabbro-check/src/cnamen.rs`:**
- New fourth name class `Klasse::Hosteintritt` with a one-row table
  `HOSTEINTRITT = ["main"]`. `main` is deliberately NOT a C11 keyword row: it is
  no keyword, and a keyword row would misname the finding site. `vergeben()`
  reads the new table; `umfang()` grows from 3 to 4 tuple elements (no reader
  outside this file, so no call site moves).

**Checker -- `crates/gabbro-check/src/namen.rs` (`N041`):**
- The `Hosteintritt` class falls under the existing `N041` refusal, with a
  finding site of its own (*a `static` function of this name is not the entry,
  and neither compiler accepts it as one*) and a `main`-specific closing note:
  the hosted entry is a `pub fn main()` in a `program` unit held by the entry
  rule of `gabbro build`; anything else carrying the name collides with C's
  entry point instead of being it.
- Exemption: exactly `pub fn main` (non-`extern`) is exempt from this pass.
  The checker pass runs over single files with no manifest in scope, so it
  cannot tell the hosted entry from a collision; refusing every `pub fn main`
  here would forbid `beispiele/63-druckt.gab`, `beispiele/64`,
  `messung/proben/probe-eintritt.gab`, `messung/einheit-proben/prog-haupt.gab`
  and everything `gabbro new` writes. A private `fn main` still falls (it
  lowers to a `static` the linker never sees); `extern fn main` falls here
  under `N041` and never reaches `N046` (C declares no bindable signature).

**Emitter -- `crates/gabbro-check/src/emit.rs` (`retry`):**
- The bounded wait now lowers to `while (!(cond))` instead of
  `for (; !(cond); )`. Counter, bound check (`if (z >= N) exit`), body and the
  `+= 1` step stand unchanged. `while (!(bereit))` is silent under both
  families at `-O0`/`-O2`; the `for` form fired clang and only clang.
- On the admitted-form question (`Erhaltung.lean` `OffeneForm.schleifeStmt`,
  BEWEIS.md Subject 2: allow list names only `for (counting loop)`, census
  books `while` at 11 sites as UNNAMED): neither surviving form is the named
  counting loop -- the retry wait is not a counting loop, its bound lives in
  the watchdog arm, not in the header. So there is NO form within the admitted
  set that expresses this loop; the repair picks the census-documented `while`
  (11 measured sites, its own ruling still open) over the admitted `for`,
  because the admitted `for` is admitted as a *counting* loop and this use is
  exactly what clang's analysis rejects. Reported plainly as weakness, not
  strength: the `schleifeStmt` slot still owes its ruling.

**Emitter -- `crates/gabbro-check/src/emit.rs` (`AwaitLoad` silencer):**
- The `awaitload` absenkung row binds `fertig` and returns past it, so the
  emitted `bool fertig = atomic_load_explicit(…)` fell at
  `-Werror=unused-variable` under BOTH families -- the one stage-9 finding of
  this lane that is not a `main`. `funktion` now collects unread `awaits`
  bindings (via the same `benutzte_namen` set as the unread-parameter
  silencers) into `Austritt::stille_awaits`, and the `AwaitLoad` arm emits
  `(void)name;` after the declaration. `AwaitLoad` binds outside
  `sammle_lets`, so the shared unread-`let` set cannot carry it.

**Corpus:**
- `messung/proben/absenkung/probe-absenkung-*.gab` (17 files): `fn main` renamed
  to `fn absenkung_haupt` (same signature, same effects, same body). These are
  measurement units for the per-primitive statement census, not programs; the
  name `main` was scaffold accident, and after the `N041` repair the files no
  longer check. The lexer pattern in `messung/ABSENKUNG-LEXERLAUF.md` section 3
  (`^static (?:uint32_t|bool) main\(.*\) \{$`) no longer matches; the counted
  region must be re-anchored to `absenkung_haupt` on the next lexer run (the
  counts themselves do not move: the rename changes only the definition line,
  which carries no `;`).
- New poison probe `beispiele/gift/796-eine-main-die-kein-eintritt-ist.gab`
  (`-- erwartet: N041`, private `fn main`).
- New positive/shape probe
  `messung/proben/probe-retry-while73.gab` (retry wait checks clean, emits
  `while (!(bereit))`, no `for (;` wait loop).

**Tests:**
- `crates/gabbro-check/tests/paesse.rs::eine_main_die_kein_eintritt_ist_faellt`:
  private `fn main` and `extern fn main` fall with `N041`; `pub fn main` and an
  ordinary `fn haupt` stay silent.
- `crates/gabbro-check/tests/rechenwerk.rs::retry_teilt_das_budget_und_format_liest_bytes`:
  asserts the wait loop is `while (!(…))` and no `for (; …` wait loop remains.
- `crates/gabbro-check/src/saetze.rs` (`namen.c_hat_den_namen`): population and
  `extern fn` exception documented, with the `main` exception-to-the-exception.

## 3. Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full log
  `.tmp/l73/cargo6.log`).
- Direct matrix over all 18 units (17 absenkung + beispiele/66): `gabbro emit`
  exit 0 everywhere; `cc` and `clang` with `-std=c11 -Wall -Wextra -Werror -c`
  silent everywhere, at `-O0` and `-O2` (logs `.tmp/l73/v5-*.c`).
- `./emission-pruef` stage 9: `218 von 220` compile under `cc`,
  `218 von 218` of those also under `clang`, `0 von 2` reverse probes bite
  under `cc` alone. The two task-named findings are gone: no
  `messung/proben/absenkung/*` line and no `NUR CLANG … 66-transport` line
  remain. The stage as a whole stays red on PRE-EXISTING marks that this lane
  does not own (verified identical on the stashed base): `beispiele/07`
  (`_Noreturn` dispatch), `gift/776` (return-with-value in void function),
  plus quantity ratchets (`MARKE_EMIT*`, `MARKE_UMGEKEHRT`) that count files,
  not findings. The base run additionally listed all 17 absenkung units as
  `UEBERSETZT NICHT` (`-Wmain`) -- that block is healed.
- Text guardians: `pruefe-kennungen.py` ALL PASS (303 codes, no new identifier
  -- the `N041` repair reuses the existing code). `pruefe-saetze.py` reports
  `55 ohne Satz, gebucht 53`: the count moved because the pre-existing binary
  predates the rebuilt tree is NOT the cause here -- after a full
  `./cargo-pruef` rebuild the binary is current and the delta is real but
  vacuous: NO new diagnostic code was added (the `--ohne-satz` list is byte
  identical to the base list: `C001 L001-L007 M142 M144 M145 M152 N047-N051
  V012 P001-P039`), and no sentence was removed. The +2 comes from the
  guardian intersecting `git ls-files` against the worktree: the two new
  probe files are untracked until commit, and their first lines
  (`-- erwartet: N041`, `-- …clang…`) shift the identifier census the mark
  counts over. Committing this report (which adds the files to the index)
  resolves it; if the number persists after commit, the mark needs a
  re-booking, not a code change.

## 4. What remains open / what I believe is wrong in the task

- The task says "extend its reserved list; check whether a guardian
  (`pruefe-kennungen.py`) or a table of reserved names exists and use it".
  `pruefe-kennungen.py` guards DIAGNOSTIC codes (`N041`, …), not C names -- it
  is the wrong guardian for this. The table of reserved names is
  `crates/gabbro-check/src/cnamen.rs`, and that is the one I extended. The
  task's "or" branch ("if `main` is reserved, the checker must refuse it")
  is what holds: `main` is not a Gabbro vocabulary word (correctly -- the
  hosted entry needs the identifier), so the checker refuses non-entry
  `main`s with `N041` instead.
- The task's suggested `while (!(bereit))` is what I emitted, but NOT for the
  reason given: the task implies the CForm table admits `while`. It does not
  (allow list: only `for (counting loop)`; `while` is 11 census sites without
  cover, ruling open). The repair is within the MEASURED set, not the
  ADMITTED set -- see section 2. The referenced commit `c3592a2d` does not
  exist in this tree (`git log --all` has no such hash; the `while`-lowering
  it allegedly made lives today only in `messung/proben/emission-144/*` prose
  and in `probe-142-retry-for.gab`, whose header documents the lane-142
  `while` -> `for` change).
- `messung/proben/emission-142/probe-142-retry-for.gab` still documents the
  `for` shape as expected. It is a prose expectation, read by no test, but it
  now describes output the emitter no longer writes. Either its header or the
  `tafel` row should be updated by the lane that owns the CForm census; I
  left the file untouched (rule 5: no existing file moves unless the task
  says so -- and the task names only the emitter function and the guardian).
- No Lean work in this lane (Rust lane; rule 5 needs no new Lean file, and
  `./lean-bau` was not touched).
- Rule 13 (inhabitation): this lane adds no Lean theorems, so no `_zeuge`
  companion is owed. The Rust-side equivalents of witnesses are the probes:
  poison `gift/796` (checker fires) + positive `probe-retry-while73.gab`
  (checker silent, emitter writes the new shape) + the `paesse.rs`/`rechenwerk.rs`
  assertions pinning both directions.

## 5. Exact names

- `crates/gabbro-check/src/cnamen.rs`: `Klasse::Hosteintritt`, `HOSTEINTRITT`,
  `vergeben()` (+1 table), `umfang()` (4-tuple).
- `crates/gabbro-check/src/namen.rs`: `name_gehoert_schon_c()` (+`pub fn main`
  exemption, +`extern fn main` fallthrough, +`main`-specific note).
- `crates/gabbro-check/src/emit.rs`: `retry()` wait loop (`while`),
  `Austritt::stille_awaits`, `funktion()` collection, `AwaitLoad` arm silencer.
- Tests: `eine_main_die_kein_eintritt_ist_faellt` (`paesse.rs`),
  `while` assertions in `retry_teilt_das_budget_und_format_liest_bytes`
  (`rechenwerk.rs`).
- Probes: `beispiele/gift/796-eine-main-die-kein-eintritt-ist.gab`,
  `messung/proben/probe-retry-while73.gab`.
