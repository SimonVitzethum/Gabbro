# MUSE-REPORT-1396 — Exact review of lane 1395 (language gaps)

Lane 1396, clone `/home/simon/Dokumente/gabbro-muse/a1396`, branch `muse/1396`
(verified via `git rev-parse`: branch `muse/1396`, HEAD `c943db2a`;
working tree clean — `git status` empty, `git diff` empty at review time).
Reviewed: author 1395, pinned HEAD `deca04b87ee91bd985a4d83c3f928686e4b2c73e`,
files `MUSE-REPORT-1395.md` + `messung/SPRACHLUECKEN-REPORT.md` (per
`.tmp/review/SNAPSHOT.json`, `clean: true`). Reviewed from
`.tmp/review/author-1395/` without git on the pinned hash, per task.
No Lean files in the reviewed material → no `./lean-bau` owed (none expected, none run).

## Machine-readable lines

CANDIDATE: 1395 deca04b87ee91bd985a4d83c3f928686e4b2c73e
VERDICT: ACCEPT

## Substance of the finding: ACCEPT (details below)

## What was checked

1. **Re-derived rows from primary sources (8 of 12):**
   - Row 1 (generics): `S20-typanwendung.gab` header lines 14–40 — `type Queue(T)`
     parses 0 errors, emit byte-identical to unparameterised, `w : T` falls
     `[C001] no lowering: field type`, `Queue<T>`/`table Queue(T)` → `P001`.
     Matches report verbatim.
   - Row 2 (record-as-value): `S18-verbund-als-wert.gab` header lines 8–25 —
     `return Completion(id: k, len: n)` checks 0 errors, emits, `lean-g`
     refuses `LG002` (record has no `Ty`). `LG002` confirmed as the
     no-`Ty`-form refusal in `crates/gabbro-check/src/lean_g.rs:178`.
   - Row 3 (traverse label): `S13-erster-treffer.gab` header lines 14–30 +
     `dokumente/SYNTAX.md:1355` (`traverse` binder is `ident`, label only on
     `retry`/`forever`) + `schleifen.rs:223-226` (`S001` "targets no enclosing
     loop label"). Exact.
   - Row 5 (option): `S12-option-als-typ.gab` header lines 13–24 —
     `option index into T` passes in all four positions, `option u32` →
     `[P001] 'index' expected`. Exact.
   - Row 6 (count): `S11-zaehlung-im-praedikat.gab` header lines 12–16 —
     `count` as `let` 0 errors (`beispiele/71:33`), in `invariant`/`spec fn`
     → `D021`. Exact.
   - Row 7 (strings): `saetze.rs:2975-2991` — `N465` refuses struct/table
     field, `const`/`static`/atomic positions. Exact.
   - Row 10 (bool static): `S16-bool-statik.gab` header lines 9–21 —
     `pruefe` 0 errors, `emit` → `[C001] no lowering: static with a
     non-constant initialiser`, all four bool shapes refused, `u32 = 0`
     emits. Exact. `C001` generic mechanism confirmed (`emit.rs:3729`).
   - Row 11 (plain payload): `OFFEN.md:1371-1383,1428` — `N485`, gifts
     1205–1210 reserved and unused, plain-payload rule open, `publishes { p }`
     with plain `p` stays refused. Exact. Class GUARANTEE correctly hedged
     as "named open premise, not a false rejection".
2. **No duplicate of unbounded dynamic structures:** no row concerns heaps
   without a ceiling (OFFEN O29, task-excluded). Rows cover generics,
   record values, traverse labels/windows, option, count-as-predicate,
   strings, byte pointers/regions, Endblock binders, bool statics, payload
   hand-off, dispatch ceremony — all disjoint from O29 and from each other.
3. **Measured vs assessed separated:** report marks only row 4 assessed,
   rows 1–3, 5–12 measured with probe-header/register citations. Row 4's
   `P001`-for-windowed-traverse claim is consistent with the grammar
   (`SYNTAX.md` traverse rule has no window arms; confirmed by read of
   `SYNTAX.md:1355`); marking it assessed rather than measured is the
   honest choice. No row I re-derived contradicted its marking.
4. **No guarantee-weakening proposal:** grepped the reviewed files for
   `propos|weaken|should (be|add|allow|accept)|relax` — zero hits.
   Workarounds carry costs; row 11's workaround (lock instead of lock-free
   hand-off) keeps the guarantee explicitly.
5. **Scope/ownership clean:** the submission touches exactly the two owned files;
   no language/checker/existing-file change, no new codes/gifts/examples,
   no `sorry`/`axiom` surface (Markdown only). Non-gap list correctly
   books closed items (pointer index, narrow scope, `let…else`, cross-unit,
   pools, `reason`-as-13th-pub-item) and LIBRARY content gated behind row 1.

## Minor notes (not REPAIR reasons)

- Row 12's Lean-correspondence remark (`stmt:switch-int` tied to constructed
  `CS.sw`) is assessed judgement without a cited probe line; it does not
  affect the row's measured core (1797-op chain, arms cap). Left as is.
- Owner's commit-blocker narrative (shell denied, then restored, committed
  `deca04b8`) is corroborated by BUILD-EVIDENCE.json (branch `muse/1395`,
  only the two owned files staged, commit hash matches SNAPSHOT).

## Build result

No build owed: the submission adds two Markdown files only; no Lean, Rust, or
corpus change. `./lean-bau` not run (no Lean files changed — none expected
per task). My own tree untouched (status/diff empty at review time).

## Blocker (resolved 2026-10-06)

`default.bash` was denied earlier in this session (permission gate rejected
the call); shell access was restored on continuation. Committed as
`89a88599` via `arbeitsprotokoll/.commitmsg` + `./commit.sh`, working tree
clean. No queued wrapper run owed (Markdown-only submission and report).
