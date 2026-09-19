# MUSE-REPORT-248 — emitter arm for reserve/commit: BLOCKED on the parser gap (TODO §-1 wave D, QUEUED post-235)

Lane 248, 2026-09-19. Scope as tasked: lower `max`-ceiling tables (reserve at
load, `grow` to commit calls, OOM-below-`max` boolean discipline) in `emit.rs`,
exclusively; no checker, no Lean, no `laufzeit/`, no `MARKE_EMIT*`, no OS
constants; new C forms through `pruefe-cformen.py`.

## Verdict in one line

**NOT BUILT — blocked by the same parser gap lanes 240, 243 and 242 already
recorded (240-F2, 243-F1, 242-F1): the tree has no `max` clause and no `grow`
statement, so there is no syntax for the emitter arm to lower. The task orders
that missing pieces are REPORTED, not re-specified, and forbids touching the
parser/checker — so any `emit.rs` edit now would either be dead code or an
invented second SPEC. Zero files changed; all three guardians green;
byte-identity holds trivially; `MARKE_EMIT` delta is 0.**

## 1. Why nothing was built (measured, not assumed)

Lane 242's SPEC (§4 of MUSE-REPORT-242.md) lists three start conditions "in
order", the first being: *"the parser lane lands `arena … max M` +
`grow A by n else B` into `StmtArt` (`ArenaSig::max`, `StmtArt::Grow`,
`SYNTAX.md` §9.1"*. On this tree (`8de4fc1a`, post-235/252/253):

- `crates/gabbro-syntax/src/ast.rs`: `ArenaDecl` carries exactly
  `name/oeffentlich/lo/hi/element/span` — **no `max` field** (lines ~1776–1786).
- `StmtArt` carries `Alloc(AllocStmt)` and `ResetArena(Ident)` — **no `Grow`
  arm** (`ast.rs` ~1330–1335). `grep -rn "Grow" crates/gabbro-syntax/src/
  crates/gabbro-check/src/emit.rs` finds only comments/prose.
- `parse.rs` parses `arena A capacity lo .. hi of T` only (§E4); **no `max`
  clause, no `grow` statement**; `SYNTAX.md` §9.1 is still unowned.
- Emitted C confirms it from the other end: re-emitted
  `beispiele/153-arena-waechst.gab` (89 lines) and `154-arena-voll.gab`
  (48 lines) contain **zero `gabbro_arena` references** — no descriptor, no
  reserve/grow call exists in any lowering path.

The alternatives were each forbidden by the task text itself:

- Emitting reserve/commit calls for *existing* `capacity lo..hi` arenas would
  rewrite every arena's C (breaking the byte-identity 242's demos pin),
  move `MARKE_EMIT` for ~all arena programs, and contradict the SPEC
  ("taken iff `max` present") — that is a second SPEC, which the task
  explicitly says not to invent.
- Adding `max`/`grow` syntax would touch the parser/checker, which the task
  explicitly forbids ("NOT the checker (240 merged, read-only)").
- A speculative `emit.rs` arm on invented AST nodes cannot compile against
  the real `ast.rs`, so even dead code is not writable without the syntax.

## 2. Verification (last lines, this tree, no changes)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full build + test).
- `./emission-pruef`: `== exit 0 (full log: .tmp/emission.log, 694 lines)`
  (288 emitting files translate, 36 units under ASan/UBSan, no finding).
- `./lean-bau`: `Build completed successfully (280 jobs).` (no Lean file
  touched; the run is the machine check behind that claim).
- `git status --short`: empty except this report (scratch emission probes
  under `.tmp/emit248/`, git-ignored, not committed).

## 3. Byte-identity statement (deliverable 2)

The static-prefix C is byte-identical before/after this lane **by zero diff**:
no file was changed, so no emission moved. Recorded re-emit on this tree
(`target/debug/gabbro emit`, stdout capture):

- `153-arena-waechst.gab` → 89 lines, sha256
  `3fb26f57925760c5862b60ee6c73a400424edba82f3e8bc0858d1dbea0fb4867`.
  (242 reported 92 lines; the 3-line drift comes from post-242 merges —
  252 traverse, 235 never-asm, 253 thread-start — all of which own `emit.rs`
  regions beside the arena path, not from this lane.)
- `154-arena-voll.gab` → 48 lines, sha256
  `878288ba4c720fbd7d378adbef455dca7c4f2e46e565802a36eb8fa1599c2c93`
  (matches 242's 48 lines).
- Both: `grep -c gabbro_arena` = 0 — the dynamic form's growth section has
  nothing to append to yet.

## 4. MARKE_EMIT delta (deliverable 3 — reported, not bumped)

**+0.** No new emitting root was added (no probes committed — see §5 why),
and no existing emission changed. Script values untouched: `MARKE_EMIT=125`
(the two 242 demos already booked in `dc651170`), all `MARKE_EMIT_*`
unchanged. The merger has nothing to bump for this lane.

## 5. What was deliberately NOT done, and why

- **No probes committed.** A positive probe needs `grow` syntax that does
  not parse; a poison probe needs an over-`max` refusal that belongs to the
  checker (240's cap rule, gift 1087 already pins the branchless shape). A
  `.gab` file that cannot parse is not a probe, it is a red corpus file.
- **No `pruefe-cformen.py` rows.** No new C form is emitted (nothing calls
  `gabbro_arena_reserve`/`gabbro_arena_grow` from generated code), so no
  row is owed; the existing `stmt:store-array` / `expr:array-read` rows
  already cover the static arena shapes. When the arm lands, the two call
  sites (reserve call, `if (gabbro_arena_grow(...))`) each need a row:
  lemma or named assumption, never silent.
- **No N codes, no gifts consumed.** Lowering lane by design; refusals stay
  the checker's.
- **No Lean touched**, so no rule-13 witness is owed; per the preamble no
  existing file was changed at all.

## 6. Unblock condition (for the orchestrator)

This lane becomes buildable when, in order: (a) a parser lane lands
`arena … max M` + `grow A by n else B` in `StmtArt` + `SYNTAX.md` §9.1;
(b) 241's rule names fix the refusal arms. Then 242's §4 SPEC applies
verbatim — file/place (`emit.rs` `fn arena` dynamic arm + `Grow` lowering
beside `Alloc` + unchanged `ResetArena`), descriptor shape, alloc/grow/reset
lowering, and test obligations (executed grow + refuse-on-full at
`-O0`/`-O2`/UBSan + stage-9 `-c`, 370/1004 shapes reused). Nothing in the
SPEC needs re-derivation; that is why this report adds none.

## Names added

- None (no definitions, no theorems, no code, no probes).
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`.
- Last `./emission-pruef` result line: `== exit 0 (full log: .tmp/emission.log, 694 lines)`.
- Last `./lean-bau` result line: `Build completed successfully (280 jobs).`

Open: the parser lane (242-F1, still unowned) then this emitter arm per
242 §4; the static-vs-dynamic op tally (§5/§8 of 242) once it lands; the two
(d) assumption texts' wiring into `Spec.lean` (241's lane).
