# MUSE-REPORT-207 — Exporter width: full `Einheit` + `obligations --g`

Lane 207 (Rust, single-threaded width). Branch `muse/207`.

## What was done

1. **Census before/after over `beispiele/*.gab` (117 files): 15 export, before and
   after — the identical 15** (104, 108, 109, 118, 119, 120, 121, 124, 130, 15,
   16, 34, 62, 69, 73). First-refusal table before: LG001 x71, LG002 x19,
   LG003 x1 (131), LG004 x5 (61, 98, 99, 110, 125), LG005 x4 (11, 92, 93, 123),
   LG006 x2 (19, 46). Claim: nothing bigger than this.
2. **One faithful widening in `crates/gabbro-check/src/lean_g.rs` (`tr_traverse`):**
   `traverse i over slots of p` where `p` is a pointer-typed name in scope
   (parameter or `let`-bound pointer) now resolves to the table its type
   statically names. A `ptr<normal, _> T` names exactly one table, so the
   domain is the same one the table spelling names; the emitted term is
   byte-identical to the table-spelled loop. Anything else (integer, `bool`,
   unknown name) still refuses LG006 `is not a table`, as does a suffixed
   domain. Module doc (feature list + LG006 line) updated; no new code.
3. **Effect of the widening:** 19 and 46 move from LG006 to LG005 (`unknown
   name passes` — the invariant `n <= passes`; `passes` has no `Expr` form)
   with `+=` on a `let mut` local behind that (no `Stmt` form). Corpus gain:
   zero, honestly reported — a first-refusal count is not a count of programs
   gained (the same lesson the linear-family comment in `lean_g.rs` records).
4. **Tests in `crates/gabbro-check/tests/lean_g.rs`:**
   - `accepts_traverse_over_pointer_domain` (positive, two tables: domain is
     `GTab.T`, never `GTab.U`);
   - `refuses_traverse_over_integer_domain`, `refuses_traverse_over_unknown_domain`
     (poison, both LG006);
   - `traverse_pointer_domain_resolves_to_its_table` (the old
     `refuses_traverse_pointer`, whose pinned refusal this lane lifted —
     fixed, not deleted: same shape now asserts the export);
   - `einheit_width_travels_together` (integration: `gReq_arbeiter`,
     `starts := [⟨g_starter, .nil⟩]`, slot-zero + declared-global `gSp0`
     entries, `gS`, `gE` with `P`/`S`/`sp0`).
   `obligations_g.rs` untouched (no new field needed it); `tests/obligations_g.rs`
   untouched.
5. **Verification:**
   - `./cargo-pruef`: `== exit 0; failing tests: 0` (all suites ok).
   - `python3 instrumente/pruefe-genlean.py`: `== GENLEAN: GRUEN ==` (2 of 2
     files byte-identical, 18927 bytes) — the widening changes no byte of the
     104/108 output.
   - `./lean-probe` on both new-shape exports (pointer traverse; full-`Einheit`
     snippet with requires/start/sp0/S/gE): exit 0, 0 errors each — every
     `by decide` in the new terms elaborates. Probe files live in `$TMPDIR`,
     not committed.
   - `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s)`, and
     `Build completed successfully (268 jobs).`
   - Corpus verdict diff zero: `git diff --stat` touches only the two files
     above; no checker pass, no `beispiele/` file, no diagnostic text, no
     `MARKE_EMIT*` changed. No new diagnostic/gift/example numbers used.

## What remains open

- The 102 non-exporting corpus programs are blocked by real G gaps, all
  single-threaded ones surveyed: atomics/devices/linear marks/formats/groups/
  assumes/spec-extern-divergent functions (LG001, 71 files), option/wrapping/
  array/float/fn-pointer/record-value types (LG002, 19), call-in-contract
  (LG003, 131), compound assign and top-level call/alloc bindings (LG004),
  non-numeral consts (LG005), `passes` invariants (LG006). Each needs a model
  or surface feature, not an exporter tweak.
- 98/99 (top-level `alloc`) still refuse: `Block.arenaAlloc` is a `Block`
  former and a body is an `Endblock` — same class as top-level `bindCall`.

## What I believe is wrong in the task / tree

- The five width items (real `requires`, starts with args, `sp0`, `S`,
  `gE`) were already complete from lane 198. "Starts WITH their arguments"
  needs no work: surface `concurrent`/dispatch syntax carries names only, so
  `.nil` is the full width, and starts with parameters are refused LG001
  (test `refuses_start_with_params` pins it). Widening further needs new
  surface syntax, which is a language decision, not an exporter gap.
- `grammatik/Grammatik/Zielsatz/Spec.lean` header still says the exporter
  "fills neither `starts` nor `sp0` nor the source `requires`" — stale since
  lane 198. Left untouched (out of scope for this Rust lane); a doc-only fix
  is owed.
- `obligations_g.rs` comment on `gCs_voll` ("the export declares no global
  (`Glob := Empty`)") is likewise stale; the proof itself is generic and
  green. Left untouched per "prefer not touching it".
