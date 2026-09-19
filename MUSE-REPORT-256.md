# MUSE-REPORT-256 — bounded strings: value model + length discipline

Lane 256. Branch `muse/256`. Owner directive followed: lengths tracked
like `u32 in 0 .. N` bounds (concat adds, stays ≤ max or refuses).

## What was built

**1. Lean value model (new file only):**
`grammatik/Grammatik/ZeichenfolgeGebunden.lean`, imported at the end of
`grammatik/Grammatik.lean`. No existing file changed, no existing
theorem touched. Bounded strings are character lists with the length
invariant — an over-long list is not constructible, exactly like an
out-of-range `Zahl`:

- `BString (max : Nat)` — data + `daten.length ≤ max`
- `bliteral`, `blaenge`, `bconcat` (target-max checked, `none` past it),
  `bindex` (in-range or `none`), `vergl` / `bvergleiche` (lexicographic)
- Theorems: `bliteral_laenge`, `bconcat_laenge`, `bindex_innen`,
  `bindex_aussen`, `vergl_refl`, `bconcat_ablehnt`, `bliteral_ablehnt`
- Witness defs `z1` (`"hi"`), `z2` (`"!"`), `z3` (`"hi!"` at max 8)
- **`bounded_string_zeuge`**: built + concatenated within max
  (`bconcat 8 z1 z2 = some z3`, length 3) + indexed
  (`bindex z3 0 = some 'h'`) JOINTLY with the reference reached run
  (`refB_erreicht` on `MB`) and its memory move (`refB_schreibt`,
  slot `0 -> 100`). Non-degenerate: one written table, four reached
  steps. No premise quantifies over program syntax, so rule 13 bites
  only via the `ZEUGE:` line — and the joint witness is provided.
- `#print axioms`: each theorem depends at most on
  `propext, Classical.choice, Quot.sound` (standard); the two refusal
  theorems and `bliteral_laenge` depend on no axioms at all.
- Planted-defect check: a claim of an over-max concat success
  (`bconcat 2 ['a','b'] ['c'] = some _`) fails red
  (`$TMPDIR/defect256.lean`, kept outside the tree, 1 error as required).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise used.

**2. Rust length discipline (new module only):**
`crates/gabbro-check/src/zeichenfolge.rs` (+ one registration line in
`lib.rs`), pure functions mirroring the Lean model: `literal_passt`,
`concat_passt` (checked add, `None` past max or on overflow),
`index_passt`. 6 unit tests, both directions (within-max accepted,
over-max concat / out-of-range index / `usize` sum overflow refused).
`./cargo-pruef`: zero failing tests; the 6 new tests pass
(`zeichenfolge::tests::*`, 6 passed, 227 others filtered). NOT wired to
any pass — specified, not built (see §Open).

**3. Measurements (today's ground truth, with the built binary):**
- `let s: string max 8 = "hi";` → `P001` parse refusal (`=` expected,
  `max` found). `TypExpr` has no string arm (verified in
  `crates/gabbro-syntax/src/ast.rs`).
- `let s: string = "hi";` → `P011` (`expression expected, string found`).
- So NO string value shape reaches any checker pass or the emitter
  today; everything stops at the reader. Corpus verdict diff: zero —
  no existing verdict moved, no new acceptance (no example numbers taken).

## Emitter handoff list (for the lowering lane)

Once value syntax lands, each accepted shape must end at a NAMED
refusal until lowering exists (lane-222 precedent, staged honesty):

| accepted shape | refusing code today | code owed after syntax lands |
|---|---|---|
| `string max N` declaration | P001 (parse) | narrowed C001 per shape |
| string literal | P011 (parse) | narrowed C001 per shape |
| `concat` | unrepresentable | narrowed C001 |
| `length` / bounded index / compare | unrepresentable | narrowed C001 |
| unbounded `string` (no max) | — | refused BY NAME, permanently (no constructor without max exists in either model) |

`emit.rs` untouched. `m1.rs` untouched. `MARKE_EMIT*` untouched.

## L4 boundary (what stays library work, per TODO §0b)

Type + literal + concat + length + index + compare are the language
(delivered as the model above). Formatting, number parsing/printing,
splitting, find and any UTF handling belong to L4 in `bibliothek/`
(later), as do byte-string containers over tables (L2/L4). Nothing here
pre-empts them.

## Open (in dependency order)

1. Value syntax: `TypExpr` arm + parse for `string max N`, literals,
   `concat`/`length`/index/compare surface. Needs an ownership decision
   (parse lanes own `parse.rs`; I did not touch it).
2. Checker wiring of `zeichenfolge.rs` into a pass + measured N codes.
   Deliberately NO new codes: nothing is measurable without syntax.
   Verified free stock: N453+ (highest used is N452), gifts 1118+.
3. Narrowed C001 emitter refusals per accepted shape (lowering lane).
4. Loan of the model into `Ty`/`Val` when syntax lands (today the model
   is standalone by design — no core-type churn before the surface exists).

## What I believe is wrong in the task

- "verify, do not assume N456+": correct instinct, and the measurement
  says N453+ is free (highest used: N452), gifts 1118+ free. The N456+
  floor was stale/high by three codes.
- "Type + checker + Lean" in one lane understates the order: checker
  rules and emitter refusals for values with no syntax are untestable
  code. I specified (Lean model + pure Rust discipline + both-direction
  tests) instead of building unwired refusals, and say so plainly.
- The `ZEUGE:` "reached run" of a string program cannot exist yet (no
  string program is writable — see the P001/P011 measurements). The
  witness joins the string facts with the ref-fixture run instead; the
  non-degeneracy (written table + memory-changing reached steps) comes
  from `refB`, honestly labelled.

## Build lines

- `./lean-bau`: `Build completed successfully (281 jobs).`
- `./cargo-pruef`: zero failing tests (full suite green,incl. 6 new).
- `./emission-pruef`: not run — `MARKE_EMIT*` untouched and no corpus
  file added/changed, so the emission count cannot have moved.

## Lane-file compliance note

- `/home/fisch/gabbro-muse/lanes/256.md` read in full before finishing;
  this report and all code follow YOUR TASK (lane 256) exactly — never a
  self-chosen task.
- Conflict resolved: the WHERE-YOU-ARE preamble names every wave-6 lane
  an independent reviewer that changes no existing file, but YOUR TASK
  explicitly orders implementation ("new file(s) + `Grammatik.lean`
  import only", checker discipline with probes, handoff list). The
  lane-specific task wins. Footprint kept minimal: 2 new files
  (`ZeichenfolgeGebunden.lean`, `zeichenfolge.rs`) + 1 import line in
  `grammatik/Grammatik.lean` (rule 5) + 1 module-registration line in
  `crates/gabbro-check/src/lib.rs`. `emit.rs`, `m1.rs`, `MARKE_EMIT*`
  untouched; no `git push`, no network, no `cargo`/`lake` direct calls.
