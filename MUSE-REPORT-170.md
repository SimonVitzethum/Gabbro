# MUSE-REPORT-170: multi-dimensional arrays (language + checker + emitter)

Lane 170. The reviewer measured on 2026-09-14 that `static mut M :
[[u32; 4]; 3] = 0;` with `M[i][j] = v;` checks clean (grammar allows the
nesting, `M103` per dimension) but the emitter refuses with `C001`
`` `static` array over an unresolvable element type`` -- no C. No corpus
program used nested arrays. This lane builds the lowering. No Lean file
touched (§7 says what the model needs).

## 0. How this lane was executed (read this first)

`cargo`, `ssh` and `rsync` were unavailable when the work was done, so the
lane was first measured with `rustc` directly (§0b), and `./cargo-pruef`
plus `./emission-pruef` were run for real after the three commits
(reviewer instruction; both call `~/gabbro-muse/bin/cargo-slot`, which
puts `cargo` on the `PATH` itself). The two sources agree on every number
they share (883 tests; 250 emitting files, 248 compiling + 2 reverse).

### 0b. The rustc-direct second source (kept, not replaced)

The workspace has **no dependencies outside `std`** (`Cargo.toml`: the
list is empty), no `build.rs`, no `env!` in `src/`. So the three crates
build with the machine's own `rustc` (1.97.1) directly:
`gabbro-syntax` -> rlib, `gabbro-check` -> rlib, `gabbro-cli` -> the
`gabbro` binary. All artefacts lived in `/tmp/lane170/`; the tree was
untouched except by the lane's own edits. A copy of the binary also stood
at `target/debug/gabbro` (gitignored) so the binary-latched instruments
(`pruefe-saetze.py`, `zaehle-absagen.py --korpus`, `zaehle-zeremonie.py`,
`pruefe-grammatiktafel.py`) ran against exactly these sources.

- Every `cargo test` target was built with `rustc --test` and run: **883 of
  883 pass** (48 integration binaries incl. all of `tests/`, 167 lib unit
  tests in `gabbro-check`, 2 in the CLI; `CARGO_MANIFEST_DIR` /
  `CARGO_BIN_EXE_gabbro` supplied at compile time). No doc-tests exist
  (zero `/// ```rust` blocks), so the count is the `cargo test` population.
- `./emission-pruef`'s `lauf` for the two new examples was replicated
  step-for-step (emit twice bit-identical, licence head, `cc -O0`/`-O2`
  with `-Wall -Wextra -Werror`, run, UBSan, `zeugnis` line, poisoned-C
  counter-run), and its Stufe 9 was replicated over the whole tree (970
  `.gab` files: emit each, `cc -c` every product, `clang` second family).
- Machine: 110 GB total, 75 GB available, 16 cores (`free -g` beside the
  runs, per `CLAUDE.md`) -- no memory pressure at any point.

Where a gate cannot run here at all (`abnahme.py`, `lean-bau`, the
mutation run), §6 says so and names what stands in its place. Numbers
booked in `README`/`TODO`/`DONE`/`PASSREGISTER` are values the merge lane
re-derives with the real commands; §6 lists each with the command that
recomputes it.

## 1. Measurement: every position an array type can stand in (unchanged tree)

Measured with the pre-lane binary (built from `HEAD` sources), one probe
per cell. `pruefe` = checker errors, `emit` = emitter refusal or C.

| # | position (nested element type) | `pruefe` | `emit` |
|---|---|---|---|
| 1 | `static mut M : [[u32; 4]; 3] = 0;`, `M[i][j] = v;` / `M[i][j]` | 0 errors (M103 per dimension; 100 % M1 coverage) | `C001`: `` `static` array over an unresolvable element type`` -- the reported finding, reproduced exactly |
| 2 | `static M : [[u32; 4]; 3] = 0;` (without `mut`), read | 0 errors | same `C001` (same arm) |
| 3 | `const T : [[u32; 2]; 2] = [[1, 2], [3, 4]];` | **parse refusal `P011** (`expression expected, '[' found`) -- the checker never sees a row | never reached |
| 4 | table slot field `m : [[u32; 2]; 2]` | 0 errors | `C001`: `field type` (the same refusal a one-dimensional array slot field draws -- kept, §4) |
| 5 | struct field `m : [[u32; 4]; 3]` in a `type` record, `S.m[i][j]` | 0 errors | `C001`: `array field type -- element or length` |
| 6 | local `let m : [[u32; 4]; 3] = a;` | `M140` on the binding (shape held); uninhabited beyond that -- no literal, no call returns an array | `C001`: `` `let` without a resolvable type`` |
| 7 | parameter by value `f(m : [[u32; 4]; 3])` | 0 errors | `C001`: `parameter type` (C cannot pass an array by value) |
| 8 | parameter by pointer to element `f(m : ptr<normal, rw> u32)` called as `f(M[0], 1)` | 0 errors -- the row decays to a pointer to its element (`zerfaellt_zu`, `m1.rs`) | blocked only by row 1's `C001`; lowers once statics do (§3) |
| 9 | parameter by pointer to array `f(m : ptr<normal, rw> [u32; 4])` called as `f(M[0])` | `M140` (no decay array -> pointer-to-array; only array -> pointer-to-element decays) | `C001`: `parameter type` |
| 10 | index proof per dimension (`M[i][9]`, `M[9][j]`) | `M103` fires with the **inner** bound (`the array has 4 elements`) resp. the outer one | -- |
| 11 | cost of an index call in either dimension (`M[i][teuer()]`, `M[teuer()][j]`, `teuer` at `costs <= 100`) | `K001`: body costs 102 at a `<= 101` promise, **both dimensions** -- each index expression costs what it costs (the lane-139 F1 shape, already general over `ausdruecke_im_ort`) | -- |
| 12 | footprint (`effects { reads M }` vs `M[i][j]`, `E010`/`E247`) | recorded on the whole carrier (`M[…]`), prefix-matched against `writes M`/`reads M` | -- |
| 13 | whole-row store `M[i] = M[j]` (with `reads M, writes M`) | **0 errors, silent** -- both sides are `[u32; 4]`, `passt` compares shapes, which agree | would write `M[i] = M[j];`, which `cc` rejects (*assignment to expression with array type*) -- the hole this lane closes with `N287` |
| 14 | whole-array store, one-dimensional twin `B = A` | **0 errors, silent** -- same hole, one lane older | same uncompilable C |

Rows 1-9 are the six positions the task names (static / static mut are
rows 1-2; const, slots, struct fields, locals, params-by-pointer rows
3-9). Rows 10-12 are the task's checker requirement (3), rows 13-14 the
hole found while measuring it.

Two adjacent pre-existing holes, observed and NOT fixed (out of scope,
booked here so no later lane re-measures them blind):

- `const T : [u32; 4] = 0;` checks clean and emits `#define T 0u` with
  `return T[0];` -- `cc` rejects (`subscripted value is not an array`).
  Flat, older than this lane; the nested `= 0` takes the same path by
  construction and is no worse.
- `atomic A : [u32; 2]` parses (general `typeexpr`); `N287` covers the
  `Zuweisung` arm only, so a `publishes` over an array-typed atomic is
  unmeasured and stays so (no corpus site declares one; booked in the
  `m1.whole_array_store` vorbehalt).

## 2. Grammar: rows nest in `arraylit` (guardians first)

`array = "[" typeexpr ";" constexpr "]"` already recursed, so the TYPE side
needed nothing. The LITERAL side did: `arraylit` elements were `expr`, and
`expr` never reads `[`, so `[[1, 2], [3, 4]]` died at `P011` (row 3 above).

- `dokumente/SYNTAX.md` §1: `arraylit = "[" [ ( arraylit | expr )
  { "," ( arraylit | expr ) } [ "," ] ] "]" ;` -- inline recursion, no new
  rule (the count stays **177**, `pruefe-syntax.sh`: 177 defined, 0 open),
  no new terminal (vocabulary stays 240/240, `pruefe-wortschatz.py` green
  both directions). The lane-111 comment carries the lane-170 paragraph.
- `crates/gabbro-syntax/src/parse.rs`: `arraylit` delegates each element to
  a new `arrayelem` (`[` opens -> nested `arraylit`, else `expr`).
  `instrumente/leite-grammatik.py` derives one new decision point from it
  (`arrayelem.@EckAuf`); `miss-grammatikdeckung.py` iterates its fixed
  `PROBEN` table, so the new point is invisible to it (no ratchet on the
  population) -- noted, not healed, and out of this lane's scope.
- `pruefe-grammatiktafel.py`: **GRUEN, 0 von 240 UNGEDECKT.**

## 3. Checker: `N285`/`N286` (shape), `N287` (no whole array as target)

All three codes were free (no `N28x` in the tree) and each is issued from
exactly one file (`pruefe-kennungen.py`: ALL PASS, 381 codes).

- `N285` -- the literal's nesting against the type's (`konstanten.rs`,
  `check_eintrag`, two issuance sites, one rule): a value where the type
  declares an array (`[[1, 2], 3]`), or a row where it declares a single
  value (`[u32; 2] = [[1, 2], [3, 4]]`). Where the outer count misses too,
  `K191` owns the fault alone and the rows are never reached (measured).
- `N286` -- a row holding anything but the declared inner count
  (`[[1, 2], [3]]`: `` declares [2] at this dimension but this row holds 1
  entries``). Short, long and empty rows alike; the check is skipped only
  where the declaration names no count (same condition as `K191`).
- The recursion is generic over depth (`arraydimension` strips `Feld`
  through `Benannt`, never through `Zeiger` -- a pointer to an array is no
  row dimension). Leaves keep their old owners: unfoldable-but-foreign is
  `K190`, out-of-range is `K194` (`[[1, 2], [3, 300]]` over `u8` falls as
  `K194`, gift 950). The call hull (`K192`/`K193`) needed no change:
  `alle_ausdruecke` descends through nested rows already.
- `N287` -- a whole array is never a store target (`m1.rs`, `Zuweisung`
  arm, any `ZuwOp`, reports-and-continues like `N270`): `M[i] = M[j]` and
  the flat twin `B = A` (rows 13-14). A row into a scalar, or a scalar
  into a row, stays `M140`'s; a row read into a `let` stays
  emitter-`C001`. The corpus sweep is the `beispiele` suite itself: with
  `N287` active, every `beispiele/*.gab` still checks clean -- **0 corpus
  sites stored a whole array.**
- Sentences (both `[measured]`, `pruefe-saetze.py` exit 0, **55 ohne Satz
  unmoved**): `consts.nested_rows` over `["N285", "N286"]`,
  `m1.whole_array_store` over `["N287"]`.

Reserved but unspent: `N288`, `N289` (budget held, not spent).

## 4. Emitter: one declarator, three sites, zero drift elsewhere

- `feld_deklarator` (`emit.rs`): the innermost element's C word plus one
  `[n]` per dimension, outermost first. It spells lengths as WRITTEN
  (`feldlaenge`, so `[KAP]` survives) and serves the **struct field**
  (`verbund`: `m : [[u32; 4]; 3]` -> `uint32_t m[3][4];`). A `static`
  spells its lengths as VALUES (the `konst_oder_name` fold, the way `count
  N` and every other emitter length does), so `feldstatisch` builds that
  suffix beside its bounds out of the same numbers -- two conventions, each
  site keeping the one it always read (the split is documented at the
  function; getting it wrong changed 3 corpus outputs and the
  byte-identity census below caught it, §6).
- `feldstatisch`: `[[u32; 4]; 3]` -> `static uint32_t M[3][4] =
  {0};` (`static const` without `mut`). Per-dimension constant/zero
  checks, refusal order kept (length before element, so `[u32; 2 + 2]`
  still says "not constant"). `D5` reads the WHOLE object
  (`gesamt × width` vs `PTRDIFF_MAX`); `D12` fills every cell
  (`{{7, 7}, {7, 7}}`) inside the same byte budget, braces nested by the
  new `fülle`. (A non-zero fill never reaches the emitter on a checked
  tree -- `M140` owns the static-value shape since 2026-09-02, gift 662's
  fence story -- but `command_emit` runs the back end before the verdict,
  so the branch is exact where reached.)
- `const_table` / `const_wert_zeile`: `[[1, 2], [3, 4]]` over
  `[[u32; 2]; 2]` -> `static const uint32_t T[2][2] = {{1u, 2u}, {3u,
  4u}};`. Word at the innermost element (primitives only, the flat rule);
  dimensions down the first column (on a checked tree `N286` holds every
  row at the declared count); values from the checker's own folder; `None`
  anywhere is `C001`.
- Reads/writes at any depth and `elems of` over the outer dimension needed
  NO code: `ort()` walks every `[…]` suffix (`M[i][j]`, `S.m[i][j]`,
  `T[i][j]`), and the `elems of` header reads
  `sizeof(M) / sizeof(M[0])` = 3 outside and `sizeof(M[i]) /
  sizeof(M[i][0])` = 4 inside. The checker side was already general too
  (`M103` per dimension, `domaenenschranke` out of the declaration,
  `D018` classifying a nested static as an array).
- Table slot fields keep the refusal (`C001`: `field type`, flat and
  nested alike -- extending nested-only while flat stays refused would be
  incoherent, and extending both is a lane of its own with no measured
  need). Locals and by-value parameters keep theirs (`C001`, uninhabited /
  C-impossible). Pointer-to-array parameters keep `M140` + `C001`.
- `N288`, `N289`: unspent (see above).

## 5. Examples, gifts, tests (all reserved numbers spent as assigned)))

- `beispiele/122-matrix.gab` (3×4 `static mut`, written and read back,
  plus `leeren`: two nested `traverse … over elems of` loops zeroing the
  matrix; costs 4/3/36, each read off `K001`; two honest `E247` hints, the
  `beispiele/64` trade). `beispiele/123-const-matrix.gab` (const 2×2 read
  by index; costs 3).
- Gifts `948` (`M103`, inner index `M[i][9]`), `949` (`N286`,
  `[[1, 2], [3]]`), `950` (`K194`, `300` in a `u8` matrix), `951`
  (`N287`, `M[i] = M[j]`) -- each falls with exactly its one code.
- `crates/gabbro-check/tests/nested_arrays.rs` (11 rows: three lowering
  texts, struct field, nested fill on the parsed tree, `M103` outer/inner,
  `N287` nested/compound/flat-twin, element-store silence) and 5 rows in
  `tests/konstanten.rs` (`N285` both directions, `N286`, `K194`-at-depth,
  clean nested table).
- `./instrumente/pruefe-emission.sh` gains `TREIBER122`/`TREIBER123` with
  `lauf "beispiel122"` / `"beispiel123"` (expected `11 42 7 0 / 0 0 0` and
  `1 2 3 4`, poisons `(v + 1)` and `{5u}`, measured `zeugnis` lines).
- Registers, every number re-derived in-lane: `README` (157 sentences /
  149 measured / 330 claimed; 381 diagnostics; 103 examples / 656 gifts /
  883 tests; 250 of 250 emit+compile, 37 run; blind spots 75·172·25·12;
  usability 1669 sites), `TODO` (Stufe-9 line, blind cells 172/25, lane-170
  Satzkette trailer), `DONE` (103 / 656 / 883 / 37), `PASSREGISTER`
  (157 / 149 / 381 / 326, lane-170 paragraph), `ZEREMONIE` (124 von 1669,
  delta exactly this lane's 17 sites, none may-fall).
- One anchor repointed in `instrumente/mutiere-pruefer.py`
  (`feldlaenge-wird-geraten`: the struct-field line learned the suffix;
  same sabotage, `[1]` for the whole suffix), and `MARKE_PY` 1085 -> 1086
  in `pruefe-englisch.py` with a dated entry (the struck old anchor line
  carries a code quote and counts; debt booked, not repaid).

## 6. Gates and drift (run for real after the three commits)

- `./cargo-pruef`: **== exit 0; failing tests: 0** (883 passed total --
  the rustc-direct prediction confirmed to the test).
- `./emission-pruef`: **exit 1 with exactly one FUND, and the FUND is the
  frozen mark**: `FUND: 103 statt 101 emittierende Dateien in beispiele/`
  (my +2 emitting examples, the good direction; `MARKE_EMIT` untouched per
  reviewer instruction -- the merge re-measures it). Everything the run
  measured is green:
  - all 36 Differenztests pass every step, including the two new ones --
    `beispiel122` (41 lines C, bit-identical second run, licence head, cc
    `-Werror`, `11 42 7 0 / 0 0 0`, `-O2` identical, UBSan silent, **ASan
    silent**, poisoned C answers `12 43 8 0`, `zeugnis` line matches the
    booking) and `beispiel123` (25 lines C, `1 2 3 4`, poison `1 2 3 5`,
    same steps incl. ASan);
  - Stufe 9: **248 von 248 emittierenden Dateien uebersetzen** (103
    beispiele/, 12 gift/, 132 messung/*/, 2 messungen/, 1 programmlogik/,
    0 sonst), `clang` accepts all 248 `cc` accepts, 0 reverse probes biting
    under `cc` alone (mark 0 holds);
  - Stufe 10 (Bibliothekskette) did NOT run -- cut off behind the mark
    abort above (`ABGESCHNITTEN`, exit 1 as abort-for-the-rest, not as a
    finding about the chain; the chain is untouched by this lane -- no
    `library`/`build` surface changed).
- Test equivalence (second source): **883 of 883 pass** (48 integration
  binaries, 167 `gabbro-check` lib unit tests, 2 CLI unit tests;
  `t-rechenwerk` green from the crate dir -- its one failure from the repo
  root is a relative `../../beispiele` path, harness behaviour, not code).
- Emission equivalence (second source): the two `lauf` replications pass
  every step (same drivers/poisons/bookings as the real runs above; both
  units also pass `-Wpedantic`). Stufe-9 replication over the whole tree:
  **250 emitting files, 248 compile under `cc` and `clang`, 2 reverse
  probes correctly rejected -- GREEN**, identical category counts to the
  real run (103/12/132/2/1/0).
- Byte-identity census (old vs new binary over all 970 tracked `.gab`):
  **every pre-existing file emits byte-identical C.** (One iteration
  caught a spelling-vs-value regression on 3 files with `const`-named
  lengths -- `[KAP]` for `[64]` -- and was reverted to the value
  convention before it could land; §4.)
- `pruefe-kennungen.py` ALL PASS (381). `pruefe-saetze.py` exit 0 (55 ohne
  Satz; 157 sentences claim 326 codes; 0 invented).
  `pruefe-grammatiktafel.py` GRUEN (0/240 UNGEDECKT). `pruefe-cformen.py`
  GREEN (no new C-form state). `pruefe-deckung.py` GREEN (Lean coverage
  untouched). `zaehle-absagen.py --korpus`: 47 UNGEDECKT forms, none of
  them array-shaped (pre-existing population; my lane adds no form and
  closes none -- the nested-`static` row stays `ungemessen`, not
  UNGEDECKT). `gabbro blindstellen`: 75·172·25·12, delta exactly
  `traverse in traverse` poison-only -> covered (122's nested loop).
- Base-red, not mine (each verified by stash A/B on the unchanged tree):
  `pruefe-vergabe.py` 31 candidates / 86 affected probes vs booked 29/84;
  `pruefe-zahlen.py`'s `Absagekennungen` 371 vs 378. Still unrunnable here:
  `pruefe-todo.py` / `pruefe-zahlen.py` / `abnahme.py` / `lean-bau`
  (cargo/Isabelle); the merge lane re-runs them. Remaining prediction for
  it: `pruefe-zahlen` Absagekennungen 381 vs 381.
- Two instrument findings filed, not fixed (out of scope, both verified by
  stash A/B): (a) `pruefe-vergabe.py`'s `(.{0,600})` tail swallows any
  issuance site within 600 chars of another -- `K192` (2 sites, 0 seen)
  and my `N286` (1 site, unseen) prove it; single-site codes cannot be
  candidates, so no ratchet moves, but the population (412) undercounts
  clustered rules. (b) `const T : [u32; 4] = 0;` emits `#define T 0u`
  with `T[0]` uses (§1).

## 7. What the Lean model needs (no `.lean` file touched)

Today a compound is a table with `count 1` (a record) or `count N` (an
array): the field is a slot field, the element index an index type
(`SYNTAX.md` §2). A nested array is therefore a table whose element type
is itself a table-with-`count`. Two ways to carry that into the model,
and the choice is the later model task's, not this lane's:

- a **product index**: `[[u32; 4]; 3]` as `Tab` with `count (3, 4)` and
  the access `M[i][j]` as the pair index `(i, j)`, with the bound proofs
  per component (exactly what `M103`-per-dimension already establishes in
  the checker); or
- a **stated flattening**: `[[u32; 4]; 3]` as `Tab` with `count 12` and
  `M[i][j] = M[i*4+j]`, with a correspondence lemma (rectangularity:
  every row holds the inner count -- exactly what `N286` establishes)
  proving the flattened access equals the nested one.

Either way the new checker rules arrive as proof obligations, not axioms:
`N285` (nesting shape) is the well-formedness side condition of the
flattening/product introduction, `N286` (rectangularity) is the premise of
the correspondence lemma, and `N287` (no whole-row store) is already a
theorem-shape -- there is no Lean value for a row, so a store to one is
not even writable. The `elems of` traversal over the outer dimension is
`forallSlots` over the outer table (the existing `ElementeVon` arm).

## 8. Position-by-position result table (after the lane)

| position | checker | emitter |
|---|---|---|
| `static` / `static mut` nested, `= 0` | holds (unchanged) | `uint32_t M[3][4] = {0};` (NEW) |
| `static` nested, `= v ≠ 0` | `M140` (since 2026-09-02) | exact nested fill on the parsed tree (`fülle`; budget-fenced) |
| `const` nested literal, well-shaped | holds recursively (`K191` outer, `K194` leaves) | `static const uint32_t T[2][2] = {{1u, 2u}, {3u, 4u}};` (NEW) |
| `const` nested literal, misshapen | `N285` / `N286` (NEW) | `C001` (shape unlowerable) |
| table slot field nested | holds | `C001` (kept -- flat refused too) |
| struct field nested | holds | `uint32_t m[3][4];` (NEW) |
| local / by-value param nested | holds (`M140` on mismatch) / holds | `C001` (kept -- uninhabited / C-impossible) |
| by-pointer-to-element param + row decay | holds (`zerfaellt_zu`) | lowers once statics do (`f(M[0], 1)` -> `f(M[0], 1u)`) |
| by-pointer-to-array param | `M140` (kept) | `C001` (kept) |
| reads/writes at any depth | `M103` per dimension, costs per index, carrier footprint (all pre-existing, verified) | ordinary place lowering (pre-existing, now reachable) |
| `elems of` over the outer dimension | bound + kind pre-existing | `sizeof` ratio (pre-existing, now reachable; 122 runs it nested) |
| whole-row/array store | `N287` (NEW, incl. the flat twin) | never reached on a checked tree |

`N288`, `N289` unspent. Gifts 948-951 and examples 122-123 all spent as
assigned. Every emitting example passes the emission check: the real
`./emission-pruef` runs all 36 Differenztests green (122/123 incl. ASan),
and Stufe 9 is green at 248/248 with `clang` agreeing everywhere -- the
run's single FUND is the frozen `MARKE_EMIT` (103 vs 101, this lane's +2,
good direction), which the merge re-measures per reviewer instruction.
