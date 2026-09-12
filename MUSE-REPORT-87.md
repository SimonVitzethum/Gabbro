# MUSE-REPORT-87: bit intrinsics in the language (PLAN-BITS.md §3, surface half)

Lane 87 (Rust lane). The Lean model half (`grammatik/Grammatik/Bits.lean`, lane 68)
existed; this lane adds the surface: parsing needs nothing (see below), the
checker types the seven calls, the emitter lowers them, probes pin all four
halves. No Lean changes.

## What was built

**Surface: no new words, no grammar change.** The seven intrinsics
`clz(x)`, `ctz(x)`, `log2_floor(x)`, `popcount(x)`, `rotl(x, s)`, `rotr(x, s)`,
`bswap(x)` are ordinary single-segment calls claimed by name, exactly the way
the integer conversions (`u64(a)`, G9) are claimed by name. Consequences:

- Vocabulary stays at 226/226 (`pruefe-wortschatz.py` green, unchanged).
- No guardian pattern had to move (rule 14 vacuous: no document moved --
  no `.md` touched except this report).
- A qualified path (`m::clz`) is an ordinary call and never an intrinsic.
- A labelled call (`clz(x: v)`) falls through to `M107` (labels live only at
  constructors), the same sentence a labelled conversion gets.

**Typing** (`crates/gabbro-check/src/m1.rs`): `intrinsik_ruf` (hooked at the
top of `ruf_roh`, before conversions) + `intrinsik_bereich` (operand reader).

- `M157`: `clz`/`ctz`/`log2_floor` over a range admitting zero. Diagnostic
  names `narrow` as the remedy (task requirement), plus the V1 alternative
  (`if x >= 1`). Result `0 .. w-1` in the operand's own width.
- `M158`: unary-group shape (non-integer, signed, non-standard width, wrong
  arity). `popcount` result `0 .. w`.
- `M159`: rotation needs the exact full range (`min == 0 && max == 2^w-1`)
  and an amount in `0 .. w-1` (plus arity 2). Result is the full range.
- `M160`: `bswap` needs `u16`/`u32`/`u64` (plus arity 1). `bswap` over `u8`
  falls; narrowed ranges of the right width pass.
- `D003` (reused, same file): intrinsic over an `opaque` carrier.
- `Unbekannt`/`never`/empty operands stay silent (nothing to hold; `M117`
  owns the empty declaration). Opaque handling mirrors the `BinOp` path.
- V1/V2 facts are read (operands go through `ausdruck`), so a `narrow`ed or
  `if`-checked operand passes: pinned by tests.

**Deliberate boundary (sound refusal, task-conformant):** rotation over an
exact sub-width sugar range (`u13`, i.e. `u16 in 0 .. 8191`) falls at `M159`.
The checker reads the storage width (16); a 13-bit rotation in a 16-bit word
is a different function, and the type system erases `u13` from
`u16 in 0 .. 8191`, so no rule could tell which width to rotate in. Refusing
is the only direction that does not guess it. Pinned by test
(`rotl over exact u13 falls with M159 alone`).

**Name claim** (`crates/gabbro-check/src/namen.rs`): `intrinsik_name_vergeben`,
code `N058` -- any item (except `module`/`use`) named as an intrinsic is
refused, since the call form routes around it (prohibition-without-replacement
shape). Locals/params keep the names (conversion precedent, G9).

**Effect hull** (`crates/gabbro-check/src/aufrufgraph.rs`): seven `pure` root
nodes (same construction as the eight conversion nodes) -- without them every
intrinsic drew `H021` + `E009` over correct programs.

**Cost** (`crates/gabbro-check/src/kosten.rs`): one primitive op plus the
arguments (same as conversions/`Some`).

**Lowering** (`crates/gabbro-check/src/emit.rs`): `intrinsik_c`, hooked in
`ruf()` after conversions; width reader `intrinsik_breite` (operand's lowered
C type, never its range -- a narrowed `u32 in 1 .. 5` still counts 32 bits)
plus `ctyp_breite`; `wert_ctyp` answers the result width so
`let y = clz(x);` needs no annotation.

- `clz`: `__builtin_clz[_ll]`, adjusted `-24`/`-16` for 8/16-bit operands.
- `ctz`: `__builtin_ctz[_ll]` (width-independent).
- `log2_floor`: `(w-1) - clz` in the matching width.
- `popcount`: `__builtin_popcount[_ll]`.
- `rotl`/`rotr`: `gabbro_rotl32(x, s)` etc. -- a helper call, because the
  shift-or pattern needs the amount twice and an inline pattern would evaluate
  an effectful amount twice. Helpers (`DREH_C`, 8 bodies) mask the amount
  (`s &= w-1`, the masking the task asks for, which also keeps `w - s` below
  the width at `s == 0`); sub-32-bit bodies compute in `unsigned int` (a
  `uint16_t` promotes to signed `int`, and `x << 15` would leave it).
- Helpers are generated on demand: collection scans the lowered bodies for the
  emitted helper names just before they join the unit, so collection and
  lowering can never name different widths (the call site reads types from the
  per-function view no pre-pass walk can see). Only used helpers are emitted.
- `bswap`: `__builtin_bswap16/32/64`.

**Sentences** (`crates/gabbro-check/src/saetze.rs`): `m1.bitintrinsik`
(`M157`-`M160`) and `namen.bitintrinsik-name` (`N058`), both `Gemessen`
against `rechenwerk.rs`.

**Shared predicate** (`crates/gabbro-check/src/lib.rs`): `ist_bitintrinsik`
-- one claim read at all five call-by-name sites (m1, kosten, aufrufgraph,
emit, namen).

**Census** (`instrumente/zaehle-c-formen.py`): the nine `__builtin_*` names as
`U` catalogue entries + `NAME_FORM` rows (precedent: `__builtin_unreachable`),
and one `__builtin_clz(1);` line in `GIFT_POSITIV` so the counter shows it can
find the form (speechprobe verified in isolation: no failures).

## Probes (`crates/gabbro-check/tests/rechenwerk.rs`, 6 tests)

- `bit_intrinsics_lower_to_the_documented_c_forms`: text pins in both
  directions (every builtin spelling, helper call + body + amount mask,
  16/64-bit adjustments, and the negative rows: no unused `gabbro_rotr16/64`).
- `bit_intrinsics_run_under_cc_and_clang`: 17 value rows over all seven
  intrinsics and four widths, compiled `cc -O0`, `cc -O2`, `clang -O2` with
  `-std=c11 -Wall -Wextra -Werror`, run, exact `checked=17 bad=0` thrice.
- `bit_intrinsic_clz_refuses_a_zero_admitting_operand`: `M157` alone over
  `u32` (message + notes name `narrow`); `ctz`/`log2_floor` twins; silent
  twins (`u32 in 1 .. 100`, `if x >= 1`, narrowed `u13` via `narrow` with the
  `- 16` lowering pinned).
- `bit_intrinsic_rotl_refuses_a_narrowed_range`: `M159` alone over
  `u32 in 0 .. 5`, over amount `0 .. 32`, over exact `u13`.
- `bit_intrinsic_bswap_refuses_u8`: `M160` alone over `u8` and over `i32`.
- `bit_intrinsic_name_cannot_be_declared`: `N058` alone for `fn clz`.

## Verification results (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (rechenwerk 162/162,
  everything else green; includes the 6 new tests).
- `./lean-bau`: `Build completed successfully (50 jobs).` (no Lean changes).
- `./emission-pruef`: exit 1 with output **byte-identical to the pristine-tree
  baseline** (verified via `git stash`: same 373-line log, same counts) --
  all stage-9 funds are pre-existing count drift (73 vs 70, 132 vs 73, gift
  ceiling, `Claude outputs/` roots, umgekehrt 2 vs 4). No new stage failure
  from this lane. (Two runs: with-lane and stashed baseline.)
- `./lean-bau` result line: `✔ [49/50] Built Grammatik (157ms)` /
  `Build completed successfully (50 jobs).`
- Guardians: `pruefe-kennungen` ALL PASS; `pruefe-saetze` rc=0
  (310 codes, 121 sentences, 55 without sentence = mark, 0 invented);
  `pruefe-wortschatz` green; `pruefe-englisch` back to exactly the baseline
  triple (7905/1085/1, all pre-existing drift -- one of my comment lines
  briefly used the identifier `heisst` and was reworded; lane adds zero
  German lines); census speechprobe green in isolation.
- Full census (`--uebersetzer`): marks read 67/32 vs booked 66/31 -- the risen
  form is `__builtin_trap` (7 hits, UNBEKANNT), emitted by the bounds-check
  lowering of lane 141 (merged, predates this lane). None of my nine builtin
  names and no `gabbro_rot*` occur in the census output: **this lane
  introduces no new used C form, so no booking by me.** The `__builtin_trap`
  rise belongs to its owning lane, not here (booking another lane's form
  would misattribute the ledger).

## Number movements caused by this lane (not booked in docs -- see below)

- `pruefe-zahlen`: 23 baseline BEFUNDs -> 24 (same lines, moved numbers:
  PASSREGISTER sentences 119 -> 121, TODO Absagekennungen 305 -> 310,
  "tragenden Grund" 139 -> 143, new DARSTELLUNG row 7 -> 8 for `M159`'s
  width half, "ohne Grund" 107 -> 108, Zeilenfortsetzungen 4017 -> 4039).
  After the gruende-note pass all five new codes read `tragend`
  (`M159`/`M160` also match a DARSTELLUNG word each, honestly: width/bytes
  are what those rules are partly about).
- `pruefe-todo`: README Absagekennungen 304 -> 310 (same stale line).
- Deliberately NOT written into `TODO.md`/`README.md`/`PASSREGISTER.md`:
  every one of those lines is already stale at baseline (parallel lanes move
  the same numbers), and editing shared ledger lines from a feature lane
  conflicts with the lanes that own the drift. The exact deltas stand here.

## What remains open / remarks on the task

1. Sub-width exact sugar (`u13`) rotation is refused (`M159`), not lowered --
   see "Deliberate boundary" above. If the task's "`uN`" row meant 13-bit
   rotation in 16-bit storage, that needs the sugar width carried into
   `IntBereich` (currently erased) plus a masked 13-bit lowering -- a
   follow-up, not a bug.
2. Intrinsics in contracts (`requires`/`ensures`) are untyped-but-silent, like
   ordinary calls there -- no new hole, no new support.
3. `korr_form`/correspondence rows: expression-level `ruf` rows are booked as
   future work in the file itself (`corrcert`), unchanged by this lane.
4. The task's "Tests in rechenwerk.rs" and "`./cargo-pruef` green,
   `./emission-pruef` no new stage failure" are met; the Lean side needed no
   change, so rules 12/13 (target statements, witnesses) have no object --
   nothing added to `grammatik/`.
5. No `beispiele/*.gab` probes were added on purpose: versioned `.gab` files
   feed the C-form census and several count-marked suites; inline probes keep
   this lane's C out of every denominator. If example files are wanted later,
   expect the census `U` entries above to light up (by design) while the
   marks stay put.

## Files changed

- `crates/gabbro-check/src/lib.rs`: `ist_bitintrinsik`.
- `crates/gabbro-check/src/m1.rs`: `ruf_roh` hook, `intrinsik_ruf`,
  `intrinsik_bereich` (`M157`, `M158`, `M159`, `M160`, `D003` reuse).
- `crates/gabbro-check/src/namen.rs`: `intrinsik_name_vergeben` (`N058`),
  wired in `pass`.
- `crates/gabbro-check/src/aufrufgraph.rs`: seven `pure` root nodes.
- `crates/gabbro-check/src/kosten.rs`: 1-op intrinsic arm.
- `crates/gabbro-check/src/emit.rs`: `DREH_C`, body-scan collection,
  `ruf()` arm, `intrinsik_c`, `intrinsik_breite`, `ctyp_breite`,
  `wert_ctyp` arm.
- `crates/gabbro-check/src/saetze.rs`: `m1.bitintrinsik`,
  `namen.bitintrinsik-name`.
- `crates/gabbro-check/tests/rechenwerk.rs`: 6 tests (list above).
- `instrumente/zaehle-c-formen.py`: 9 `U` entries + `NAME_FORM` rows +
  one `GIFT_POSITIV` line (`ruf` 2 -> 3, `__builtin_clz` 1).
