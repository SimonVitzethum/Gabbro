# Upstream PR 2 Rust review: compiler validation and ELF integration

Lane 716. Pinned PR2 head `987b286df9d8465714a00bab8226f7b9c7f4afc1`, base
`5d5a72e5889a3063b417b955fa7824e72c52ef7c` (PR1 head). Scope of this review
is the Rust side and its integration; the Lean proofs are taken as the
specification they claim to be, and every Lean claim below was checked only
far enough to judge the Rust mirror against it.

## 0. What the PR touches (measured, not assumed)

`git diff --name-only base head` = 27 files, all insertions, no deletions:

- Rust (8 files, all under `crates/gabbro-check/src/x86/`): `codec.rs`
  (772 lines), `codec_golden.rs` (4372), `elf.rs` (257), `lower.rs` (390),
  `mod.rs` (48), `opt.rs` (2019), `pipeline.rs` (2119),
  `pipeline_golden.rs` (2037). `typen.rs` predates the PR (wave A).
- Lean (18 new files under `grammatik/Grammatik/X86/`) + 18 import lines in
  `grammatik/Grammatik.lean`.

Nothing else moves: no checker pass, no `emit.rs`, no CLI, no `Spec.lean`,
no `gabbro_syntax` change. Outside-x86 Rust regressions are impossible by
construction; the only cross-cutting build risk is a broken
`Grammatik.lean` import, which is a Lean-gate matter, not a cargo matter.

## 1. The integration question this lane was asked to answer

Does `compile_to_image` call Lean, export actual source/cert/final-image
candidate, parse a generic Lean verdict, or merely run a handwritten Rust
mirror? Answer, from the code:

**A handwritten Rust mirror, with no live Lean step and no user path.**

Evidence:

1. `mod.rs` (PR's own words): "Unwired: no checker pass, no emitter
   template and no CLI reads this module."
2. `opt.rs` CUTS: "No conversion from `gabbro_syntax`/`gabbro-check`'s
   checked AST ... A real conversion is future work" and "No CLI wiring:
   `optimise`/`find_strength_opportunities` are library functions nothing
   calls yet."
3. `pipeline.rs` `Program` is a hand-built Rust model (`Deklaration`,
   `IntExpr`, `BoolExpr`, `Block`, ...), NOT the typed Lean syntax and NOT
   the gabbro AST. Its CUTS say so explicitly: "The input model is NOT the
   typed Lean syntax: a `Program` can be ill-typed", recompensed by a
   `typ_ok_block` re-check inside `compile_to_image`.
4. `pipeline.rs::validate` is a Rust re-implementation of Lean's
   `validate` (same three conjuncts: bytes equal the recompiled encoding,
   decode back, data separated from code). It never shells out, never
   reads a Lean verdict. Grep over all eight Rust files: zero process,
   command, network, filesystem or environment uses; no `unsafe`, no
   `todo!`/`unimplemented!` in library code (remaining `unwrap`/`expect`/
   `panic!` are inside `#[cfg(test)]` modules only, verified by line).
5. The "agreement with Lean" is two frozen artefacts: `codec_golden.rs`
   (4059 `#eval` stdout lines, generator harness scratch-only and NOT
   committed) and `pipeline_golden.rs` (`LEAN_AUSGABE`, 42 verbatim `FALL`
   blocks from branch `feat/x86-compiler-pipeline` at `af57ba71`).
   Both headers honestly state this is point-in-time evidence, not a
   machine-checked correspondence, and that the files go stale silently
   if the Lean side moves.

Consequence, stated plainly: golden agreement is not complete translation
validation, and today there is no closed loop at all — no `.gab` source
can reach `compile_to_image`, and no produced image is ever presented to
Lean by the toolchain. The PR body's sentence "Lean stays the authority"
is true of the theorems and false of any runnable path: the authority is
never consulted. This matches the PR's own CUTS ("equality with Lean is
tested on golden cases, not proved"), so it is a scope fact, not a
deception — but it must stay attached to every claim: this PR delivers an
untrusted producer plus frozen agreement evidence, not a verified
compiler path a user can run. In particular there must be no
`gabbro build --direct-x86`-style CLI activation on top of this code
until (a) a real AST conversion exists, (b) a live Lean verdict closes the
loop, and (c) images are loader-faithful (see §3).

## 2. Mirror fidelity (spot-checked against the Lean files in the PR)

Sampled function-for-function against
`ExpressionLoweringDeep.lean`, `Pipeline.lean`, `PipelineImage.lean`,
`PipelineEntry.lean`, `OptimizationRules.lean`:

- `senk_tief` == `senkTief` (lit/var/weiter/add/sub/neg shapes, same
  scratch-stack sharing `tmp :: rest` with BOTH operands reusing `rest`,
  same `none` arms), `senk_vergleich` == `senkVergleich`,
  `senk_bed_t` negation table, `senk_pruef` exit re-check,
  `sprung_ok` (`k < 2^31`, equal to Lean's `dispWort` round-trip test),
  ite layout (`pt+5`, `pe` displacements), `prolog`/`prolog_ok` ==
  `prologPaare`/`prologOk` including the pairwise `ZugOk`
  (`q.0 != r.1 && q.0 != r.0`, later-pairs only — matches `List.Pairwise`),
  `ohne_doppel` (keeps LAST occurrence), `validate` (same three
  conjuncts as Lean's `validate`), `bau_ok` field-for-field against
  `bauOk` as far as sampled, `layout_ok`, `grund_liste`.
- Codec: canonical-only REX.W prefixes (`0x48/49/4C/4D`, X=0), mod=3/mod=2
  dispatch, SIB `0x24` iff `reg_low(base)==4` (covers rsp and r12),
  mod=2/rm=5 (rbp/r13, no SIB) falls out correctly, push/pop short and
  `0x41` forms, `decode_all` fuel = byte length (each step consumes ≥ 1
  byte, so fuel always suffices).
- `i128` vs Lean `Int`: constructors saturate (`saturating_add/sub/mul`
  in `IntExpr::add/sub/mul/neg`), while `typ_ok_int` demands exact
  `checked_*` equality — saturated programs are refused as `IllTyped`.
  Documented asymmetric conservatism ("Rust may refuse where Lean
  accepts"), sound direction.
- `int_wort` wraps mod 2^64 via `rem_euclid`, matching `intWort` on the
  golden edges (`2^63`, `-2^63`, `2^64-1`); `slot_wort` is exact on
  non-negative in-range values (`rep_ok` forces the range non-negative).
- `sprung_disp` wraps via `rem_euclid`, matching `BitVec.ofInt 32`.

## 3. ELF container

`elf.rs` is the honest file in the PR. It writes a minimal static
ELF64 (`ET_EXEC`, one `PT_LOAD` per `Abschnitt`, `ELFOSABI_NONE`), reads
it back, and says what it does not do in its CUTS: byte-granular vs
page-granular loader mismatch (`p_offset ≡ p_vaddr (mod page)` fails;
neighbour bytes of different permission share pages), no section
headers/symbols/dynamic/interp/relocations/notes, nothing executed, and
only the FIRST entry round-trips (`eintraege[1]`, the code start behind
the prologue, has no ELF field and is dropped by `lies_elf`).

- `the_headers_carry_the_permissions` pins code R+X / stub R+X / data R+W
  (W^X holds per section in the model).
- `pilot_images_are_not_page_faithful` pins `!seitentreu(&bild(), 4096)`:
  the images are NOT loadable under a real OS loader, by test. This is
  the correct verdict and must remain a test, not a comment.
- No claim of loadability is made anywhere; the PR body disclaims it.
  Hold that line: nothing in the tree may present these files as
  runnable until a page-faithful layout exists.

Two minor blemishes (no repair demanded): `code_abschnitt_p` uses
`saturating_sub` for the prologue base — unreachable via
`compile_to_image` (the `bau_ok` gate requires `pl <= code_base`) but a
footgun for direct `baue_bild_p` callers; `lies_elf` accepts trailing
bytes into `datei`, which its "None on anything this writer does not
produce" doc sentence overstates.

## 4. Findings (all reproduced or precisely located; fixes proposed)

### B1 — `const_int` panics on `MIN / -1` and `MIN % -1` (bug, fix required)

`opt.rs:298-313`: `Div`/`SDiv` use raw `x / y` (line 304),
`Rem`/`SRem` raw `x % y` (line 312). Every other overflowing operator
uses `checked_*`; these two do not.
Counterexample (fixture-only probe
`crates/gabbro-check/tests/x86_716_sonden.rs`, NOT committed here):

```rust
IKind::Div(lit(i128::MIN), lit(-1))  // const_int: debug panic / release wrap
IKind::Rem(lit(i128::MIN), lit(-1))  // same
```

Lean's `Int` is unbounded, so Lean folds these fine — the Rust mirror
must return `None`, never trap or wrap. Reachability today needs a
hand-built `IExpr` (the pipeline model has no div nodes), but `const_int`
is `pub`, the producer calls it on caller-supplied blocks, and a panic
is the one failure mode this codebase otherwise refuses to have in
library code. Fix: `x.checked_div(y)` / `x.checked_rem(y)` (both return
`None` on zero divisor AND on `MIN/-1`), plus the two probe tests above
as permanent regression tests. One-line fix; no golden bytes move
(no golden case folds a division overflow — the suite passes either
way, see §5).

### B2 — strength reports `Shr`/`Shl` with `k >= 64` (advisory, bound before use)

`strength_div`/`strength_mul` accept any `k` with `const_int(b) ==
pow2(k)` (up to 126; only `strength_rem` bounds `k <= 64`). Reports are
"never certified" and no lowering consumes them, so nothing miscompiles
today. But `Shr(100)` for `x / 2^100` is a report a future lowering
must not emit as `shr reg, 100`: x86-64 masks the count to 6 bits, so
hardware would compute `x >> 36`, not `0`. (For `Shl(k>=64)` the side
conditions force the operand to 0, so hardware happens to agree; `Shr`
has no such luck, e.g. `x = 2^63, k = 64`.) Proposed: bound reports to
`k <= 63` for `Shr`/`Shl` (keep `Mask(64)` = identity, which is exact),
or record the bound as a premise on `StrengthOpportunity`. Cross-PR
note: the same bound question applies to Lean `checkStrength` consumers.

### B3 — `Shr` on negatives folds differently from Lean (divergence, cover or align)

Lean `constInt?` for `shr` is `x / 2 ^ y.toNat` with Lean `/` = FLOOR;
Rust is `x / pow2(k)` = TRUNC toward zero. Example: `Shr(-3, 1)` folds
to `-2` in Lean, `-1` in Rust. `Div`/`SDiv` agree (`Int.tdiv` is also
truncating), `Rem`/`SRem` agree (`Int.tmod`), `Shl` agrees, `Band/Bor/
Bxor` agree (`nat_trunc` == `toNat` on the mapped domain). The golden
suite evidently contains no negative-`Shr` fold (it passes — §5 will
confirm), so this bites only uncovered inputs. Proposed: one golden
case pinning the agreed direction, or align Rust to floor division for
`Shr`. Do not "fix" by weakening Lean.

### B4 — unbounded recursion over caller-built trees (robustness, cap it)

`sink_tief`, `apply_block`, `to_opt_*`, `typ_ok_*`, `slot_adressen`,
`grund_liste` recurse to expression/block depth with no bound; only the
cert producer has `STEP_CAP`. A 10^6-deep hand-built `IntExpr` exhausts
the stack and aborts the process (never an unsound accept, but a
denial-of-service on a library). Proposed: thread a depth budget
through the lowering/validator recursion the way `decode_all` threads
fuel.

### B5 — division-by-zero fold direction (safe, pin it)

Lean `lift2 Int.tdiv _ (some 0)` = `some 0` (Lean divides by zero to
zero); Rust returns `None`. Safe direction (refuse where Lean accepts),
and the golden cross-test
(`compile_to_image_agrees_with_the_lean_verdicts`, which asserts
two-sided agreement case by case) can only pass if no golden case folds
a division by zero. Proposed: add one div-by-zero golden case so the
direction is pinned rather than accidental.

## 5. Test evidence

Method (per lane task, disposable fixture only): fixture
`.tmp/fix716` = own tracked base + the exact 27 PR files overlaid
(byte-identical, verified with `diff -q`), plus a fixture-only probe
file and a fixture-only filtered wrapper `cargo-pruef-x86` (same
`cargo-slot`/`lean-slot` queues, `cargo test --no-fail-fast x86`).
Nothing in the reviewed clone was modified for testing.

- PR claim under test: `cargo test -p gabbro-check x86` — 137 passed
  (PR body), 42 golden `FALL`s, codec sweep of 4059 vectors.
- Methodology note (read, not run): the golden tests assert per-case
  two-sided agreement — compile bytes, validate bool, reasons,
  ohneDoppel, prolog bytes + ok, bauOk, full file bytes, sections,
  entries — plus name-list equality of the 42 cases. Strong evidence for
  the covered fragment. One nit: twin fidelity itself is checked by name
  list only (`every_lean_case_has_a_rust_twin_and_back`); a mismatched
  twin would have to survive the byte-equality assertions to matter,
  which it almost surely would not. Acceptable.
- Fixture run (measured 2026-10-02): `./cargo-pruef-x86` in `.tmp/fix716`
  reports `== exit 101; failing tests: 2` and
  `== total: 137 passed, 2 failed, 0 ignored`. The 137 are ALL of the
  PR's x86 tests — golden vectors included — so the PR's "137 passed"
  claim reproduces exactly. The 2 failures are the lane's own B1 probes
  and nothing else:
  `attempt to divide with overflow` at `opt.rs:304:22`,
  `attempt to calculate the remainder with overflow` at `opt.rs:312:22`.
  Full log: fixture `.tmp/cargo-test-full.log` (disposable, not committed).
- Full-suite baseline was deliberately not re-run: the PR changes no
  Rust outside `x86/`, so the non-x86 baseline cannot move; the Lean
  import gate (`Grammatik.lean` + 18 new modules) belongs to a Lean
  review lane with a warm cache, not to this Rust lane.

## 6. Verdict and concrete repair list

ACCEPT-AS-UNTRUSTED-PRODUCER after B1 is repaired; no CLI activation; no
loadability claim. Concretely:

1. MUST: `checked_div`/`checked_rem` in `const_int` + the two
   `x86_716_*` regression tests (promoted into the PR's own test
   module, fixture path above gives the exact bodies).
2. SHOULD before any consumer exists: bound `Shr`/`Shl` reports to
   `k <= 63` (B2), pin one div-by-zero and one negative-`Shr` golden
   case (B3, B5), depth-cap the lowering recursion (B4).
3. MUST NOT in this PR's name: expose a CLI build flag, claim a
   loadable/runnable image, or present golden agreement as translation
   validation. The review document trail (`dokumente/x86/`) must keep
   saying: producer + frozen evidence, loop not closed.

The PR body already says all of §6.3 honestly; this review's contribution
is verifying that the code matches the body's modesty, plus B1–B5 with
counterexamples and fixes.
