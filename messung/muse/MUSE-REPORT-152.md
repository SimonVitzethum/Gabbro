# MUSE-REPORT-152: bare atomics and variant constructors (T4 emitter findings)

Lane 152. Both T4 findings measured first, then fixed. No Lean touched.

## 1. Finding 1: bare read/assignment of an `atomic` — CONFIRMED, then fixed

T4 said `ort()` has no atomic branch, so a bare access emits the plain name.
Measured on the unchanged tree (`target/debug/gabbro`, three minimal probes):

| probe | `pruefe` | `emit` | `cc -Wall -Wextra -Werror` |
|---|---|---|---|
| `let x : u32 = AT;` (`relaxed`) | 0 errors | `uint32_t x = AT;` over `_Atomic uint32_t AT` | accepts, silent |
| `AT = w;` (`relaxed`) | 0 errors | `AT = w;` | accepts, silent |
| `if AT == w` | 0 errors | `if (AT == w)` | accepts, silent |
| `narrow AT to 0 .. 100` | 0 errors (E247 hint only) | `if (!(AT >= 0 && AT <= 100))` | accepts |
| `retry warten until USED_IDX != von` (`acquire`, `messung/proben/probe-transport-poll-used.gab`) | 0 errors | `for (; !(USED_IDX != von) ...)` | accepts |

So the defect is real and `cc` is no guard: a plain access where the
declaration said `relaxed`/`acquire` (C: `seq_cst`), stuck in the C model
(`C-SPEICHERMODELL.md` §1c: every atomic access goes through an explicit
`atomic_*_explicit` call, none is a plain access to an `_Atomic` object --
a census claim that was FALSE on this tree until this lane).

### Fix, split by direction (deliberately not one rule)

- **Reads lower in the emitter** (`crates/gabbro-check/src/emit.rs`, `ort()`:
  bare atomic read -> `atomic_load_explicit(&A, <load side>)`). The order is
  the LOAD side of the declaration (`release` loads `acquire`); `u.atomics`
  carries both. One branch fixes every runtime read position at once, because
  all funnel through `ort()`: expressions, `retry … until` conditions (via
  `pred_c` -> `ausdruck`), narrow bounds, indices. Refusing the read instead
  would make payload-free atomics (`publishes nothing`, `SPRACHE.md` §1.1)
  unreadable, kill the `retry`-spin (no `awaits` form spins), and break the
  shape `V009` hunts (blindstellen: "the plain load of an atomic is the shape
  `V009` hunts"). Shadowing is exempt through the four function-scoped views
  (`parametertyp`, `lokaltyp`, `werte`, `laufvariablen`) -- a parameter named
  `AT` keeps lowering as the plain C local (measured).
- **Stores are refused in the checker: `N270`** (`crates/gabbro-check/src/m1.rs`,
  `Zuweisung` arm, any `ZuwOp`, reports-and-continues like `M143`). Grounding:
  `SPRACHE.md` §11.3 says every store to an atomic IS a `publishstmt`.
  Lowering the bare store to an explicit store is no fix: the store is where
  the payload promise stands (V001-V004), and an explicit store without one
  would carry the pairing past the checker in silence. Needs the new
  `Umgebung::atomare` set + `nennt_atomic` (module-aware; the type in
  `globale` cannot tell an atomic from a `static`). Locals shadowing the
  atomic are exempt (`lage.lokal` first, mirroring `typ_von_ort`).
- **Suffixed reads are refused: `N271`** (same file, `ausdruck_roh` `Ort` arm).
  Found while sweeping: `let x : u32 = AT[0];` checked clean (indexed type
  falls out as untyped) and emitted `AT[0]` over a scalar. Legal indexed
  atomics (`FP_OWNER[core]` at `publishes`/`awaits`/`exchange`) never reach
  that arm (all three read their source via `typ_von_ort`).
- **Emitter backstop** (`anweisung`, `Zuweisung` tail): an atomic *target* is
  written as the plain name, never read through the new `ort()` branch (which
  is an rvalue). Through `gabbro emit` this line is unreachable (`N270`
  blocks first); it preserves the counterfactual byte-for-byte for the
  `-- erwartet: … allein` probes, which compile the checker-bypassed product
  to prove the checker is the ONLY guard.

After the fix: `let n = ZAEHLER;` -> 
`uint32_t n = atomic_load_explicit(&ZAEHLER, memory_order_relaxed);` the spin
in `probe-transport-poll-used.gab` ->
`!(atomic_load_explicit(&USED_IDX, memory_order_acquire) != von)` (the
declared order -- the file's own comment says the acquire load is what makes
the entry readable); `AT = w;` -> `N270`; `AT[0]` -> `N271`.

## 2. Finding 2: variant constructor `V(x)` — CONFIRMED as refused, pinned

`Kurz(x)` in a body: M1 leaves the callee untyped, `H021` errors (unknown to
the graph), `K003` beside it where costs are promised; `emit` writes nothing
(`has errors -- no C written`). So no generic call text escapes -- the
refusal is incidental (no rule owns the shape) but complete in every body
position measured (return, argument, statement, nullary `Leer()`, with and
without `costs`). Pinned with `beispiele/gift/938` (`-- erwartet: H021`) +
unit rows. The one checker-silent path is a `static` initialiser
(`static N : Nachricht = Kurz(5);`: `pruefe` green, emitter refuses `C001`) --
no body pass visits it; pinned by a unit test asserting the `C001` refusal,
not a gift file (the gift corpus runs the emitter only for `C001`-expected
files). A bare nullary variant (`let m : Nachricht = Leer;`) already falls
at `M119`. No lowering was built: a constructor would need a marke+union
literal the checker does not establish, so refusal (not lowering) is the
correct scope, and the codes for it already exist.

## 3. Corpus sweep (measured, script in `$TMPDIR/sweep.py` on this machine)

- Bare atomic stores (`=`, compound) outside `publishes`/`exchange`:
  **0 sites** in `beispiele/`, `messung/`, `sonden/`, `programmlogik/`.
- Bare atomic reads in executable positions: **1 site** --
  `messung/proben/probe-transport-poll-used.gab:46`
  (`retry warten until USED_IDX != von`); device-register untils
  (`g.fertig`, `k.STATUS.BEREIT`, `q.USED_IDX` in F04) are volatile reads by
  design, not atomics. `beispiele/gift/301:30`
  (`let versiegelt = VERSIEGELT;`) is the known `V009` poison probe -- still
  falls with `V009` (checker unchanged for reads), emission now explicit.
- Variant constructors called like functions: **0 sites** (tagged types are
  only matched on, never constructed, in the whole tree).
- Blind-spot effect (`gabbro blindstellen beispiele/*.gab --
  beispiele/gift/*.gab`): `75 blind · 171 covered · 26 poison-only · 12 no
  cell (of 285 pairs)`, from `77 · 170 · 25 · 12`. The delta is exactly this
  lane's files: `atomic × read` poison-only -> covered (116/117),
  `atomic × written` BLIND -> poison-only (936/937),
  `tagged × return (body)` BLIND -> poison-only (938).

## 4. What changed (names)

- Codes: `N270` (bare atomic store, `m1.rs::Pruefer` assignment arm),
  `N271` (suffixed atomic read, `ausdruck_roh` `Ort` arm). Both fire once per
  site and let the other passes continue. Reserved-but-unused: `N272`-`N274`.
- `Umgebung::atomare: HashSet<String>` + `Umgebung::nennt_atomic` (additive).
- Emitter: atomic read branch in `ort()`; atomic-target arm in `Zuweisung`.
- Sentence `m1.bare_atomic_place` over `["N270", "N271"]` (covers both halves
  incl. the codeless read lowering); `N270`/`N271` added to `korpus.rs`
  `BENANNT`.
- Gifts (all reserved numbers used except none spare -- 939 spent on `N271`):
  `936-bare-store-to-atomic` (`N270 allein`), `937-bare-store-despite-pairing`
  (`N270 allein` beside a live pairing), `938-variant-constructor-is-no-call`
  (`H021`), `939-index-into-atomic` (`N271`).
- Examples: `116-payload-free-counter` (bare read -> `relaxed` load),
  `117-message-passing-flag` (`publishes`/`awaits` pair). Both emit; `cc` and
  `clang -Wall -Wextra -Werror` accept both.
- Tests: `crates/gabbro-check/tests/bare_atomic.rs`, 13 rows (poison, silent
  twins, lowering text incl. load-side orders and the spin, `H021`, `C001`).
- Docs booked: `README` (371 diagnostics; 97/97 examples; 644 poison files;
  775 tests; blind spots 75·171·26·12), `TODO` (150 sentences / 142 measured
  / 320 claimed / 371 issued; lane-152 trailer; blind cells 171/26),
  `DONE` (97 / 644 / 775), `messung/ZEREMONIE.md` (lane-152 quote: 120/1621,
  delta exactly this lane's 11 sites).

## 5. Gates (this tree, this machine)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (775 passed total).
- `./emission-pruef`: `ALL PASS -- 35 durchgestochen, 240 von 240
  uebersetzen` (95 `beispiele/` incl. 116/117, clang accepts both).
- `pruefe-kennungen.py`: ALL PASS (371 codes, `N270`/`N271` single-filed in
  `m1.rs`). `pruefe-saetze.py`: exit 0 (`N270`/`N271` mapped, 55 ohne Satz
  unchanged). `pruefe-grammatiktafel.py`: GRUEN.
- `pruefe-todo.py`: 11 BEFUNDE, all pre-existing drift except none mine (my
  `~~369~~` carries its date; the `~~358~~` flag it sat beside is retired by
  the same date).
- `pruefe-zahlen.py`: 21 BEFUNDE, down from 24; every remaining one is red at
  base too (parallel-lane drift). Fixed three: `Absagekennungen` 369->371,
  gift-only cells 25->26, and the dead `besetzte Zellen` pattern (revived by
  moving history outside the bold span -- it checks 171 green again).
  Left red (base-red, my deltas noted): Zeremonie 120/1621 (mine +1/+11),
  reason-naming refusals +2 (exactly my two refusal texts), revocation files
  +2 (exactly my two examples), continuations +46 (my test/source lines).
- `pruefe-englisch.py`: ratchet red at base already (7949 vs 7905 booked, no
  German line added by this lane -- verified by stash A/B).
- `./lean-bau`: `Build completed successfully (112 jobs).` (no Lean files
  touched).

## 6. Open / CUTS

- `narrow AT to …` evaluates the place twice (condition + use) -- pre-existing
  narrow shape, now two explicit loads; check-then-use over an atomic is
  TOCTOU by construction, same as over a volatile register. Not refused.
- A `match`/`awaits`/`alloc` binder (or ghost `let`) shadowing an atomic name
  is not exempt in the emitter read branch (params, `let`s, record values and
  traverse binders are). No corpus site binds one; booked in the sentence
  vorbehalt, not closed.
- `AT[i] = v` (suffixed store) draws `N270` (basis check) but has no gift
  probe of its own (939 pins the read); the emitter still writes it plain.
- No Lean work: rules 12-13 N/A (no theorems added; new diagnostics are
  covered by gift/unit witnesses instead: 936/937 pin `N270 allein`, 939 pins
  `N271`, the `bare_atomic.rs` rows pin every refusal and every lowering).

## 7. Where I think the task (or the tree) is wrong

- The T4 report's §1c citation cuts the other way round: §1c *claims* zero
  plain accesses, but the tree EMITTED three shapes of them (bare read,
  bare store, atomic spin). The census was aspirational, not measured. This
  lane makes it true; the T4 lane owns the recount.
- "Refuse in the checker if lowering is out of scope" is the wrong default
  for the READ half: refusing reads would outlaw payload-free atomics and the
  spin with no replacement form in the language. The store half is the one
  where refusal is forced (payload promise). The split is the finding, not a
  hedge: each direction gets the mechanism its own discipline already names.
- `H021` as the variant-constructor refusal is load-bearing by accident: if
  the call graph ever learns variant edges, the refusal evaporates and the
  generic call text escapes to `cc`. A dedicated `M1` rule naming the shape
  would be strictly better; I did not build it because the static-init path
  (the only gap) is already refused (`C001`) and a third code for an
  already-refused shape buys overlap, not coverage. Flagging for the next
  lane that touches constructors.
