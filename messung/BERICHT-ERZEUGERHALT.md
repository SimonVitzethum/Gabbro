# The emitter's third answer: output that grows with a VALUE

*Running report. Started 2026-09-02, worktree `agent-a0c686a610acf10c5`, base `26620f1`.*

**Six lanes died mid-run this week and each lost its report, not its code.** This file is
written from the first measurement onward and committed at every finding.

## 0. The finding, as handed over

```
static mut A : [u64; 100000000] = 7;

gabbro pruefe   accepted
gabbro emit     runs without end -- killed at 25 s, exit 124, empty output
```

Far inside `PTRDIFF_MAX`, so `D5`'s refusal does not fire. A non-zero initialiser is written
out element by element on purpose, and a hundred million elements is a hundred million lines
of C.

The emitter's promise has two answers -- *lower it, or refuse it by name*. This is a third.

## 1. Why the sweep counts it at zero

`instrumente/fuzze-erzeuger.py` measures exactly this property, and shape 1 (a panic, a
timeout, an unnamed exit) it reports as `0`. The reason is in the form table it borrows from
`fuzze-grenzen.py`:

```python
"array-laenge": """module f {{
static mut A : [u64; {V}] = 0;
}}""",
```

The initialiser is a literal **zero**, and a zero short-circuits to `{0}` in the emitter --
one line of C for any length. *A ladder with one rung measures one rung.*

## 2. THE FIRST CORRECTION TO THE MANDATE: `gabbro pruefe` does NOT accept it

Measured on `ki-pc-fisch-101`, base `26620f1`, debug binary:

```
module f { static mut A : [u64; 8] = 0;   }   pruefe exit 0
module f { static mut A : [u64; 8] = 1;   }   pruefe exit 1   M140
module f { static mut A : [u64; 8] = 7;   }   pruefe exit 1   M140
module f { static mut A : [u64; 8] = 255; }   pruefe exit 1   M140
module f { static mut A : [u64; 8] = 0x7; }   pruefe exit 1   M140
```

```
error: [M140] static value requires `[u64; 8]`, the value has `u8 in 7 .. 7`
       -- a number does not answer for an array
```

`M140` was added on **2026-09-02 by another lane** (commit `5065843`), for an unrelated
reason -- a value whose SHAPE does not match its slot. `m1.rs::gestalt_grund` lets the
literal zero through and nothing else:

```rust
if ist_null(quelle) && matches!(z, "a pointer" | "a record" | "an array") {
    return None;
}
```

So the mandate's sentence *"gabbro pruefe accepted"* is no longer true of this tree.

## 3. AND THE FINDING SURVIVES THAT ANYWAY -- the work happens before the verdict

`crates/gabbro-cli/src/main.rs`, `command_emit`:

```rust
gabbro_check::pruefe(&baum, &mut absagen);
register.nimm_auf(datei, &baum, versatz, &mut absagen);
let c = gabbro_check::emit::emittiere_mit(&baum, &mut absagen, bau);   // <-- runs anyway
if absagen.fehler_zahl() > 0 {
    ...
    eprintln!("gabbro {getippt}: {datei} has errors -- no C written");
```

**The emitter runs unconditionally and the verdict is read afterwards.** So `M140` does not
stand between the user and the loop; it only throws away what the loop produced. Measured,
same file, debug binary, wall clock:

| `n` in `static mut A : [u64; n] = 7;` | `gabbro emit` wall | exit |
|---|---|---|
| 1 000 000 | 0.091 s | 1 |
| 10 000 000 | 0.868 s | 1 |
| 100 000 000 | **8.51 s** | 1 |

Linear, and the constant is about **85 ns per element**. `D5` refuses only past
`PTRDIFF_MAX` bytes, so for `u64` the emitter will happily start on

```
static mut A : [u64; 1152921504606846975] = 7;      /* PTRDIFF_MAX / 8 */
```

which at 85 ns per element is **about 3000 years**, having first tried to build a
`Vec<String>` of 1.15 * 10^18 entries. *That is not a slow answer; it is a third answer.*

## 4. THE CLASS, MEASURED -- 52 numeric slots, one of them linear

The question the mandate asks is not "is the array initialiser broken" but *"where else does
the output grow with a value rather than with the program text?"*. Answered by measurement
rather than by reading: every form of `fuzze-grenzen.py` that is swept with a numeric ladder
(51 of the 63) plus three this measurement owns, emitted at seven values spanning six
decades, with the length of the C recorded at each.

`grep` says the only numeric-range-driven text in `emit.rs` is two lines --

```
6216:    "    ".repeat(n)                                            # indentation, by nesting DEPTH
7420:    std::iter::repeat(w.to_string()).take(n as usize)           # the array initialiser
```

-- and the measurement below is what turns that into a number rather than a reading.

| verdict | count | forms |
|---|---|---|
| **linear in the value** (`O(V)`) | **1** | `static-array-nichtnull` |
| logarithmic in the value (`O(log V)` -- the printed digits) | 20 | `acc-percpu` `array-laenge` `ausdruck` `bank-at` `bank-count` `bank-stride` `boot-step` `const-als-schranke` `const-wert` `embeds-scale` `entry-ist` `entry-nested-bounded` `entry-vector` `if-bedingung` `let-wert` `reason-code` `static-array-null` `static-array-u8-null` `static-wert` `table-count` `zuweisung` |
| constant -- text-driven | 17 | `aligned-n` `aufruf-argument` `costs` `format-version` `gleitkomma-bereich` `invariant-kosten` `lock-held` `lock-rank` `lock-shared-held` `range-einpunkt` `range-hi` `range-lo` `range-offen-hi` `reg-bit-hi` `reg-bit-lo` `reg-versatz` `slot-bereich-hi` |
| fewer than two accepted rungs -- no slope measurable | 13 | `bank-regversatz` `embeds-hi` `embeds-lo` `forever-schranke` `format-bit-hi` `format-bit-lo` `gleitkomma` `index-stelle` `range-verkehrt` `retry-schranke` `static-array-nichtnull` `walk-knoten` `walk-levels` |

**The denominator is 54 numeric forms** (51 read out of `fuzze-grenzen.py`, 3 owned by this
measurement); 21 of them proved value-dependent at all, and **exactly one of those 21 grows
faster than the digits of the number**. The other twenty grow by 6 characters between
`V = 4` and `V = 1048576` -- which is `len("1048576") - len("4")`, the literal itself and
nothing more.

The raw table, C length in bytes:

```
form                               4         8        64       512      4096     65536   1048576
array-laenge                     504       504       505       506       507       508       510
bank-count                       861       861       862       863       864       865       867
table-count                      558       558       560       562       564       566       570
acc-percpu                      1832      1832      1833      1834      1835      1836      1838
embeds-scale                    1420      1420      1421      1422      1423      1424      1426
static-array-null                504       504       505       506       507       508       510
static-array-nichtnull             -         -         -         -         -         -         -
walk-levels                     C001      C001      C001      C001      C001      C001      C001
```

`table count`, `bank count`, `walk levels`, `embeds scale` were the mandate's own suspects,
and **none of them repeats anything per element**: a `table` lowers to one C array with the
count as its bound, a `bank` to one accessor with the count in an index expression, a `walk`
is refused by name at every rung, and `embeds scale` is one multiplication. The `-` column
for `static-array-nichtnull` is `M140` at every rung, which is section 2.

*This is the narrow, measured answer the mandate asked for: **array initialisers are the
only site in the emitter whose output grows with a value.** One of fifty-four.*

## 5. THE SWEEP FINDS IT -- and this is BEFORE any repair

`fuzze-erzeuger.py` gains **net 8: THE EMITTER DID NOT HALT**, beside the property rather
than inside it, for a reason that is measured:

* **Shape 1 already names a timeout, and it can only ever see one on an input the checker
  ACCEPTED.** The tool's `eine_probe` returns at the checker's verdict; the emitter is not
  started on the rest.
* **This case has no accepted population and never will.** `M140` refuses every rung of a
  non-zero array initialiser, the known-good baseline included -- and a form whose baseline
  the checker refuses stops the whole run with *THE GENERATOR IS BROKEN*, which is the right
  behaviour for a property about accepted inputs. So the non-zero rung cannot be added to the
  shared table; it needs a table of its own, and `HALT_FORMEN` says so at the site.
* **Halting is a property of the RUN, not of the C.** Nets 5 to 7 all read the emitted text;
  here there is no text to read. Only a deadline can see it.

The rungs, three of which must stay silent:

| rung | what it is | before the repair |
|---|---|---|
| `8` | the shared table's own known-good length | halts, exit 1 |
| `4096` | a page of `u64`, 8x the corpus's largest array | halts, exit 1 |
| `1000000` | a million elements, 0.091 s | halts, exit 1 |
| `100000000` | the mandate's own reproducer | **TIMEOUT at 3 s** |
| `1152921504606846975` | `PTRDIFF_MAX / 8`, the largest `[u64; n]` `D5` allows | **PANIC, `capacity overflow`** |

```
-- 8. THE EMITTER DID NOT HALT -- a deadline is the only reader of this: 2 --
   the back end runs BEFORE `command_emit` reads the verdict, so a refused input still drives it
   array-nichtnull  (2)
      `100000000`  the checker refused it, and `gabbro emit` still ran the back end -- no answer within the deadline
      `1152921504606846975`  the back end PANICKED on an input the checker had refused: thread 'main' panicked at
                             library/alloc/src/raw_vec/mod.rs:28:5: / capacity overflow
```

**Two faces of one defect, and the second was not in the mandate.** Past
`isize::MAX / size_of::<String>()` the `collect::<Vec<_>>()` reserves its slots up front and
`raw_vec` answers *capacity overflow* in two milliseconds. So the same slot gives a hang at
one size and a panic at another -- both third answers, both closed by one fence.

**And the boundary rung was wrong the first time, which is worth writing down.**
`(1 << 63) // 8` is `PTRDIFF_MAX + 1` over eight, so `D5` refuses it by name and net 8 came
back reporting only the timeout. *An off-by-one in a boundary rung does not look like a bug;
it looks like a repair.* Corrected to `((1 << 63) - 1) // 8`, and the panic appeared.

The net's own speech test runs in both directions before the sweep, over `sleep`: a process
that outlives its deadline must come back `TIMEOUT`, one that finishes at once must not.
`lauf` swallows every exception by contract, so a broken deadline would come back as a clean
answer and every hang would count as a halt. **Speech test 11 probes -> 13.**

## 6. THE FENCE, AND THE ARGUMENT FOR ITS NUMBER

`emit.rs::feldstatisch`, in front of the loop and not around it:

```rust
let text = w.to_string();
let bytes = (n as u128).saturating_mul(text.len() as u128 + 2);
if bytes > C_INITIALISIERER_MAX { weigere(absagen, st.name.span, &format!(...)); return; }
```

`C_INITIALISIERER_MAX = 1 << 20` -- **one mebibyte of initialiser text**, named at module
level beside `C_OBJEKT_MAX` and read at exactly one site.

### Why bytes and not an element count

The mandate offered three fences. Two were checked and fall away:

* **A repeat form.** `{ [0 ... 9] = 7 }` is a GNU extension. Measured with the tree's own
  gate: silent under `-std=c11 -O0 -Wall -Wextra -Werror`, and under one switch more
  `error: ISO C forbids specifying range of elements to initialize [-Werror=pedantic]`.
  That switch is **net 5 of this very tool**, so the road trades a hang for a finding in the
  same instrument. *Checked before promising, as the mandate required.*
* **A loop at run time.** A `static` initialiser has to be a constant expression. Filling the
  array from an init function moves the work to a moment this language does not have -- and
  it changes what `= 7` MEANS, which is the one thing the function's own header was written
  to keep straight.

So it is the third: refuse above a stated output size. **And the size is on BYTES, because
bytes are what does not halt.** A count cannot say it: one element of `7` costs three
characters and one of `-2^127` costs forty-two, a factor of fourteen at the same length. The
speech test holds exactly that -- `[u64; 100000]` passes at `7` and is refused at
`18446744073709551615`, same length, different cost.

`+ 2` is the `, ` between two elements; the last carries none, so the count is two bytes
high and the refusal fires two bytes early rather than two bytes late.

### THE HEADROOM, measured over the corpus and not estimated

612 versioned `.gab`/`.gabi`. **Ten declare an array `static`, and nine of the ten are
`= 0`** -- the tenth is poison probe `662` itself, written today.

| where | declaration | initialiser |
|---|---|---|
| `beispiele/08-bereiche.gab:135` | `static mut kernlast : [Zaehler; 64]` | `= 0` |
| `beispiele/64-writes-a-whole-buffer.gab:66` | `pub static mut PUFFER : [u8; KAP]`, `KAP = 64` | `= 0` |
| `beispiele/gift/03`, `/18`, `/20` | `[u32; 64]` | `= 0` |
| `beispiele/gift/605:36` | `[u8; KAP]`, `KAP = 8` | `= 0` |
| `beispiele/gift/633:22` | `[u8; KAP]`, `KAP = 64` | `= 0` |
| `beispiele/gift/602:46` | `[u64; 2^128 - 1]` | `= 0`, already refused |
| `beispiele/gift/645:43` | `[u64; PTRDIFF_MAX]` | `= 0`, already refused by `D5` |

**The largest array `static` in a clean program is 64 elements.** Every literal array length
anywhere in the tree, of any kind: `8` (x4), `10`, `32`, `64` (x4), `256`, `512` (x8) -- the
largest is `[Pte; 512]`, a page table's node, and it is not a `static`.

What one mebibyte leaves:

| value written | bytes/element | elements allowed | x the largest array `static` (64) | x the largest array of any kind (512) |
|---|---|---|---|---|
| `7` | 3 | **349 525** | 5 461 | 683 |
| `2^64 - 1` (20 chars) | 22 | 47 662 | 745 | 93 |
| the widest literal Gabbro has (40 chars) | 42 | 24 966 | 390 | 49 |

A full budget costs about **30 ms** at the rate measured in section 3. *A limit a real
program hits is worse than the defect; the nearest real declaration in this tree is between
two and four decimal orders below it -- and it would not reach the branch at all, because it
is `= 0`, which lowers to `{0}` at any length.*

## 7. THE SWEEP IS SILENT AGAIN -- and nothing else moved

Same tool, same 16 threads, same machine, before and after the fence:

```
                                          before      after
-- 1. A THIRD ANSWER                           0          0
-- 8. THE EMITTER DID NOT HALT                 2          0
   NOT BOOKED                                  1          0
accepted cases that kept the promise    3423/3514  3423/3514
shapes 1-4                                    91         91
```

The **whole** diff between the pre-repair sweep at `26620f1` and the post-repair sweep is
the new net's own lines -- the speech-test count, the five generated cases, net 8's heading,
and the coverage line. **Not one of the 3514 accepted cases changed its answer.**

```
< -- 8. ... : 2        array-nichtnull  `100000000`            no answer within the deadline
<                      array-nichtnull  `1152921504606846975`  PANICKED: capacity overflow
> -- 8. ... : 0
```

And the net's denominator is not five: **2380 checker-refused cases were driven through the
emitter under the 3 s deadline, and every one of them halted.**

## 8. WHAT IS LEFT, AND WHAT IS NOT MINE

* **`zaehle-gifttreffer.py` stays RED, on purpose.** Probe `662` cannot be written without
  `M140` falling beside `C001` -- measured, section 2 -- so it is the eighth untrennable
  pair and it is written into `messung/GIFT-GEGEN-ZUSAGE.md` §10 with its reason. The mark
  went `7 -> 8`, **by exactly one**. Measured with the probe removed, the count is 8 and not
  7: probe `411` (`N046@17 · M134@24`) was over the mark before this lane began and is not
  in §10. *Raising to 9 would have swallowed it -- a mark lifted past somebody else's
  finding does not record a repair, it deletes a report.*
* **The emitter runs before the verdict is read** (`command_emit`, section 3). The fence
  makes that harmless for this slot, but the ordering itself is untouched: it is another
  file, another lane's territory, and the note above it says the ordering is deliberate.
  **Net 8 now watches it** -- 2380 cases a run.
* **11 stale bookings in `fuzze-erzeuger.py`** (`BOOKED AND GONE`), all from the `D1`-`D6`
  repairs in `26620f1`. They were standing before this lane and are untouched; the sweep
  exits 1 because of them, at the baseline and after.
* **The merge against `master` `4e53df3` is CLEAN, and that is measured and not hoped.**
  `git merge-tree --write-tree HEAD master` exits 0 with a tree and no conflict block. The
  two change sets do not overlap at all: `master` moved `TODO.md`,
  `dokumente/GABBROV.md`, `messung/GABBROV-V1.md` and `programmlogik/gabbrov/V1.lean`; this
  lane moved `emit.rs`, `tests/rechenwerk.rs`, two instruments, the probe and three
  documents. **No region of `emit.rs` needs hand-merging** -- the `D1`-`D6` repairs that
  touched it heavily are `599ca75`/`26620f1`, which is this lane's BASE and not something
  it has to catch up with.
