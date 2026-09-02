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
