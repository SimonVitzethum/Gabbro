# CForm ruling: logical and/or (`&&` / `||`)

Status: ruled 2026-09-10. Verdict: admit with price. No emitter change.

Census slot: C2, `logUndOder`, 23 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.logUndOder`). This is the
second door of the conditional-evaluation class whose first door (`?:`, 8 sites)
was ruled before: refuse, with the emitter to write `if (v > z) { z = v; }`
for `MergeOp::Max` / `Min` (emitter edit still open at the time of writing).
This note closes the class at the ruling level: every conditional door now has
a verdict.

## 1. Emitter site

Unlike `?:` (one line out of one site), `&&` and `||` come out of six related
lowering lines in `crates/gabbro-check/src/emit.rs`, all of them faithful
renderings of a Gabbro conjunction or disjunction, never an invented idiom:

| emitter line | function | shape written |
|---|---|---|
| 8203, 8204 | `pred_c` | `Und` as `a && b`, `Oder` as `a \|\| b` for `until` conditions |
| 4849-4873 | `pred_c_format` | same pair for format `where` clauses; the `\|\|` arm carries load-bearing parentheses (comment at 4864-4868: `&&` binds tighter than `\|\|`) |
| 10971-10980 | `pred_c_eintrag` | same pair for walk entry predicates |
| 10606-10674 via 10890-10891 | `ausdruck_breit` via `op_text` | `BinOp::Und` as `&&`, `BinOp::Oder` as `\|\|`, parenthesised by `geklammert` (10867-10876) |
| 7097 | range guard | `{o} >= {von} && {o} {oben} {bis}` |
| 11041-11045 | `ausdruck_eintrag` | `BinOp` pair via `op_text` plus `geklammert` |

Two bridges feed the general arm: `pred_als_expr` (10177-10186) turns a
predicate conjunction into `BinOp::Und` / `Oder`, so one Gabbro `and` can reach
C through more than one of the rows above. A form with several sites needs one
row per site because the fix may differ per site; here the fix does not differ
(see section 4), which is itself a finding and is booked there.

Count: 23 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`). One of them is the emitter talking about
itself: the skeleton guard at line 8536 joins its two tests with `&&`.

## 2. Compiler fold

Two shapes of the same check, `cc (GCC) 16.2.1` on x86-64, instruction counts
from `objdump -d` per function:

```c
int gueltig_op(int f_bit, int grund) { return f_bit == 0 || (grund >= 1 && grund <= 12); }
int gueltig_flat(int f_bit, int grund) { if (f_bit == 0) return 1; if (grund < 1) return 0; if (grund > 12) return 0; return 1; }
```

The `op` shape is the emitter's own idiom (comment at 4858:
`grund : u64 @[39:32] where f_bit == 0 || (grund >= 1 && grund <= 12)`); the
`flat` shape is what a refusal would have to write instead.

| flags | operator form | flat desugar |
|---|---|---|
| -O0 | 15 | 19 |
| -O2 | 8 | 8, same mnemonic sequence |
| -Os | 8 | 8, same mnemonic sequence |

Reading: at optimisation the two shapes fold to the same instruction sequence,
and at -O0 the operator form is shorter by 4 instructions. Refusal buys
nothing at any level and costs at -O0. This is the opposite side of the `?:`
trade: there the `if` replacement cost nothing at any level, which is what
made refusal cheap.

## 3. Semantic price

Admitting `&&` / `||` pins three things into the target language, and the note
names all three because the admission is the ruling:

1. Conditional evaluation with a sequence point. The right operand evaluates
   only if the left one does not decide, left to right, with a sequence point
   between. This is the same door as `?:`, now named rather than refused.
   Consequence for readers: a right operand with a read side effect (for
   example a volatile device read) may not happen. Any consumer that needs
   both sides evaluated must not lean on the skipped side.
2. Result value 0 or 1 used as truth. The emitter types every comparison and
   every `Und` / `Oder` node as `bool` (`wert_ctyp`, lines 9407-9421); C still
   computes `int` 0 or 1 underneath. No usual-arithmetic-conversion rule is
   dragged in: unlike `?:`, the two arms never form a common type.
3. Precedence parenthesization as an emitter obligation. `&&` binds tighter
   than `||`, so a bare `Oder` under an `Und` would reassociate silently
   (`a || b && c` parses as `a || (b && c)`). The obligation is already
   discharged in code: the load-bearing parentheses of `pred_c_format` and
   `geklammert` for the expression arms, with `-Wparentheses` as the net
   (nine warnings caught against three missed, per the comment at 10838).

UB inventory: `&&` / `||` contribute no UB class of their own. There is no
out-of-bounds, no overflow, no unsequenced access in the operator itself; the
UB of an operand (for example a signed overflow inside a comparison arm)
belongs to that operand's row, not to this form's. The one new proof-relevant
fact is item 1 above: short-circuit evaluation is now target meaning, and a
proof that reasons about which reads happened must respect it.

## 4. Verdict: admit with price

`&&` / `||` go on the list with the three prices of section 3. Refusal was
considered and rejected on two grounds, one of fit and one of cost:

- Fit: `X_gueltig` functions return the conjunction as a single expression
  (`return ... && ...;`). A statement-level desugar into nested `if`s does not
  fit that position without restructuring every generated validity function.
  Six emission lines would have to change, against one for `?:`.
- Cost: section 2 shows the desugar costs 4 instructions at -O0 and buys
  nothing at -O2 / -Os.

Coherence with the `?:` refusal: the two verdicts differ because the two
prices differ. `?:` was refused because its replacement cost zero everywhere
and its admission would have imported the usual arithmetic conversions into a
table the compiler certified free of implicit conversion. `&&` / `||` cost at
-O0 to refuse, fit nowhere as statements, and import no conversion rule. The
class is now fully ruled: `?:` refused (emitter edit open), `&&` / `||`
admitted here. No door is left undecided.

No emitter change was made: admission needs none, and refusal is not
trivially safe (six sites, `X_gueltig` single-expression position,
precedence logic). Hence no `cargo test` and no corpus-unit recompile belong
to this ruling; the verification is the fold table of section 2, measured
2026-09-10 with the commands `cc -O0/-O2/-Os -c` plus per-function
`objdump -d` counts on the two shapes above.

Effect on the census on admission: C2 loses the `&&` / `||` row, the C count
falls from 30 to 29 (26 to 25 under the generous reading), and the
conditional-evaluation class carries zero open doors.
