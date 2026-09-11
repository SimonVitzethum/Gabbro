# CForm ruling: compound assignment (`+=` / `|=` / `-=`)

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C3, `zusammZuweisung`, 24 sites (`dokumente/BEWEIS.md` Subject 2
section 1a; `grammatik/Grammatik/Erhaltung.lean`,
`OffeneForm.zusammZuweisung`). This is the last of the four C3 forms, covered
by the generous reading printed beside the count ("assignment"). With this
note the generously-covered class carries zero open doors; the siblings are
ruled in `messung/CFORM-REGEL-PFEIL.md`, `messung/CFORM-REGEL-BOOL.md`, and
`messung/CFORM-REGEL-BOOLLIT.md`.

## 1. Emitter site

Compound assignment in emitted C comes out of one lowering in
`crates/gabbro-check/src/emit.rs`, the merge-operation arm:

| emitter line | function | shape written |
|---|---|---|
| 2093 | merge lowering | `z += v;` for `MergeOp::Add` |
| 2094 | merge lowering | `z |= v;` for `MergeOp::Or` |
| 2095 | merge lowering | `z |= v;` for `MergeOp::And` (flag form, second element `true`) |
| 2092 | merge lowering | `z = (z > v) ? z : v;` for `MergeOp::Min`, the refused `?:` neighbor, not this ruling |

Every other `+=` hit in the file (lines 4400, 4450, 4519, 4670, 5793) is a
Rust-level accumulation of the emitter itself, not emitted text. So all 24
census sites come out of the three merge lines: the accumulator updates of
the generated folds, each a faithful rendering of a Gabbro merge, never an
invented idiom. The `-=` sites counted by the census lexer are the same class
in units whose merge direction the lexer groups with this row.

Count: 24 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), out of the three merge-lowering lines
above.

## 2. Compiler fold

Two shapes of the same accumulation, `cc (GCC) 16.2.1` on x86-64,
instruction counts from `objdump -d --disassemble=<fn>` per function:

```c
int add_comp(int z, int v) { z += v; return z; }
int add_plain(int z, int v) { z = z + v; return z; }
```

| flags | compound form | plain desugar |
|---|---|---|
| -O0 | 9 | 9, same mnemonic sequence |
| -O2 | 2 | 2, same mnemonic sequence |
| -Os | 2 | 2, same mnemonic sequence |

Reading: the two shapes are the same program at every level. A refusal that
expanded `z += v;` into `z = z + v;` would buy nothing at any level because
there is nothing to buy: the compiler already sees one form.

## 3. Semantic price

Admitting compound assignment pins two facts into the target language, and
the note names both because the admission is the ruling:

1. Single evaluation of the left-hand side. `z += v` evaluates `z` once, so
   an LHS with a read side effect (for example a volatile device read) fires
   once, not twice. Here every LHS is the plain accumulator `z`, so the
   distinction is discharged by construction; any future LHS with a side
   effect must not lean on a double evaluation the form never promised.
2. Arithmetic of the underlying type. `+=` on the accumulator is the declared
   addition with its rules (wrapping for the unsigned folds, the
   single-overflow refusal for the signed ones); `|=` is the bitwise-or with
   no overflow class at all. The UB of an operand (for example a signed
   overflow inside `v`) belongs to that operand's row, not to this form's.

UB inventory: compound assignment contributes no UB class of its own. There
is no out-of-bounds, no unsequenced access, and no new overflow beyond the
operation the plain spelling would carry. There is nothing here that can
devalue a proof through C's rules beyond what the `+=` operand rows already
say, so no inventory row is owed.

## 4. Verdict: admit with price

`+=` / `|=` / `-=` go on the list under the generous reading of assignment
with the two prices of section 3: single LHS evaluation, arithmetic of the
underlying type, no new UB. Refusal was considered and rejected: the only
rewriting-style refusal (`z += v;` into `z = z + v;`) is definitionally the
same update (section 2 measures it identical at -O0, -O2, and -Os), and it
would touch the one merge lowering that all three accumulator shapes share to
no effect, which fails the trivially-safe bar for an emitter change.

No emitter change was made, so no `cargo test` and no corpus-unit recompile
belong to this ruling; the verification is the fold table of section 2,
measured 2026-09-11 with `cc -O0/-O2/-Os -c` plus per-function `objdump -d`
counts on the two shapes above.

Effect on the census on admission: C3 loses the compound-assignment row, and
the generously-covered class carries zero open doors. Together with the three
sibling notes, step 3 of the work-off order
(`messung/CFORM-ABARBEITUNG.md` section 2) is fully ruled at the note level.
