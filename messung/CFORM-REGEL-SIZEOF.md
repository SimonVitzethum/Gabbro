# CForm ruling: `sizeof`

Status: ruled 2026-09-11. Verdict: admit with price. No emitter change.

Census slot: C2, `cSizeof`, 27 sites (`dokumente/BEWEIS.md` Subject 2 section
1a; `grammatik/Grammatik/Erhaltung.lean`, `OffeneForm.cSizeof`). The form is
the step-4 remainder twice over: lane-142 held it with no ruling
(`messung/CFORM-REGEL-SENKUNG-142.md`: user paths already C001, bounds
text-pinned, `_Static_assert` without alternative spelling) and lane-143
admitted it unruled in the step-4 batch (`messung/proben/emission-143/`
`EVIDENCE.md`). This note closes the remainder with the short price the
batch owes.

## 1. Emitter site

`sizeof` reaches C through two generator families, and is refused on a
third path. All three rows were read off the code and the measured corpus:

| path | shape written |
|---|---|
| traverse bounds | `eintrag < (u32)(sizeof(q->slots) / sizeof(q->slots[0]))`, the loop bound lowered from the declared table layout |
| `entrust` self-check | `_Static_assert(sizeof(Gastbild) > 0, ...)` where the handed-over space names a declared type |
| body `sizeof(T)` | refused by name (`C001`: agreement with the checker-computed layout is established nowhere) |

The refusal is the load-bearing half of this ruling: user-written `sizeof`
outside a `format` predicate never reaches C, so the admitted shape is only
ever the layout-carrying one. Pinned by the pair
`messung/proben/emission-15x-c23/c23-sizeof-traverse.gab` (admit) and
`c23-sizeof-refused.gab` (C001).

Count: 27 emitted sites per the 2026-08-31 census
(`instrumente/zaehle-c-formen.py`), two admitted families plus the refused
path.

## 2. Compiler fold

Measured by `messung/zeugen-c2/z10-sizeof.sh`, re-run 2026-09-11 with the
base binary (EMIT leg PASS: `beispiele/04-schleifen.gab` emits the
traverse bound): element count by `sizeof` quotient plus a `sizeof`-driven
fill loop, output `sizeof 8 8 8`, identical at `-O0`/`-O2`/`-Os`. The
admitted probe of this lane compiles under
`cc -std=c11 -Wall -Wextra -Werror -c` at `-O0` and `-O2`. There is no
refusal fold to measure: the refused path has no C, and the admitted shape
has no meaning-preserving desugar that does not re-derive the declared
layout in the emitter.

## 3. Semantic price

Admitting `sizeof` pins one fact into the target language: the
compile-time element count from the declared layout. `sizeof` is a
compile-time constant; its operand is never evaluated and performs no
access, so the bound carries no step and no value the proof must track
beyond the declared type it falls out of.

UB inventory: `sizeof` contributes no UB class of its own. The operand is
unevaluated, so no access it names can fault, overflow, or race. No
inventory row is owed.

## 4. Verdict: admit with price

`sizeof` goes on the list with the price of section 3: layout-derived
compile-time counts only, operands never evaluated. Refusal was considered
and rejected for the two admitted families: the traverse bound has no
spelling that does not re-derive the layout, and the `entrust` assert has
no alternative spelling at all. The body path stays refused by name, and
that refusal is part of this ruling, not beside it.

No emitter change was made, so no `cargo test` and no corpus-unit
recompile belong to this ruling; the verification is the `z10-sizeof`
fold table plus the witness pair of section 1.

Effect on the census on admission: C2 loses the `sizeof` row; the C count
falls by one step and the strict and generous totals fall together, since
no generous reading ever covered this form.
