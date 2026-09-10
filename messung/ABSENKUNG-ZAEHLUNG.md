# Lowering count — the search path behind the `Absenkung` constant

Measured: nothing in this file. This file books the procedure that would
replace the standing constant with a measured number, the context that makes
the procedure load-bearing, and the compiler distinction that bounds what any
such number can buy. Every figure below stands inside a plain code block next
to the command that prints it. No figure here was taken on trust, and no
figure here was produced by a build.

## 1. The constant and what it lacks

`grammatik/Grammatik/Ziel.lean` carries the lowering assumption as a structure
with a bound, plus a constant that fills it:

```
proPrimitiv : Nat
begrenzt : proPrimitiv <= 8
def absenkung : Absenkung := ⟨4, by decide⟩
```

The comment at the constant says it directly: the value stands there because
the sentence needs a number, not because anyone ever held each Gabbro
primitive against `emit.rs`. That is finding W7, a number without a search
path, and this file is that search path written down before anyone walks it.

The claim the constant would carry is preservation of the `ops` count from C
to Asm by a quantitative CompCert. Section 4 below says why that carrier is
narrower than its name suggests.

## 2. The counting procedure

For each Gabbro primitive, count the C statements the emitter produces for
exactly that primitive, and take the maximum. The maximum fills
`proPrimitiv`; the bound beside it stays as the check that the measured
maximum fits.

```
for each Gabbro primitive P:
  write a minimal unit exercising exactly P
  run: gabbro emit unit_P.gab
  count the C statements in the output
proPrimitiv = maximum over all P
```

Concretely, per primitive:

```
./target/debug/gabbro emit unit_P.gab > out_P.c
grep -c ';' out_P.c
```

The statement count is per primitive, not per program: a unit exercising two
primitives measures neither. Shared headers and the file scaffold
(`#include`, the boilerplate around the body) do not count toward any
primitive; they are constant across units and cancel out of the maximum only
if every unit carries the same scaffold, so every unit must carry the same
scaffold.

Two readings the procedure must keep apart, because the folder already
confused a near neighbour once (`BEWEIS.md` section 1a: `grep` finds `for`
far more often than a statement `for` occurs — a lexer counts statements, a
text search does not):

```
lexer statement count per primitive  = the number that fills proPrimitiv
grep occurrence count in emit.rs     = orientation only, never the result
```

Read-only orientation over the emitter, taken without any build:

```
grep -c "_Atomic" crates/gabbro-check/src/emit.rs
```

```
7
```

```
grep -c "volatile" crates/gabbro-check/src/emit.rs
```

```
48
```

```
grep -c "__asm__" crates/gabbro-check/src/emit.rs
```

```
8
```

```
wc -l crates/gabbro-check/src/emit.rs
```

```
11708
```

These are occurrences in the emitter source, not statements in emitted C.
They are booked here so that the future run has a baseline to differ
against, and for no other purpose.

The run itself is one pass over all primitives with no early stop: a count
that aborts at the first maximum measures whether at least one primitive is
large, not which primitives are large. The maximum is taken after the last
primitive, not at the first one that exceeds the standing constant.

Acceptance for replacing the constant:

- every Gabbro primitive has a minimal unit, and every unit emits;
- the statement count per unit was produced by the same lexer with the same
  scaffold rule;
- the maximum with its per-primitive table lands in this file next to the
  commands above;
- only then does the constant change, with the commit naming this file.

## 3. Why the count matters now — `H = 1` context

`messung/ABSENKUNG.md` section 1.1 books the lowering obligation count. The
snapshot and its three updates read, in order:

```
H = 5, measured 2026-08-28
H = 4, since 2026-08-31, F6 pierced
H = 3, since 2026-09-03, F9 pierced
H = 2, same day, F1 pierced
H = 1, same day, F5 pierced
```

F5 was pierced by `lauf "fragment5"`, thirteen numbers and one trace covering
the full service distribution. Measured fragments are:

```
F1 F2 F4 F5 F6 F7 F8 F9 F10
```

The one fragment still open is:

```
F3
```

What remains of `H` is one line per fragment with the same content: the
generated C computes what the fragment says, measured at execution. The
procedure in section 2 above is the static counterpart of that line: how many
C statements each primitive can cost at most. Neither replaces the other —
the execution line says the output is right, the count says the output is
bounded.

## 4. What the number cannot buy — CerCo is not the production compiler

The quantitative CompCert the `Absenkung` structure names is CerCo, not the
production compiler. The production promise is sequential and race-free, and
it covers neither inline assembler nor C11 atomics. Our own emitted product
contains all three, counted in the emission census booked in
`dokumente/PLAN-HARDWARE.md`:

```
__attribute__   696      volatile      120      restrict      260
_Atomic          39      _Noreturn      20      __asm__         2
__builtin_unreachable 5  _Static_assert  1
```

The three forms outside the production fragment, with their counts:

```
_Atomic   39
volatile  120
__asm__   2
```

For a multicore kernel with DMA, CompCert is therefore no line one can
substitute: the cheaper reading of the constant (the compiler preserves the
count) already assumes away concurrency, devices, and exactly the three
forms above. A measured `proPrimitiv` bounds the emitter side of the
contract; the preservation side still needs a carrier that accepts the whole
emitted language, and the production compiler is not that carrier. That
distinction is booked at the constant itself in `Ziel.lean` and repeated here
so the future measurement cannot silently drop it.

## 5. What was expressly not done here

- No minimal unit was written and no count was run; `proPrimitiv` still
  stands on the old value.
- No build was started and no binary was produced; all commands above are
  read-only text searches.
- No sentence in `SPRACHE.md`, no fragment file, and no Lean source was
  changed.
- The open fragment F3 was not touched; `H` still stands where
  `messung/ABSENKUNG.md` books it.

Evidence beside the orientation figures: `grep -c` over
`crates/gabbro-check/src/emit.rs`. The census figures are cited from
`dokumente/PLAN-HARDWARE.md`, not re-measured here.
