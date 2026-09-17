# Ruling record: lowering batch of lane-142 (2026-09-11)

Status: ruled. Three forms lowered in `emit.rs`, two refused with price,
two held. Evidence: corpus units in `messung/proben/emission-142/` plus
`cc -O0/-O2` folds; clean-corpus output byte-identical except the owned
lowerings. No BEWEIS.md edit; table flips cite this file.

## Lowered (admitted by implementation)

- `schleifeStmt`: retry header only; `while (!(c))` becomes `for (; !(c); )`
  with identical codegen (15/15, 16/16 insns). No user path writes it.
- `schrittStmt`: `++` becomes `+= 1` in accumulates merge, retry counter,
  slots-of/elems-of headers and walk descent (identical codegen 21/21,
  14/14). The exchange CAS `++` is a sibling-owned arm, untouched.
- `typOfErw`: `bezugnahme` spells the signature from the same lowering as
  the definition; undeclared targets stay a comment under `N006`.

## Refused with price

- `zeigerArithmetik`: pointer-typed `+`/`-`/`+=`/`-=` refused (C001);
  integers cannot match the `*`-suffix check. Price: per-site in-bounds
  duty; UB row owed for the out-of-bounds case. Static scan over 662
  corpus units finds zero triggers.
- `doubleTyp`: mixed float/double arithmetic nodes refused (C001); 7400
  of 200000 sampled cases differ between widths. Same-width, comparisons,
  literals and F005 cases untouched.

## Held (no ruling)

- `cSizeof`: user paths already C001; bounds text-pinned; `_Static_assert`
  has no alternative spelling.
- `cInclude`: all four preamble lines load-bearing (drop-one-include runs);
  refusal would red the gift corpus.
