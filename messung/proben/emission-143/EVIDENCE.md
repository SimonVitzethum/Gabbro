# emission-143: code evidence for offen slots 8-14

Scope: slots 8-14 of the offen rows in `grammatik/Grammatik/Erhaltung.lean`
`tafel`, in tafel order (slots 1-7 belong to the parallel lane):
`cInline`, `cConst`, `deref`, `adressVon`, `bitNicht`, `schrittStmt`, `cSizeof`.

Method: one minimal unit per form in this directory, each emitted with the
base binary (`gabbro emit`, base `6f26e76`, exit 0 for all seven), each
emission compiled with `cc (GCC) 16.2.1` on x86-64 as
`cc -std=c11 -O0/-O2 -Wall -Wextra -Werror -c` (14 of 14 green, 2026-09-11).
No emitter change was made, so every existing emission is byte-identical by
construction; the pin below is the enforcement.

Verdicts: all seven ADMIT, none lowered, none refused.

| unit | pinned shape in the emission | verdict |
|---|---|---|
| `emission-143-cinline.gab` | `static inline` byte-order helpers plus one reader/writer pair per format field | admit, ruled in `messung/CFORM-REGEL-INLINE.md` |
| `emission-143-cconst.gab` | read-only handle `const D *restrict v` on the generated reader | admit, ruled in `messung/CFORM-REGEL-CONST.md` |
| `emission-143-deref.gab` | volatile-cast dereference `(*(volatile u32 *)(v->basis + 0))` in the field reader | admit, ruled in `messung/CFORM-REGEL-DEREF.md` |
| `emission-143-adressvon.gab` | error-channel call `gib_opt(&v, &e)` over `let … else` | admit, ruled in `messung/CFORM-REGEL-ADRESSE.md` |
| `emission-143-bitnicht.gab` | width-bound complement `(u16)~(u16)(x)` | admit, ruled in `messung/CFORM-REGEL-TILDE.md` |
| `emission-143-schritt.gab` | bounded retry counter `_r1++` | admit (unruled; step-4 batch of `messung/CFORM-ABARBEITUNG.md`) |
| `emission-143-csizeof.gab` | traverse bound `sizeof(q->slots) / sizeof(q->slots[0])` | admit (unruled; step-4 batch of `messung/CFORM-ABARBEITUNG.md`) |

Why neither lowering nor refusal, per form:

- `cInline`, `cConst`, `deref`, `adressVon`, `bitNicht`: the merged rulings
  measured the fold (zero instructions at every level) and rejected refusal
  on meaning and scale (device readers, atomics, out-parameters, width-bound
  complements). Re-lowering here would contradict measured work.
- `schrittStmt`: all 42 sites are emitter-internal loop counters
  (`emit.rs` retry counter, traverse headers); Gabbro has no increment
  operator, so a named refusal has no attach point, and rewriting to
  `+= 1` churns every loop for zero semantic difference.
- `cSizeof`: the checker already refuses `sizeof` outside `format`
  predicates by name; the remaining sites carry the declared layout
  (`slots of` bound, `entrust` self-check), which no desugar reproduces
  without re-deriving the layout in the emitter.
