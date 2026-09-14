# MUSE-REPORT-172 — T3: the round-trip main induction, one level at a time

Lane 172, branch `muse/172`. Task: prove the print-parse round trip
`parse_druck` in a NEW file `Parser/Rundlauf2.lean` (importing
`Rundlauf.lean`), starting from a sub-grammar predicate and widening
level by level, each extension a green commit; two witnesses on
corpus expressions; stop at the widest green predicate with exact
blockers if a level resists. No codes, gifts or examples reserved
(none used).

## Status: round trip proved for a widened kernel predicate; main induction green

`./lean-bau` last lines:

```
✔ [174/175] Built Grammatik (207ms)
Build completed successfully (175 jobs).
```

(`./lean-probe` on `Rundlauf2.lean`: exit 0, 0 errors; only
pre-existing-class linter warnings — unused simp args,
unreferenced binders — same class as lane 161's.) No Rust touched
(`./cargo-pruef` not applicable). `Ausdruck.lean` NOT edited.
`Rundlauf.lean` edited twice, both measured and documented below
(`brennstoff` growth, one header comment). `Grammatik.lean` gains
one import line. No `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe` anywhere (grepped); every theorem premise is used.

## What was built (all in `grammatik/Grammatik/Parser/Rundlauf2.lean`, 3149 lines, 107 theorems)

Step A (one precedence level, strong size induction — lane 161's
trap avoided by never aiming at all constructors at once):

- `gutKern` (literals, variables, unary `!`, parenthesised `+`),
  `gutKern_un`/`gutKern_bin` `rfl`-equations, `gut_of_gutKern`
  bridge, `RKern n` (lane 161's `R n` restricted to `gutKern`,
  with `parseUnary`/`parsePrimary` taking NO `ruhig` premise)
  plus `BKern n` (binary-inner parse for `+`, general tail).
- `kern_prim_var`, five atom towers (`turm_lit/gleit/wahr/
  falsch/var`) sharing `tower_up`, arm lemmas `bang_arm`/
  `paren_arm`/`un_paren_fall` with WHOLE-SUBTERM middles/tails,
  `kern_un_turm` split in two (the primary leg is provable only
  for atoms), `kern_bin_turm`, `kernB_step` (the `+` inner
  trace), per-level step lemmas, `kernRB` (joint induction),
  `parse_druck_kern`, witnesses in instance form plus
  kernel-computed `match` form (`decide` on `Except`-equality
  fails: no `DecidableEq SExpr`).

Step B (each a green commit, predicate widened in place):

- B1: full unary level (`-`, `~` alongside `!`;
  `bang_arm_gen`, both un-towers and `turm_un` take the
  spelling lawfulness through; callers pass `hop` untouched).
- B2: second binary level (`*`; `BKernStar`, Mul-level consume
  trace, spelling-blind tower duplicates).
- B3: places/suffixes (`gutKernPlatz`, `suffGutKern`,
  `zerlege_kern`, `kern_suff_rund`, `kern_prim_platz`,
  `turm_platz` split into weak/full for the `ruhig`-free
  components).
- B4: loop level `||` (`BKernOr`, `tower_up_orbar`, OrL-consume
  trace, towers).
- B5: loop level `&&` (`BKernAnd`, `tower_up_andbar`,
  AndL-consume trace with outer OrL stop, towers).

Widest green predicate:

```
gutKern = lit/gleit/wahr/falsch, variable (non-reserved),
  un {!,-,~}, bin {+,*,||,&&},
  feld/index/pfeil over gutKernPlatz (variable-based places,
  index payloads gutKern)
```

`parse_druck_kern : ∀ (e : SExpr), gutKern e = true →
parseOr (brennstoff e) (druckToks e ++ [.ende]) = .ok (e, [.ende])`
is proved (via the `Or` leg of `kernRB` at `groesse e`).
Sixteen witnesses: eight corpus expressions
(lit, `+`, unary `-`, `*`, `||`, `&&`, field, index) each as a
`parse_druck_kern` instance and a kernel-computed `match` check.

## Open (in priority order — each with the exact blocker)

Full `gut` (lane 161's predicate) and hence `parse_druck` are
NOT proved. Per remaining constructor, what blocks and why:

- `&&`-rest: none — done this lane. `||`/`&&` close the loop
  levels; `+`/`-`-family vs `*`-family close two flat levels.
- `cmp` (`==`,`!=`,`<=`,`>=`,`<`,`>`): needs `BKernCmp`
  (single-shot consume at `parseCmp`: `parseBit` left operand
  through weak legs, `opVgl` hit, `parseBit` right operand,
  outer loops stop at `)`). Same shape as done levels, no new
  ideas — ~150 lines, not started for turn budget, not
  resistance.
- `bit` (`&`,`|`,`^`,`<<`,`>>`,`<<%`): needs `BKernBit`
  (flat-loop consume at `parseBitL`, exactly the `+` shape
  one level up). Mechanical.
- `add`-rest (`-`,`+%`,`-%`,`+|`), `mul`-rest (`/`,`%`,`*%`):
  same `parseAddL`/`parseMulL` loops as `+`/`*` — one B-trace
  duplicate plus op-table facts per spelling. Note unary `-`
  vs binary `-` share a token with no conflict: the printer
  parenthesises every non-atom, verified by the neg witness.
- `ruf` with argument lists: needs a `parseArgs` round trip.
  Lane 161's `args_rund` needs full `R n`; an `RKern`
  adaptation additionally needs `keinDP`/`toksKernKopf`
  analogues (the `parseArg` label-strip fires on `name :`,
  so printed kernel argument lists must be shown `:`-free
  and `)`-headed). Estimated ~200 lines. Not started.
- `eingebaut` (`sizeof`/`lenof`/`aligned`): lane 161's
  `prim_eingebaut` RESISTED there (removed, not weakened) and
  was not re-attacked here; `sizeof`/`lenof` additionally
  need `parseOrt`-placed payloads (lane 161's
  `ort_platz_all` adapts to `RKern` in ~30 lines) plus the
  type-word gate.
- `alt` (`old`): same `parseOrt` machinery as above.
- `ergebnis`, `fnwert` (`&`-paths need segment acts),
  `grund` (`G::F` needs segment acts): single-constructor
  primaries, small, not started.
- Statements (task item 4, `SAnw`): untouched — the
  `Anweisung` layer was never entered this lane.

## Findings about the task (rule 12 notice)

1. A uniform `+8` fuel bound cannot thread same-tree level
   descent (`omega` rightly refuses `X + 8 ≤ G'` from
   `X + 8 ≤ G' + 1`). `RKern` staggers per level (`+8` at
   `parseOr` down to `+1` at `parsePrimary`); loop-stop
   strips are fuel-free (`omega` from the bound), descents
   cost one each — `BKern` needs `+10` by count (measured).
2. `brennstoff` as lane 161 left it (`12 * (groesse e + 1)`)
   never fits the `RKern` Or-bound (thirteen fuel per size
   unit needed, twelve given). Grown to
   `12 * (groesse e + 1) + groesse e + 8` in `Rundlauf.lean`
   with the measurement in its doc comment. It occurred in
   no proof, only comments — zero breakage risk, and the
   full build confirms it.
3. `++` association discipline, measured twice: equation
   lemmas fire only on syntactic successors AND matching
   association. Arm lemmas take whole-subterm middles/tails
   (`M`, `R`) so unification never sees association; use
   sites canonicalise both sides with `append_assoc`-only
   simp (confluent) before `exact`. Four strips numeral-fold
   loop fuel to `+ 3`, which no equation fires on — unfold
   once more by explicit rewrite.
4. Core Lean `obtain` with a destructuring pattern clears
   the target hypothesis: after
   `obtain ⟨rOr, …, rPr⟩ := rkn`, later uses of `rkn` fail
   with unknown-identifier while `n`/`bkn` beside it
   resolve (verified by minimal probe: `obtain ⟨a, b⟩ := h`
   then `exact h.1` fails the same way). Workaround in
   `kernUnary_step`: `have rkn' := rkn` before the obtain.
   (Loop steps never destructure, so only the Unary step
   pays this.)
5. Concrete op-table facts (`opMul` on `+`, loop tables on
   `)`, `*`, `||`, `&&`) and benign follows on concrete
   heads all close by kernel `rfl` with variable tails —
   twelve plus eleven plus eight plus seven such one-liners
   this lane, zero failures.
6. Tower proofs are spelling-blind: `druckToks`,
   `paren_arm`, `un_paren_fall`, `tower_up` never inspect
   the operator. Widening a level therefore touches only
   statements, spelling splitters (`un_is_pre`,
   `bin_is_pm`), and step-arm case splits — the proofs
   transfer verbatim. The `*`/`||`/`&&` towers are
   near-duplicates by design, not by accident.

Commits on `muse/172` (22 total, A1 through B5, each green
at commit time); nothing outside `grammatik/` touched; no
network/`cargo`/`ssh` used.
