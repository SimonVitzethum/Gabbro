# MUSE-REPORT-161 — T3: printer and round trip by induction (expressions)

Lane 161, branch `muse/161`. Task: prove the parse/print round trip by
induction in a new file `grammatik/Grammatik/Parser/Rundlauf.lean`:
(1) `beqSExpr` soundness; (2) token printer `druckToks`; (3) `parse_druck`
by induction with a fuel bound; (4) statements if (3) is done; witnesses
on corpus expressions. No codes, gifts or examples reserved (none used).

## Status: infrastructure plus single-constructor primaries green; main induction open

`./lean-bau` last lines:

```
✔ [147/148] Built Grammatik (186ms)
Build completed successfully (148 jobs).
```

(`./lean-probe` on `Rundlauf.lean`: exit 0, 0 errors; only pre-existing
linter warnings about `eP`/`Rn` binders, which are false positives —
both are referenced.) No Rust touched (`./cargo-pruef` not applicable).
`Ausdruck.lean` was NOT edited. No `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe` anywhere; every theorem premise is used.

## What was built (all in `grammatik/Grammatik/Parser/Rundlauf.lean`)

Part 1 — structural equality soundness:
`strKlingt`, `strEq_eq`, mutual `beqSExpr_klingt` + `beqSExprList_klingt`
(`beqSExpr a b = true → a = b`, by cases over both trees with explicit
induction hypotheses — `simp only` cannot apply a bare implication as a
rewrite, measured), `beqTop_klingt`.

Part 2 — printer, measures, printability, benign follows:
`groesse`/`groesseListe`, `brennstoff e = 12 * (groesse e + 1)`,
`druckToks`/`druckToksListe` (fully parenthesised; every binary operator
inside its own parens; names/`ruf` heads/`Grund` segments/`fnwert` paths
as `ident`, so even `Some`/`None`/`old`/`result` as call heads parse back
as calls — no string-printer `None` special case needed at token level;
`sizeof`/`lenof`/`aligned`/`old`/`result`/`true`/`false` as `wort`),
operator groups `istCmpOp`/`istBitOp`/`istAddOp`/`istMulOp` (shared by
`gutOpCmp`/`gutOpBit`/`gutOpAdd`/`gutOpMul` aliases and `istSchleifenOp`),
`gutOpUn`/`gutOpOr`/`gutOpAnd`/`gutOpBin`, `gut`/`gutPlatz`/`gutListe`,
`ruhig`/`ruhigSuff`/`istSchleifenOp`, helpers `strNe_of`,
`nichtWahr_falsch`, stop lemmas `stopOder`/`stopUnd`/`stopVgl`/`stopBit`/
`stopAdd`/`stopMul` (every operator table misses a benign follow, by
`split`+injection for multi-arm tables) and `stopSuffix`.

Foundations for the induction: `unFrei`, `groesse_pos`, `toksLang`
(printed tokens non-empty), `groesse_mem_le`, `gutListe_mem`,
`gut_of_gutPlatz`, `gutListe_Kopf`/`gutListe_Schwanz`,
`args_einzeln`/`args_cons` (`rfl` unfolding equations),
`keinDP_list` + `keinDP_tree` (no `:` in printed `gut` trees, joint size
induction; `eingebaut` by `decEq` cascade + `rfl` shape equations
`gut_sizeof_one`/`gut_sizeof_multi`/`gut_lenof_one`/`gut_lenof_multi`/
`gut_aligned_one`/`gut_aligned_two`/`gut_aligned_multi`), `toksKopf`
(printed heads are never `)`, by size induction).

Induction invariant and place machinery: `R n` (8-component conjunction:
`parseOr/And/Cmp/Bit/Add/Mul/Unary` exact on benign follows with fuel
`12 * (groesse e + 1) + groesse e + 8`, `parsePrimary` with `+1`),
`B n` (binary-inner parse, no follow premise),
`SuffFrag`/`suffToks`/`applySuff`/`suffGroesse`/`suffGut` (+
`groesse_applySuff`, `applySuff_append`, `suffGroesse_append`,
`suffGut_append`), `zerlege` (every `gutPlatz` tree is head variable +
fragments, by size induction), `suff_rund` (chains through
`parseSuffixe`, fuel with fragment-count slack), `druckToks_applySuff`,
`ort_platz_all` (places through `parseOrt`), `sammleSeg_stop`/
`sammleSeg_suffToks`/`suffToks_nopar`/`ruhigSuff_nopar`,
`arg_einzeln` (one `parseArg`: label strip misses), `args_rund`
(argument lists, paren consumed), and single-constructor outcomes
`prim_lit/gleit/wahr/falsch/ergebnis/grund`, `prim_platz`,
`prim_ruf` (via `kopf_ruf_head`), `prim_alt`, plus `ruhigGleit`
(rounded-follow) and `istTypWortVar` (`sizeof`/`lenof` refuse bare
type-word variables).

## Open (in priority order)

`prim_eingebaut` (REMOVED as resisting — see finding 5),
`prim_bin`, `un_X_all` (`fnwert` + `un` + delegation), `B_one` (six
operator levels), `rundlauf_n` (`R n ∧ B n` assembly), `parse_druck`
itself:

```lean
theorem parse_druck : ∀ (e : SExpr), gut e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) = .ok (e, [.ende])
```

(`parseTop` takes no fuel argument, so the fuel-explicit `parseOr`
form with `brennstoff e = 12 * (groesse e + 1)`; `.ok e` is
`Except.ok`, hence the pair form.) Plus its `_zeuge` companion and two
witnesses on corpus expressions (e.g. sonde shapes), task item (4)
(statements `SAnw`), and completing `CUTS:`/`#print axioms`.

## Findings about the task (rule 12 notice)

1. `parse_druck` "for every `e`" is false as stated and will be proved
   with a `gut` (printability) premise in a theorem named `parse_druck`,
   with the deviation documented here: counterexamples are reserved head
   words (`variable "if"` is refused), unknown operator spellings
   (`bin "??"` matches no level), `sizeof`/`old` over non-places
   (`parseOrt` positions), `Some` with ≠ 1 argument, `Grund` with
   integer/sugared-width/`Self` head (`u64::max` parses as a field —
   confirmed by sonde06), and suffixes on non-place bases (`f(x).g`
   never parses). Each is unavoidable against the fixed parser.
2. `parseTop` takes no fuel argument (`parseTop toks`), so the theorem
   is stated via `parseOr (brennstoff e) (druckToks e ++ [.ende]) =
   .ok (e, [.ende])` — an elaboration detail, not a weakening.
3. `++` is left-associative: every membership chase runs tail-first.
   `simp only` cannot rewrite with a bare implication, apply `rfl`
   inside `first | (...)` parens across newlines, or reduce matches
   that `rfl`/`unfold` handle — all measured this lane and worked around
   (`unfold`+`rfl` helpers, `split`+injection, `rw` with iff lemmas,
   `decide` only on closed goals).
4. `!x = true` parses as `!(x = true)` (`!` binds looser than `=`;
   measured) — parenthesise Boolean negations in statements.
5. `prim_eingebaut` resists and was removed (not weakened): beyond the
   `decEq` head cascade and `rfl` shape equations (all green), its
   `sizeof`/`lenof` singleton arms need a variable-check match
   (`parseEingebaut` refuses bare type-word variables) whose
   rewrite/split handling never stabilised across patch cycles, and
   `aligned` needs two `R`-level rewrites whose associativity never
   aligned. The `gut` typWort gate (`istTypWortVar`), the
   `eingebaut_ein_ok` helper, and all `sizeof`/`lenof`/`aligned`
   infrastructure stay green in the file for the next attempt.

Commits on `muse/161` (parts 1–14); nothing outside `grammatik/` touched;
no network/`cargo`/`ssh` used.
