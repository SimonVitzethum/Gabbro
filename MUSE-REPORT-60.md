# MUSE-REPORT-60 -- `uN` / `iN` sugar (PLAN-BITS.md §1)

Rust lane (parser + checker), plus `SYNTAX.md`. No Lean work: the plan needs no new
core notion (`Ty.int lo hi`).

## What was built

`u13` is sugar for `u16 in 0 .. 8191`; `i37` for `i64 in -2^36 .. 2^36 - 1`.
Storage is the next standard width (8/16/32/64); widths run 1..64. The eight
standard words keep their full-width meaning exactly. The emitted C uses the
storage width, never `_BitInt`.

- Lexer unchanged (closed vocabulary, rule 14): `u13` still lexes as one
  identifier. The type rules read it: `intty`, `slottype` (same `wrapping`
  branch), `typeexpr_innen` (arm directly below the eight words, above the
  name arm), `primary` conversion/call arm, `pfad` first-segment arm (G5).
- `parse.rs`: `zuckerbreite` (shape check + 1..64 refusal text), `zucker_intty`
  (desugar to storage `Kw` + literal `Bereich` nodes over the sugar span),
  `zucker_speicher` / `zucker_bereich` (public: storage word / exact range).
- `ast.rs`: `IntTy.zucker: Option<ZuckerBreite>` (`Some` iff sugar-spelled; then
  `wort` is the storage word and `bereich` the exact range), plus `ZuckerBreite`.
- `SYNTAX.md`: `intty` gains `uint | int` alternatives (`nonzero`, 1..64), the
  «SG-1» note records storage/range/refusal/no-`_BitInt`/13-bit field, and
  `pathseg` admits `uint | int` (`u13::max` parses). Terminal/table counts
  unchanged (221/221); no new vocabulary word.
- Checker: `m1.rs` conversion arm (`u13(a)` -> storage word's range),
  `u13::max`/`::min` answer the sugar's exact bound in the storage width
  (constant folder, M1 expression, emitter literal), `M138` extended to the
  sugar spelling (`u13::gross`). `aufrufgraph.rs`: `zucker_umschreiben`
  rewrites the sugar callee to the storage word at both collectors, beside a
  comment that the conversion node list is read off the checker, not repeated.
  `kosten.rs` conversion arm accepts the rewritten name (1 op). `umgebung.rs`
  documents that `breite_von` only ever sees the eight storage words.
- `slottype` sugar and `regdecl` sugar verified by hand (`u13 wrapping` slot,
  `reg R : u13`, `format` bit group `u13 @[12:0]` all check clean); table slot
  fields lower to the storage C type (`uint16_t`), which is the existing
  lowering -- no `_BitInt` anywhere.
- `instrumente/miss-grammatikdeckung.py`: four `intty.u1/u13/i37/u64` probes
  against the `typ` host (storage moves the C, range moves the checks).

## Probes

- `beispiele/72-sugar-widths.gab`: positive (`u1`, `u13`, `i37`, `u64` checks
  clean, emits `uint8_t`/`uint16_t`/`int64_t`, `u13::max` -> `8191u`,
  `u13(a)` -> `(uint16_t)(a)`).
- `beispiele/gift/796-sugar-width-zero-falls.gab` (`P008`, `u0`),
  `797-sugar-width-above-range-falls.gab` (`P008`, `u65`),
  `798-sugar-range-bites.gab` (`M101`, `return 8192` at `-> u13`).
- `crates/gabbro-syntax/tests/sprechprobe.rs::zuckerbreiten_tragen_bereich_und_speicher`
  (positive + `u0`/`u65`/`i0`/`i65` + `u13 in ...` second-range refusal).
- `crates/gabbro-check/tests/rechenwerk.rs::zuckerbreiten_tragen_speicher_bereich_und_schranke`
  (checker range, emitter storage, no `_BitInt`, exact `::max`, conversion cast).

## Results

- `./cargo-pruef`: `== exit 0; failing tests: 0`.
- `./emission-pruef`: red, but NOT by this lane: `beispiel19` step 8
  (poisoned-C speech probe) reports UEBERSEHEN and the run cuts there with
  exit 2. Reproduced on the stashed (pre-lane) tree: same cut at the same test.
  Cause, measured: the emitted loop spells the increment `i += 1`, and the
  stage's poison `sed 's/; i++)/; i += 2)/'` no longer matches, so poisoned and
  clean C compute the same result. Pre-existing, unrelated to sugar
  (no sugar spelling occurs in `beispiele/19` or its driver).
- Stage-9 equivalent for the four new files, run by hand
  (`.tmp/lane60-stufe9.py`): `72` emits and its C passes `cc -Werror` at `-O0`
  and `-O2` with zero `_BitInt`; the three gifts refuse at the checker
  (`P008`/`P008`/`M101`) so no C is owed.
- `pruefe-wortschatz.py`: green, 221/221, both speech directions ok.
  `leite-grammatik.py --zahl`: 109 rules, 325 forms (was 324: the new
  `primary` sugar arm), speech test ok.

## Guardian audit (rule 14, patterns before the document)

New syntax touches: EBNF terminals `uint/int/nonzero` (covered by the
`221 EBNF-Terminale` count, not by name), parser `zuckerbreite`/`zucker_intty`
(covered by `leite-grammatik.py` arm counting + speech test -- the count moved
324 -> 325 and the test holds), refusal `P008` (already on the `BENANNT` list
in `korpus.rs` and in `saetze.rs`'s register; `pruefe-vergabe.py` lists the two
new issuance sites under `P008` at similarity 0.26 -- same rule, second and
third.|\n-site, not a new rule). Corpus counts move by construction: +1 clean
(72), +3 poison (796-798); guardians that pin absolute corpus numbers
(`pruefe-todo.py`/`pruefe-zahlen.py` counts, `zaehle-gifttreffer.py` marks
271/8/333, `pruefe-vergabe.py` marks 20/68 -- already broken pre-lane at
21/75) were read but not moved: moving a ratchet is a separate lane's call.

## What remains open / what I believe is wrong

1. `emission-pruef` step 8 at `beispiel19` is a pre-existing red (see above);
   the poison `sed` must match the emitted increment spelling (`i += 1`).
2. Packed table fields: the task asks that `u13` fields "occupy exactly 13
   bits where the table is packed". There is no packed-table feature in the
   tree -- `emit.rs` documents that the producer does deliberately NOT do
   `packed`/`aligned`, and tables lower to one C field per slot field at the
   storage width. What holds instead: bit-exact range (checker), storage-width
   lowering without `_BitInt`, and exact 13-bit occupancy in `format` bit
   groups and device register fields (shift-and-mask readers, verified by
   hand). If "packed table" means a new layout feature, that is a separate
   build, not this sugar.
3. `i37`'s lower literal builds as unary-minus over `2^36`: `auswerten` folds
   it, `grenzzahl` reads it in reset values, `konst_zahl`-only readers do not.
   `u13 in ...` second-range refusal reuses `P008` (see `pruefe-vergabe.py`
   note above); a dedicated code would be cleaner but would add a 40th P-code
   for one sub-case.
4. No Lean changes (nothing to prove: sugar desugars before every pass).
