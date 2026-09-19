# MUSE-REPORT-256 — bounded strings, round 2 (review findings F1–F4)

Lane 256. Branch `muse/256`. `/home/fisch/gabbro-muse/lanes/256.md` read
in full; this is the assigned task, never a self-chosen one. Round 1
(value model + unwired discipline) is superseded below: the type form
parses, three checker codes fire, ten probes pin both directions, and
every accepted shape ends at a measured named refusal.

## F1 — the type form parses; literals stay out with mechanical evidence

- `TypExpr::Zeichenkette { max: u128, span }`
  (`crates/gabbro-syntax/src/ast.rs`) plus the `span` arm. Parse arm in
  `typeexpr_innen` (`crates/gabbro-syntax/src/parse.rs`): `string`
  directly followed by `max` takes it; `string` stays an ordinary name
  everywhere else (no new keyword, zero new words — the `wortschatz`
  test is untouched). A non-number max is `P004`. Parse ownership does
  not block: lane 222 (the only parse owner) is merged.
- Exhaustiveness arms forced by the new variant (compiler-oracle,
  `E0004` × 7): `lib.rs` (two type visitors ignore the form),
  `alias.rs` (`zieltext` renders `string max N`), `namen.rs` (names no
  values), `umgebung.rs` (reads `Typ::Unbekannt` — deliberately no `Typ`
  variant, so the shared passes step aside by the W10 fiat and
  `zeichenfolge.rs` decides).
- Value surface WITHOUT new `ExprArt`/`Eingebaut`/`Typ` variants (all
  three would break exhaustive matches in files this lane must not
  touch): `+` on two strings is concat, `lenof(s)` is length, `s[k]` is
  the index, `==`/`<` compare. All four are m1-silent on `Unbekannt`
  (measured: `binaer` returns `Wahrheit` for comparisons and `Unbekannt`
  for `Plus` without bounds; `Eingebaut` and the index suffix on an
  unknown base are silent).
- The literal gap, as a probe not prose: `"hi"` stays `P011`
  (`beispiele/gift/1127-literal-bleibt-leserfehler.gab`). Mechanical
  cause: a literal needs an `ExprArt` arm and `m1::ausdruck_roh`
  (`crates/gabbro-check/src/m1.rs:2368-3090`) is exhaustive over
  `ExprArt` with no wildcard. String sources are parameters, `extern`
  returns and inferred `let`s. First program through the checker:
  `string max 8` params with `lenof`, 0 errors (measured).
- `emit.rs`: exactly two arms, both forced by exhaustiveness and both
  refusal-shaped — `ruecksetzwert` returns `None` for the form, string
  parameters earn no local-view entry. No lowering logic, no behaviour
  change for any pre-string program (the variant is unconstructible
  from old sources). Wave chain please confirm; revertible in two
  lines, quoted verbatim at the end of this report. Without them the
  workspace does not compile, so "add to `TypExpr`" and "never touch
  `emit.rs`" cannot both hold — the refusal arms are the resolution,
  and the handoff table below is the specification the task asks for.

## F2 — the discipline is wired: N453–N455, sentences, probes, diff

- Pass `zeichenfolge::pass` (`crates/gabbro-check/src/zeichenfolge.rs`),
  wired directly behind `m1::pass` in both pipelines in `lib.rs`. Same
  column as M1, no pass number (kontexte precedent). It tracks declared
  maxes per body (params, annotated and inferred `let`s, `extern`
  returns via a callee map) and fires ONLY on positive string
  knowledge; shadowed names drop out (a miss, never a false fire).
- Stock re-verified before taking, not assumed: highest N in use is
  N452 (N431–N445 still reserved for lanes 242/245/246), so N453–N455;
  highest gift is 1117, so 1118–1127.
  - `N453` (concat past the target max): `1118` (5+5 into 8).
  - `N454` (index not provably in range): `1119` (literal 8 at max 8),
    `1120` (computed index, narrowed yet unproven).
  - `N455` (sort): `1121` (`0` at a string slot), `1122` (`s + 1`
    mixed). Mixed comparisons, string at non-string slot or parameter,
    over-max returns/arguments, and field suffixes on strings share the
    code; each fires exactly once per probe (measured).
  - Sentences: `zeichenfolge.laengen` (N453, N454) and
    `zeichenfolge.plaetze` (N455) in `saetze.rs`, same commit as the
    firing code. `pruefe-saetze.py`: 0 erfunden; `pruefe-kennungen.py`:
    ALL PASS (N now 143).
- Positive probes (checker-clean, emitter-refused): `1123`
  (declaration plus `lenof`), `1124` (5+3 into 8), `1125` (literal
  index below the max), `1126` (`==` and `<` over two strings) — all
  `-- erwartet: C001`, all with 0 checker errors and no C written.
- Corpus verdict diff: `./cargo-pruef` exit 0, zero failures, WITH the
  ten new gifts (the gift loop enforces every `-- erwartet:`). Sweep
  with the built binary: N453–N455 fire NOWHERE outside gifts
  1118–1122 (0 hits over `beispiele/*.gab`, 0 over other gifts), so no
  existing verdict moved and no existing gift changed class. The
  `zaehle-gifttreffer.py` "41 statt 24" is pre-existing drift on master
  (its rows carry other lanes' fresh codes: N322, H022, K003); all ten
  new gifts classify `sauber`.
- `./emission-pruef`: exit 0, counters unmoved (no new emitting file).

## F3 — handoff table, every row measured with the built binary

Committed probe per row (gifts 1123–1127); codes below are measured,
not asserted. Every string value originates at a string-typed
declaration (parameter, `extern` return, annotated or inferred `let`);
all three declaration positions hit existing narrowed `C001` arms, so
no string value reaches C:

| accepted shape | committed probe | measured refusal today |
|---|---|---|
| `string max N` declaration (param) | 1123 | C001 "no lowering: parameter type", no C |
| `string max N` declaration (`extern` return) | $TMPDIR pext (extern needs effects/costs: E001/H021/K003 measured) | C001 "no lowering: return type", no C |
| `string max N` let (annotated and inferred) | 1124 ($TMPDIR pext3 for inferred) | C001 "no lowering: `let` without a resolvable type", no C |
| `lenof(s)` | 1123 | C001 "no lowering: `lenof` over a place whose type is not a fixed-length array …", no C |
| within-max `+` (concat) | 1124 | inside refused units only (its `let` C001s); no C |
| in-range `s[k]` | 1125 | inside refused units only; no C |
| `==` / `<` over two strings | 1126 | inside refused units only; no C |
| string literal `"hi"` | 1127 | P011 "expression expected, string found" (reader; nothing downstream) |
| unbounded `string` (no max) | — (no form) | refused by name, permanently: no constructor without max exists in either model |

The N-poison gifts use plain `-- erwartet:` (checker half only — there
is no C for `cc` to take, so no `allein` counterfactual exists).

## F4 — Lean cosmetics, done

- `z1`/`z2` have one doc line each; the stale second `CUTS:` block is
  gone; one accurate `CUTS:` block remains (value model ahead of the
  surface on literals; lowering owed, with the index obligation named).
  `./lean-probe`: 0 errors. Axioms unchanged (standard subset; the two
  refusal theorems depend on none).

## Definitions and theorems (exact names)

- Lean (`ZeichenfolgeGebunden.lean`, imported in `Grammatik.lean`):
  `BString`, `bliteral`, `blaenge`, `bconcat`, `bindex`, `vergl`,
  `bvergleiche`, `z1`, `z2`, `z3`, `bliteral_laenge`,
  `bconcat_laenge`, `bindex_innen`, `bindex_aussen`, `vergl_refl`,
  `bconcat_ablehnt`, `bliteral_ablehnt`, `bounded_string_zeuge`
  (joint with `refB_erreicht`/`refB_schreibt` on `MB`; planted-defect
  over-max concat fails red).
- Rust (`zeichenfolge.rs` + 1 module line in `lib.rs`): `literal_passt`,
  `concat_passt`, `index_passt` (kept as arithmetic pins with their 6
  unit tests), `pass`, and the rule helpers `synth`, `sammle_lets`,
  `ziel_regel`, `expr_regel`, `ort_regel`, `index_regel`, `ruf_regel`,
  `concat_ablehnung`, `sort_ablehnung`.

## L4 boundary (unchanged)

Type + literal-model + concat + length + index + compare are the
language (delivered as far as the m1 ban allows). Formatting, number
parsing/printing, splitting, find and UTF handling stay L4 library
work per TODO §0b; byte-string containers over tables stay L2/L4.

## Open, in dependency order

1. Literal surface (`"hi"`): needs an `ExprArt` arm plus one arm in
   `m1::ausdruck_roh` — the lane that owns `m1.rs` takes it; the Lean
   model (`bliteral`) and gift 1127 already pin both sides.
2. Lowering lane: exact-length side of the index rule (runtime length
   check or exactness tracking) and the C lowering itself; the C001
   table above is its per-shape checklist.
3. Flow-narrowed indices (`if i < lenof(s)`), call-arity edge cases,
   contracts/`const`/`static`/table-slot string positions: documented
   misses, all end-to-end safe behind `C001` today.

## Build lines

- `./lean-bau`: `Build completed successfully (281 jobs).`
- `./cargo-pruef`: exit 0, zero failing tests (55 result lines ok).
- `./emission-pruef`: exit 0.
- `pruefe-saetze.py`: 0 erfunden. `pruefe-kennungen.py`: ALL PASS.
  `zaehle-gifttreffer.py`: 10 new gifts sauber; 41-verdeckt drift
  pre-existing (see F2).
- `pruefe-englisch.py`: aborts as before (7963 pre-existing German
  comment lines in the checker); my additions are English-only.

## The two emit.rs lines (for the wave chain)

```rust
// ruecksetzwert: joined the refusal list
| TypExpr::Zeichenkette { .. }
// parameter local-view map: joined the no-entry scalars
| TypExpr::Zeichenkette { .. }
```

Full arms with comments in the diff (`git show 9c247a02` range plus
this commit). No example numbers taken. `m1.rs` untouched.
`MARKE_EMIT*` untouched.
