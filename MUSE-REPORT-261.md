# MUSE-REPORT-261 — Lower bounded strings to C (OFFEN O24)

Lane 261 delivers representation, literals, the max bound and emission for
`string max N`. Every string program that the checker accepts in parameters,
results and `let`s now lowers; the five old `C001`-positive probes became
examples, three new poison probes pin the new refusals, and example 161 runs
under `./emission-pruef`.

## 1. The layout decision (O24, first three rows CLOSED)

- **Representation:** per distinct max `typedef struct { uint32_t len;
  uint8_t data[N]; } gabbro_string_N;` — one length word plus `max` bytes,
  **no NUL terminator** (Gabbro semantics never requires one; storage is
  exactly 4+N bytes). Params, results and locals pass **by value** of their
  exact max type. Same-max copies are plain `=`; widening (smaller to
  larger, always sound per `N455`) goes through generated `static inline
  gabbro_widen_N_M`; `+` through `gabbro_concat_T` at T = the operand-max
  sum (which the checker held against the slot, `N453`); comparisons
  through the two generic `(len, data)` helpers `gabbro_streq` /
  `gabbro_strlt` (no widening). `lenof` is `.len`, the index `.data[k]`
  (the checker proved `k < len`, `N454`).
- **Literals:** `"hi"` parses to `ExprArt::Kette` (UTF-8 bytes, length is
  the byte count). The checker holds the count against the target max
  exactly; an over-long literal falls as `N455` (gift 1213). The slot
  writes a compound literal at its own max. Adjacent texts are NOT joined
  (unlike `claim` prose, «B22»): concatenation is `+`.
- **Upper limit:** `1 ..= 65535` (`N486`, `zeichenfolge.schranke`). Zero
  has no object form (`uint8_t data[0]` is no strict-C11 object); more has
  no stack frame. Held at every declared max, in parameters, results,
  `let` annotations and refused positions alike.
- Empty literals clamp to one spare byte at helper-selection time
  (`ktyp`); the length word governs every read, so it is never observed.

## 2. Rust: exact new/changed items

`crates/gabbro-syntax`: `ExprArt::Kette(Vec<u8>)` (`ast.rs`); one
`Art::Text` arm in the primary reader (`parse.rs`).

`crates/gabbro-check/src/zeichenfolge.rs`: `MAX_OBERGRENZE`,
`max_traegt`, `max_regel`, `ketten_maxima`; `synth` answers a literal's
byte length as its bound (no other synthesis rule changed); `expr_regel`
takes the honest `Kette` arm; N486 hooks in `deklarationen` and
`typ_annotation`; unit tests `max_schranke_traegt_1_bis_65535`,
`max_schranke_verweigert_null_und_ueber`.

`crates/gabbro-check/src/emit.rs`: `ktyp`, `ketten_max` (mirror of the
checker's `synth`), `ketten_byte`, `ketten_text`, `ist_kettenname`,
`kette_wert` (value at own carrier), `kette_zu` (value widened into a
slot), `kette_seite`, `ketten_abschnitt` (typedef + helper section from a
name scan of the lowered declarations and bodies — the `DREH_C`
principle, complete by construction), `let_tyexpr`, `kettenwert`;
`ctyp` lowers `Zeichenkette` and still refuses pointer targets;
`ausdruck_breit` arms for literals, string `+`/comparisons and string
`lenof`; the `ort()` string-index hook; `wert_ctyp` arms for string
index (`uint8_t`), string `lenof` (`uint32_t`) and literals;
string paths in `Let`, `Zuweisung` (plain `=` only, compound refused),
`Return` (new `Austritt::rueck_kette`), `ruf` and `LetSonst` (new
`Signatur::param_typen`); `lokale_lets` infers literal/name/concat maxes;
`verbundlokale`, `eigene_sicht` and the unit-wide collection register
string values in `werte`; the section is spliced at `ketten_marke`;
guards keep atomics, `accumulates` and string pointer targets at today's
refusal. Honest `Kette` arms in: `domaene`, `sperrinv`, `lib`
(`unterausdruecke`, `alle_orte`), `clone` (2), `m1` (`ausdruck_roh` reads
`Unbekannt`, like the type), `lean` (2, `OtherValue`/`None`), `kosten`
(0), `freigabe`, `certstmt`, `corrlean`, `refinement` (2), `namen`,
`enthaelt_bitnicht`, `ausdruck_geraet`, `ausdruck_format`,
`sammle_expr_namen`, `needs_saturation`, `geist_wert`, the `when`
expected-value refusal.

`crates/gabbro-check/src/saetze.rs`: new `zeichenfolge.schranke`
(`N486`); the three old string sentences updated (no more "stops at
`C001`", literals are sources, aggregates still a deliberate cut, moved
file paths).

## 3. Lean: `grammatik/Grammatik/ZeichenfolgeC.lean` (new, imported last in `Grammatik.lean`)

`CString max` (length word + full N-byte buffer, bytes are `Nat < 256`)
with `nimm` (live prefix), `len_in_bytes`, `clen`/`clen_nimm`,
`cindex`/`cindex_innen`/`cindex_aussen` (in range exactly under the
checker's guard), `ckopie`/`ckopie_nimm`, `cconcat`/`cconcat_nimm`,
`cvergleiche`/`cvergleiche_eq`, witnesses `w1`/`w2`/`w3` and
`cstring_zeuge` (concat `"hi"+"!"`, length 3, index 2 = 33, prefix
compares less). Axioms are standard subsets only. CUTS states the two
remaining gaps: no verified UTF-8 Char↔byte bridge, no `CForm` hook.
`ZeichenfolgeGebunden.lean` header + CUTS updated (the "ends at `C001`"
and "no representation" lines were stale); its theorems untouched.

## 4. Corpus verdict diff

- gift → beispiele (checker-silent, now emitting, C compiles under
  `-Werror`): `1123`, `1124`, `1126`, `1159`, and `1127` (renamed
  `1127-literal-bleibt-leserfehler.gab` → `1127-literal-ok.gab`; it pinned
  the old `P011`).
- `gift/1166` STAYS (`-- erwartet: C001`): its doubly-bound names have no
  emitter type — a finding, not an omission (see §6).
- New poison: `1211` (`N486`, max 70000), `1212` (`N486`, max 0), `1213`
  (`N455`, `"hi!"` at max 2). Each bites exactly once (measured).
- New example `161-zeichenkette.gab` + `lauf "beispiel161"`: builds,
  copies (8→16), concatenates (5+3→8), lengths, guarded indexes,
  `==`/`<`; expected `2 104 105 2 3 104 105 33 1 0 1 0`.
- Taken from the reserved block: code `N486`, gifts 1211–1213, example
  161. Still free: `N487`–`N490`, gifts 1214–1220.

## 5. Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` —
  `== total: 1328 passed, 0 failed, 1 ignored`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (286 jobs)`).
- `./emission-pruef`: `== exit 1`, and the ONLY finding is the booked
  counter — `FUND: 131 statt 126 emittierende Dateien in beispiele/`.
  Every Differenztest is green including `beispiel161` (emit bit-identical
  twice, `-Werror`, `-O0`/`-O2` equal, UBSan clean, zeugnis exact,
  Sprechprobe falls on the mutated concat); stage 9 compiles **294 von
  294** under both cc (GCC) and clang. MARKE_EMIT untouched per
  instructions. Count arithmetic, verified: stage 9 counts tracked files
  only — 126 + the 5 moved = 131; after this commit lands,
  `beispiele/161` (still untracked here) makes it 132. The merger
  re-measures.
- `pruefe-saetze.py`: Sprechprobe ok; `N486` claimed (55-without-sentence
  mark holds).
- `pruefe-cformen.py`: 0 new uncovered, 0 missing lemmas/assumptions; the
  1 unclassified statement is atomic (`140`, string-free) — pre-existing.
- `pruefe-grammatiktafel.py`, `pruefe-englisch.py`: red, both byte-identical
  on the base tree (stashed and re-run) — pre-existing, unrelated.
- `wortschatz` test caught one real overreach of mine (a `"string"`
  terminal that is not a word): repaired with a contextual `stringkopf`
  rule; suite green since.

## 6. What remains open / what I believe is wrong in the task

- `gift/1166` (sibling-scope string vs number under one name) cannot emit:
  the double-binding rule drops both entries, so `lenof(x)` and the
  unannotated number lets have no type. Scoped emitter views per block
  would fix it — out of scope here; the probe stays honest.
- Unannotated `let x = 5;` (plain numbers) still needs an annotation for
  the emitter — pre-existing, not strings.
- The task's "positive probe" for the bound rule is `beispiele/161`
  (run, not just checked) — stronger than a `C001`-positive gift, and the
  old `C001`-positives could not stay gifts once they emit.
- Refusing `max 0` goes beyond the letter of the task (which only asked
  an upper limit), but a zero buffer has no strict-C11 object form; it is
  probed (1212) and sentenced beside the upper bound.
- Not run: `mutiere-pruefer.py` and the full `abnahme.py` (reviewer
  business; the new refusals each have their biting probe).

Co-Authored-By: muse-agent-261 <muse-agent-261@noreply.invalid>
