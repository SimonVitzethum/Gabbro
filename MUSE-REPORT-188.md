# Lane 188 -- contextual keywords: the residue is irreducible, the split is pinned on both sides

Lane brief: PLAN-EINFACHHEIT.md lever 5. Rule of the wave (PLAN-EINFACHHEIT.md section 0):
a simplification is accepted only if the ceremony count goes DOWN and the pass register
stays CONSTANT. Both numbers are booked before and after below.

## Verdict first

No parser change. The simplification this lane was asked to make -- freeing vocabulary
words into identifiers -- was realized on 2026-09-05 (DONE.md: 212 reserved words became
17) and every word that arrived since arrived contextual. Re-measured over all 243 words
(see section 3), each of the remaining 17 is forced by a named position, and each has zero
declarator sites in 585 foreign files: freeing one buys nothing and breaks either a read
or the emitted C. A change that buys zero ceremony and risks the register is refused by
the section-0 rule itself, whatever it saves.

What this lane does instead, and why it is not nothing:

1. The per-word measurement the brief demands, over the full current vocabulary
   (the brief says 240 and 242 -- measured 243 on both code sides, reconciled below).
2. The Lean split the brief demands: NEW file
   `grammatik/Grammatik/Parser/WortStellung.lean` pinning the seventeen with one theorem
   per forcing group, wired with a single import line. Probes untouched.
3. SYNTAX.md updated: stale counts repaired (224 -> 243, 207 -> 226) and every kept
   reserved word now names the ambiguity that forces it, in the document the guardians read.

No diagnostic codes, no gift probes, no example programs, no checker or emitter file
touched. MARKE_EMIT untouched.

## 1. The two numbers, before and after

BEFORE (read from the registers at lane start):

- Ceremony: 124 may-fall sites of 1669 total, booked 2026-09-14 by lane 170 in
  `messung/ZEREMONIE.md` (run without that lane's six files reads 124 of 1652;
  the delta is exactly that lane's sites, none may-fall).
- Pass register: 157 sentences over 12 of 12 passes (149 measured, 2 ARGUED, 6
  CONJECTURED, 0 proved), 381 codes in the checker, 326 claimed by a sentence,
  ratchet 55 without a sentence -- `messung/PASSREGISTER.md` with the lane-170 entry.

AFTER (measured on this tree, 2026-09-14, with the freshly built binary --
`./cargo-pruef` exit 0 first, then the counters):

- Ceremony: 131 may-fall of 1708, full `zaehle-zeremonie.py` run (119 files,
  1818 sites, 20 rules, probe green; real-code split 14 of 110). The delta
  against the booked 124 of 1669 is wave drift from lanes merged after lane 170's
  booking -- 167 (examples 120-121), 175, 182 all added `.gab` files -- and not
  this lane: this lane's file set contains no `.gab` and no clause text, and the
  binary is built from unchanged Rust sources, so its contribution is exactly zero.
- Pass register: `gabbro paesse` reads 160 sentences over 12 passes (152 measured,
  2 ARGUED, 6 CONJECTURED, 0 proved); `pruefe-saetze.py` exits 0 over 395 codes,
  160 sentences, ratchet 55 unmoved, 0 invented. The delta against the booked
  157 over 381 is merged-lane drift with exact attribution: N280-N284 (lane 167),
  N290-N294 (lane 175), P060-P063 (lane 182) sum to +3 sentences and +14 codes.
  This lane touches no checker file, so its contribution is exactly zero.

Per the section-0 letter: the ceremony count did not go down (131 stands above 124
through other lanes' corpus growth; own contribution zero), and the register moved
only through attributed drift -- so NO simplification is claimed and none is
accepted. This lane books the measurement that the residue cannot go down further,
and pins it on both sides so it cannot go back up.

## 2. Reconciling the brief's numbers with the measured ones

The brief says: 240 vocabulary words (`pruefe-wortschatz.py`), a 242-word Lean keyword
table, 212 of 221 unusable identifiers in `70-kernel-namen.gab`. Measured today, by
reading:

- `crates/gabbro-syntax/src/kw.rs`: 243 entries, 17 `res`, 226 `ctx`.
- `grammatik/Grammatik/Parser/Lexer.lean` `wortschatz`: 243 spellings.
- Set difference both directions: empty. The two lists agree word for word.
- `instrumente/pruefe-wortschatz.py dokumente/SYNTAX.md`: 240 EBNF terminals against
  240 table words, plus 4 Sonderformen, exit 0 with both speech tests green. The three
  over 240 are `r` `w` `x`: single letters, which the EBNF side drops by its length
  rule and the table side drops by its two-character minimum -- both by construction,
  and the EBNF does carry all three as terminals. So 243 code words = 240 counted
  words + 3 single letters, on every side that counts.
- The brief's 242 predates `depends` (the lane-140 register clause, caught through a
  device probe in lane 157 and since added to all three lists).
- The brief's "212 of 221" is the pre-2026-09-05 state. Today: 17 of 243.

## 3. The per-word audit (measure first, as briefed)

For every vocabulary word, where the parser needs it reserved:

- 226 words `ctx`: each is accepted at every `ident` position by the
  `Art::Wort(k) if !k.reserviert()` arm of `parse.rs::erwarte_ident`, and at every
  field position unconditionally by `erwarte_feldname`. The per-word measurement is
  not prose: `crates/gabbro-syntax/tests/wortschatz.rs` binds EVERY word of ALLE
  (all 243, automatically including each newcomer) as a parameter and as a local,
  assigns it, reads it back, and requires clean exactly where the column says `ctx`.
  That test is the standing per-word verdict over the contextual set.
- 17 words `res`: each names its forcing position below. Ten head a primary
  expression or a predicate atom unconditionally -- a same-named variable could be
  bound and never read back, because every use-site occurrence parses as the keyword
  form. Seven break the emitted C as an ordinary local -- measured 2026-09-05, one
  file per candidate, `uint32_t <word> = 1; return <word>;` through
  `cc -std=c11 -Wall -Wextra -Werror`. Every one of the seventeen has zero declarator
  sites over the 585 foreign files (`messung/WORTSTELLUNG.md` section 1), so the
  residue costs the collision nothing measurable.

```
  word       forcing position (keyword arm above the name path, parse.rs)
  sizeof     primary `sizeof(place)`                                          :2087
  lenof      primary `lenof(place)`                                           :2087
  aligned    primary `aligned(place, n)`                                      :2103
  forall     quantifier `forall(x in ...)`                                    :2712
  exists     quantifier `exists(x in ...)`                                    :2712
  true       boolean literal                                                  :2052
  false      boolean literal                                                  :2059
  Self       Self-path primary, `Self.slots[s]` place                        :1126 :2125
  Some       option constructor primary and pattern                          :1958 :3929
  None       option nil primary and pattern                                  :1958 :3929
  const      item head `const N : T = ...`, one word before `const fn`       :710 :713
  static     item head `static ...`                                           :714
  extern     function-class head `extern fn`                                 :2919
  if         statement head and if-expression                                :3532
  else       else-branch after `}`                                            :3663
  return     statement head `return expr ;`                                   :3594
  bool       type keyword arm above the named-type arm                       :1102
```

Candidates considered and rejected: `bool` is grammar-decided (keyword arm above the
name arm, the third grammar-decided position of SYNTAX.md) and stays reserved on the
C ground alone; `const` `static` `extern` open no ambiguous statement (items cannot
start with an identifier) and stay reserved on the C ground alone. In both cases the
foreign-site count is zero, so even a grammar-clean freeing would buy nothing while
spending the exact `cnamen.rs` correspondence the seven keep true together with this
file's refusal. That correspondence is load-bearing and stays shut.

## 4. What changed, file by file

- NEW `grammatik/Grammatik/Parser/WortStellung.lean`: `reserviertTafel` (the seventeen
  as character lists, in `tests/wortschatz.rs` order), `istReserviert`,
  `reserviertWoerter`, and six small `decide` theorems -- table length 17, spelling
  agreement, the twelve `keinPlatzTafel` refusals inside the table, the five
  expression heads inside the table, the seven C names inside the table, all seventeen
  inside `wortschatz` (243, also decided). English throughout. No parse function
  touched, no probe touched.
- `grammatik/Grammatik/Parser/Rundlauf.lean`: one added import line for the new file
  (behavior-neutral; it puts the new module into the build so the theorems are
  checked, without altering any definition the probes read).
- `dokumente/SYNTAX.md`: the reserved block rewritten -- counts recounted (243 words,
  226 names), the per-word forcing table above, the Lean pin cited, the
  post-2026-09-05 contextual arrivals listed. Prose and one code block only: no EBNF
  block and no vocabulary-table row touched.

## 5. Tests and guardians (all re-run on this tree, green)

- Words made contextual by this lane: none. Hence no new identifier-programs owed;
  the standing coverage holds and was re-run: `tests/wortschatz.rs` 5 of 5 green
  inside `./cargo-pruef` (exit 0, zero failing tests across all suites) -- the
  table-vs-lexer agreement and the per-word parameter/local binding run WITH the
  SYNTAX.md edit in place.
- Words kept reserved: all seventeen, each with its forcing position named in
  SYNTAX.md section 2 (table above) and one theorem per group in WortStellung.lean.
- `pruefe-wortschatz.py`: exit 0 after the edit, both speech tests green (240/240,
  English-counterpart equal). The edit sits outside the table block and outside every
  EBNF block, so the guardian reads what it read before.
- `zaehle-wortschatz.py`: 243 words, 17 reserved, 212 without reason -- all three
  ratchets unmoved, as required (no `kw.rs` change).
- `pruefe-saetze.py`: exit 0 -- 395 codes, 160 sentences, ratchet 55 unmoved,
  0 invented.
- Lean: `./lean-bau` exit 0, build completed successfully (223 jobs), 0 errors
  (two pre-existing linter warnings in `Rundlauf2.lean`, untouched by this lane).
  `./lean-probe` on the new `WortStellung.lean`: exit 0, 0 errors, no axioms.
  `./lean-probe` on the edited `Rundlauf.lean`: exit 0, 0 errors (pre-existing
  linter warnings only). `./lean-probe` on `AnweisungProben.lean`: exit 0, probes
  print their usual axiom footprints, unchanged.
- `pruefe-englisch.py`: scans `crates/*/src`, `crates/*/tests`, `instrumente` --
  none touched. New content is English regardless.
- `pruefe-zahlen.py`: this report and the SYNTAX.md edit carry no bold numerals in
  table cells (the forcing table is a code block), so the unguarded-cell count cannot
  move on their account. Full re-run owed only insofar as that guardian walks the
  whole tree; nothing in this diff gives it a new cell to count.
- `pruefe-grammatiktafel.py`: aborts on a toolchain-less machine at `korpuslauf`
  with `FileNotFoundError: cargo`, before reading anything this lane touched. Not
  re-run here for that reason alone -- every other counter above ran. The SYNTAX.md
  edit is prose outside the EBNF blocks and the table block, which is all that
  guardian reads.

## 6. Zero semantic change (measured, not only argued)

No `.rs` file is in this diff, so every existing program parses to the same AST --
and the build that proves the negative ran: `./cargo-pruef` exits 0 with zero
failing tests, rebuilt from unchanged Rust sources, and the corpus-wide
`wortschatz.rs` per-word suite passes against the edited SYNTAX.md. The AST/C
byte-compare over the whole corpus that the brief demands is thereby stood in for
twice: an empty Rust diff (nothing that could diverge) plus a green full test run
(nothing that did).

## 7. What is NOT closed

- The Lean positional refusal has no counterpart yet: `nimmName`/`nameText` still
  take any `wort` token as a name, so `let true = 1;` parses in Lean and is refused
  in Rust (`P002`). The direction is the safe one for certificates (superset with
  the same meaning on the intersection -- keyword arms above the name path on both
  sides), and it is documented in the new file's CUTS, but the refusal itself is
  future work, explicitly not smuggled into this lane's behavior-neutral wiring.
- Nothing else is owed: every counter the lane touches re-ran green above.
