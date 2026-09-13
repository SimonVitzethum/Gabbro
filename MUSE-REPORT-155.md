# MUSE-REPORT-155 — statement certificates for real programs (T1 transfer, part 2)

Lane 155. `gabbro certificate beispiele/104-referenz.gab` prints certificates
for BOTH bodies; both are pasted into the new `ZeugnisStmt104b.lean`, accepted
by `decide`, and pushed through the new soundness theorem. Corpus coverage is
measured below: 17 of 245 bodies print (was 8), refusals per code included.

## 1. What was built

**Rust printer** (`crates/gabbro-check/src/certstmt.rs`, extended; codes
CS001–CS005 kept, none added):

- `index into T` parameters/locals carry `(0, count - 1)` like any integer
  (the `Ty.index = .int 0 (n-1)` convention), so an index variable prints as
  `(.var k)` and recomputes wherever an index shape is owed.
- Index positions narrow through `weiter` like values: whatever `CertExpr`
  the index elaborates to, claimed at exactly `0 .. count - 1` (literals
  print byte-identically to before).
- Writes through an `rw` pointer parameter (`k.slots[i].f`, the `slots`
  path) print `assignDurch` (a `CertStmt2` shape); the table number is
  declaration order (the `tabNr` convention of `lean-g`); the pointer proof
  rebuilds from `tabNr` on the Lean side. Reads through a pointer print
  nothing in value position (`CS002`) except as a terminal `return`, which
  prints `retDurch`.
- Direct calls with arguments print `consCall` (callee name, argument
  count, erased flow; the `RufPasst` prints as `?hp`, filled at paste like
  `refHpLiesAt` was). Each argument must name a bare parameter place
  (checked here, `CS002` otherwise); arity mismatches and unknown callees
  are `CS005`. Nullary direct calls still refuse `CS004` (unchanged).
- `const` aliases resolve counts (`NKONTO = 2` in 104); the first parameter
  is de Bruijn 0 (the `gCtx` convention of `lean-g`; parameters push in
  reverse). Old-only bodies print byte-identically to lane 153 (`CertEnd2`
  via `liftE`); bodies with a new shape print `CertEnd104` terms, with old
  steps embedded through `cons1`/`bind`/terminals.
- New refusal behaviour is pinned in-test, never truncated.

**Tests** (`crates/gabbro-check/tests/certstmt.rs`, 25 tests: 13 positives,
12 refusals): new positives `call_with_args_prints`, `index_var_prints`
(direct write with an index variable), `first_param_is_index_zero`,
`ptr_write_var_index_prints`, `ptr_return_prints`, `reference_104_prints`
(both bodies, exact terms); new refusals `call_arg_count_mismatch_refused`
(`CS005`), `call_unknown_callee_refused` (`CS005`),
`call_literal_arg_refused` (`CS002`), `readonly_ptr_write_refused`
(`CS002`). Replaced: `call_with_args_refused` (now prints),
`index_var_refused` (now prints), `reference_104_refused` (now prints).

**Lean transfer** (`grammatik/Grammatik/ZeugnisStmt104b.lean`, new, imported
in `grammatik/Grammatik.lean`): the `CertEnd104` layer — `lift2` (whole old
bodies), `cons1`/`cons2` (single old steps), `bind`, `consCall` (callee,
count, carried resources, carried `RufPasst`), `ret`/`retWert` terminals,
`retDurch` (table, field, table number, index certificate). Validity
(`certEnd104Gueltig`) recomputes the count shape, reason freedom, holdings
equation, table-number equation, generated index shape, field-type equation
and guards; `Decidable` by structural recursion; the checker is
`certEnd104Ok`. The carried proofs travel beside the print as `End104Args`
(argument lists, pointers — the `Block5Args`/`Cut4Ptr` precedent).
Soundness `end104_sound`/`zeugnisStmt104b_sound` elaborate to an accepted
`Endblock`. Section 4 pastes the verbatim printer output for both 104
bodies against the `lean-g` export (`Export104.lean`: `gD`, `gCtx_*`,
`gL_*`; `?hp` filled with `gHp_einzahlen_lies`), each with a `decide`
validity example and a soundness corollary. CUTS + `#print axioms`
(standard three everywhere, no `sorryAx`).

## 2. New definitions/theorems (all in `ZeugnisStmt104b.lean`)

Types: `CertEnd104`, `End104Args`. Validity/checker: `certEnd104Gueltig`,
`decEnd104Gueltig`, `instDecEnd104`, `certEnd104Ok`. Soundness:
`end104_sound`, `zeugnisStmt104b_sound`. Witness data: `witCall104`,
`witCallArgs104`, `witDurch104`, `witDurchArgs104`. Rule-13 companions
(on `refD` + the `MB` run, `refB_erreicht`/`refB_schreibt`):
`end104_sound_zeuge` (call shape), `end104_retDurch_zeuge` (pointer-return
shape), `zeugnisStmt104b_sound_zeuge` (call shape through the top theorem).
Transfer data: `cert104_einzahlen`, `args104_einzahlen`, `cert104_lies`,
`args104_lies`, plus three forged-print rejection probes (`decide`).

Verbatim printer output now accepted:
`(.cons2 (.assignDurch Konto stand 0 true (.var 1) (.wide 0 100 (.lit 100))) [] (.consCall lies 2 [] ?hp .ret))`
`(.retDurch Konto stand 0 (.var 1))`

## 3. Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (all suites green, incl.
  25 `certstmt` tests).
- `./lean-bau`: `Build completed successfully (139 jobs)` (with the new
  module; `ZeugnisStmt104b.olean` built).
- `./lean-probe grammatik/Grammatik/ZeugnisStmt104b.lean`:
  `== 0 error(s) in the COMPLETE output` (three linter warnings only:
  unused binder name `a` in the three `_zeuge` statements).
- `pruefe-kennungen.py`: exit 0. `pruefe-englisch.py` and `pruefe-todo.py`
  exit 1 identically on the clean tree (pre-existing: measured with my
  changes stashed) — the former flags nothing in `certstmt*`/`*104b*`,
  the latter cannot find a `cargo` binary in this environment.

## 4. Corpus measurement (the instrument, then the result)

Statement-form census over `beispiele/*.gab` (95 files parse, 245 block
bodies; nested `if`s included; scratch test, since deleted): `return` 177,
`assign` 86, `let` 56, `if` 31, `call` 31 (29 with arguments, 0 nullary
direct, 2 indirect), `loop` 26, `locks` 21, `let-else` 15, `match` 13,
`narrow` 11, `alloc` 9, `exchange` 5, `awaits`/`publish` 4–5, `breaking` 3,
`observes`/`reset-arena` 2, `library-call` 1. Pointer-shaped sites: 43
writes through a parameter, 27 reads in return position; 69 `index`
parameters, 100 pointer parameters.

Of the `ZeugnisStmt2/3` forms, the corpus uses most: `assignDurch`
(43 pointer writes — printed from this lane), then loops (26:
`traverse`/`retry`/`forever`) and matches (13: `onTag`/`onGrund`), which
stay refused (arm elaboration with branch contexts plus loop invariants —
out of scope, booked in CUTS). Float steps, axiom calls, transitions and
indirect calls are absent or marginal in the corpus.

Coverage with the shipped binary (`gabbro certificate` per file): 17 of
245 bodies print (lane 153: 8), 228 refuse — `CS001`: 86, `CS002`: 23,
`CS003`: 19, `CS005`: 100 (`CS004` fires on no corpus body: there is no
nullary direct call in `beispiele/`). Printing files: 06 (2), 104 (2),
13/14/16/70/72/93 (1 each), 43 (2), 47 (2), 52 (3). Seven files yield no
section (check errors, all without block bodies: 07, 11, 20, 24, 51, 60,
67). The `CS005` count rose (85 → 100) while `CS001`/`CS002`/`CS003` fell:
bodies that refused early now travel further and fail on later checks
(result ranges, unknown names) — the refusal is deeper, not new.

## 5. What remains open

- Calls inside `if` branches, `let`-bound pointer reads, indirect calls
  with arguments, `bindCallElse`-style error channels: refused by name
  (`CS001`/`CS002`), arms unwritten (CUTS).
- Loops and matches (26 + 13 corpus sites): the largest printable
  remainder; needs arm-body recursion plus invariant/condition shapes.
- Term identity (`print (elab x) = x`) still proved nowhere; the
  `einzahlen` paste passes a fresh `ptrOf` (as the `lean-g` export does),
  not the caller's variable — booked in CUTS.
- `CS004` no longer fires anywhere (kept as a code, as tasked).

## 6. What I believe is wrong in the task

- "Calls with arguments (`CertBlock5`/`Block5Args` in `ZeugnisStmt.lean`)":
  the precedent lives in `Zeugnis.lean`, and it is `Block`-level — no
  `Endblock`-level shape for a call with arguments existed. `CertEnd104`
  adds it (count recomputed, `Args` as proof, same honesty justification).
- "Index parameters/variables (with their recomputable ranges)" holds with
  no new Lean shape at all: `Ty.index` IS `.int`, so `ctxTyp` recomputes an
  index variable's range and the existing `assignDurch`/`slot` arms accept
  it — the gap was printer-side only (literal-only indices, `Sonst`
  parameters, literal-only counts).
- "The forms of `ZeugnisStmt2/3` the corpus uses most" is satisfied by
  `assignDurch` (43 sites, the top such form); loops/matches, the next two,
  do not fit "extend the printer to print them" in this lane and are
  reported refused instead of half-printed.
