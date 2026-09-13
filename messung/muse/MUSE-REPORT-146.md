# MUSE-REPORT-146 (lane 146, T1 part 2: remaining statement-certificate constructors)

## What was built

New file `grammatik/Grammatik/ZeugnisStmt2.lean` (887 lines), imported at the
end of `grammatik/Grammatik.lean`. It extends `ZeugnisStmt.lean` to the
statement/block shapes that fit the current certificate data, following that
file's architecture exactly: plain-data certificates, recomputed validity
predicates with `Decidable` instances (`decide`-closed acceptance and
rejection), soundness by structural elaboration, one lemma per constructor.

### Measurement first (task question 1)

Counted from the `Stmt`/`Block`/`Endblock` inductives in
`grammatik/Grammatik/Syntax.lean:407-548` against the covered cases of
`ZeugnisStmt.lean`: the tree has **27 + 17 + 6 = 50 constructors, not 49**.
`ZeugnisStmt.lean` books "38 of 49" (21 + 11 + 6) and its `CUTS` already
lists every booked shape, so one `Stmt` constructor was added after that
count was written (stale denominator, not a miscount of the gap). The
**twelve** missing constructors:

- `Stmt` (6): `assignDurch`, `onTag`, `onGrund`, `callInd`, `axiomCall`,
  `transition`.
- `Block` (6): `bindCallInd`, `bindAxiom`, `gleit`, `gleitLit`,
  `gleitVon`, `gleitNarrow`.
- `Endblock`: none missing (6 of 6).

### New definitions

- `CertStmt2 D V` — the four remaining `Stmt` shapes as plain data:
  `assignDurch` (table number + `rw` flag + two `CertExpr`), `callInd`
  (callee + signature number + carried `Λc` + `RufPasst`-as-proof),
  `onTag` (`cs` + index + payload option + `CertArms2`), `onGrund`
  (`n` + `r` + `CertGrundArms2`).
- `CertArms2 D V cs` / `CertGrundArms2 D V n` — arm-list certificates
  mirroring `Arms`/`GrundArms` (case pinned per arm / length `n`).
- `CertSeq2 D V` — the five remaining `Block` shapes with `CertSeq2`
  tails plus `lift` (reuses every old block print) and `cons2` (new
  statements inside blocks): `bindCallInd`, `gleit`, `gleitLit`,
  `gleitVon`, `gleitNarrow`.
- `CertEnd2 D V` — body prints: `liftE` plus `cons2E`.
- Validity Props `certStmt2Gueltig`, `certArms2Gueltig`,
  `certGrundArms2Gueltig`, `certSeq2Gueltig`, `certEnd2Gueltig` with
  `Decidable` instances (`decStmt2Gueltig`, `decArms2Gueltig`,
  `decGrundArms2Gueltig`, `decSeq2Gueltig`, `decEnd2Gueltig` +
  `instDecStmt2/Arms2/GrundArms2/Seq2/End2`).
- Checkers `certStmt2Ok`, `certSeq2Ok`, `certEnd2Ok` (`decide` of validity).

### New theorems (all premises used; no `sorry`/`axiom`/`admit`)

- Helpers: `fall_typed` (valid `fall` print elaborates to `Expr … (.sum cs)`
  — the `cut3_sound` fall case with the type pinned), `arms2_sound`,
  `grundArms2_sound`.
- Per-constructor soundness (9): `assignDurch_sound`, `callInd_sound`,
  `onTag_sound`, `onGrund_sound` (direct proofs), `bindCallInd_sound`,
  `gleit_sound`, `gleitLit_sound`, `gleitVon_sound`, `gleitNarrow_sound`
  (single-constructor corollaries of `seq2_sound` — splitting them into a
  `mutual` block defeats structural recursion, since each helper recurses
  on a certificate it receives as an argument; the reason is documented
  in-file above `seq2_sound`).
- Joint: `stmt2_sound`, `seq2_sound` (structural, all block cases inline),
  `end2_sound`, and the target `zeugnisStmt2_sound` (valid body print
  implies `∃ _ : Endblock …, True`).
- Witnesses (10, rule 13): `assignDurch_sound_zeuge`,
  `callInd_sound_zeuge`, `onTag_sound_zeuge`, `onGrund_sound_zeuge`,
  `bindCallInd_sound_zeuge`, `gleit_sound_zeuge`, `gleitLit_sound_zeuge`,
  `gleitVon_sound_zeuge`, `gleitNarrow_sound_zeuge`,
  `zeugnisStmt2_sound_zeuge` — each instantiates ALL premises jointly on
  `refD`/`vertragVon refD refEin` plus the non-degenerate run (`MB`,
  `refB_erreicht`, `refB_schreibt`: `konto` written, slot `0 → 100`).
- Three rejection probes (`¬ …Gueltig …` by `decide`): read-only pointer
  as write carrier, reason `1` of one, `zahl` payload on the caseless sum.

`#print axioms` for all 26: only `[propext, Classical.choice,
Quot.sound]` — the project's standard base, no extra axioms.

### Not covered, with exact reasons (3 of 12, in-file `CUTS`)

- `axiomCall`, `bindAxiom`: the foreign-write/guard frames quantify over
  arbitrary carrier types — the R-3 indexed-certificate shape, not plain
  data. AND no rule-13 witness exists on the fixture: `refD.Ax` is
  `Empty`, so no such certificate is even well-typed there.
- `transition`: `D.spiegel r = some m` needs `DecidableEq D.Reg`, which
  the declaration does not supply (there is `decTab`/`decGlob`/`decLock`/
  `decMarke`, no `decReg`); `refD.Reg` is `Empty`, so no witness either.
- Calls with arguments stay in the R-2 nullary fragment; the
  with-arguments shape is the existing `CertBlock5`/`Block5Args`
  precedent, not re-proved here.

### Rust side

`zeugnis.rs` needed NO print change: `erhebe`/`block` is already
exhaustive over every surface `StmtArt` (no wildcard arm), so the surface
origins of all nine shapes were booked (pointer writes under
`assignment`, indirect calls under `call`, tagged and reason matches
under `match (tagged)`, float steps under `let`/`narrow`/`return`).
New file `crates/gabbro-check/tests/zeugnis_stmt2.rs`: 9 tests, one per
form, each asserting its input parses (`fehler_zahl() == 0`, loud on
failure), the census carries the expected mark, and `unzugeordnet` is
empty. All 9 pass by name; full `./cargo-pruef` exits 0 with 0 failing
tests. `certemit.rs` still prints expression certificates only; the
statement print format stays designed in `ZeugnisStmt.lean`'s `CUTS`.

### Term identity (task question)

It is proved NOWHERE — neither `Zeugnis.lean`/`ZeugnisStmt.lean` nor
`certemit.rs` links the printed certificate to the checked term.
`certemit.rs` states it outright ("printer-prints-what-was-checked is
trust base there"). The smallest closing statement for one expression:
`theorem print_elab (e : CheckedExpr) : elab (print e) = e` — the printer
applied to the CHECKED term re-elaborates to that same term. It needs
(a) the printer to take the checked (typed) term, not the raw AST, and
(b) `elab` computational (`Option`-returning, `= some e` by `rfl` over
the validity predicates) — lane 136's report already names direction
(b): current soundness yields `∃`, proved with choice inside, so the
witness term is not computational. One expression form fixes the shape;
per-constructor instances follow the T1 rows.

## Last builds

- `./lean-bau` → `== 0 error line(s) in the COMPLETE output`
  (`✔ [103/104] Built Grammatik`, `Build completed successfully (104 jobs)`).
- `./cargo-pruef` → `== exit 0; failing tests: 0` (full suite, no-fail-fast).

## What remains open

The 3 listed constructors (`axiomCall`, `bindAxiom`, `transition`)
need a fixture lane (axioms + registers in the reference declaration,
`decReg` on the declaration) before their nullary fragments can be
certified with witnesses; the with-arguments call fragment; the Rust
statement printer (transfer phase); term identity per the statement
above; the closing per-program theorem (with T2–T4).

## Task feedback (rules 4/12/13)

Nothing in the task was weakened: 9 of the 12 missing constructors are
certified with one lemma each plus a joint witness-carrying top theorem;
the 3 left listed are left listed with the exact reason (no witness
possible on `refD` — `Ax`/`Reg` are `Empty` — and no recomputation
possible without `decReg`/indexed proofs), not with weakened
certificates. One correction to the task text: it asks for "the 11
missing constructors" — the measured number is 12 (the "38 of 49" count
in `ZeugnisStmt.lean` undercounts `Stmt` by one: 27, not 26).
