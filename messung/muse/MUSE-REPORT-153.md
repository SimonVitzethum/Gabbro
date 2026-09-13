# MUSE-REPORT-153 — statement certificates from Rust (T1 transfer)

Lane 153. Printer built, tests green, Lean transfer file checks.
One task premise is wrong with evidence: 104 cannot check (finding §3).

## 1. What was built

**Rust printer** (`crates/gabbro-check/src/certstmt.rs`, new, ~1000 lines):

- `zeige(baum) -> String` — section S of `gabbro certificate`
  (wired into `zeugnis::zeige`): one `CertEnd2` term per block body,
  or a named refusal. `zeige_rumpf(f, info) -> BodyCert`,
  `zeuge_funktion(baum, name) -> Option<BodyCert>` (per-function query,
  used by the tests). `BodyCert::{Gedruckt{lean}, Abgewiesen{weigerung}}`,
  `Refusal{code, grund}` with reserved codes CS001–CS005:
  CS001 statement form with no printed shape, CS002 expression with no
  `CertExpr` shape, CS003 index/variable with no recomputable range,
  CS004 nullary direct call (shape exists, `RufPasst` travels as proof),
  CS005 unresolvable name/count/range for the claim.
- Prints: `return;` (`.ret`), `return <int>` (`.retWert` with the result
  range), `let x : <range> = …` (`.bind`), integer locals (`.assignVar`),
  direct table writes with literal indices (`.assignSlot`), `if` with
  printable condition and falling branches (`.ite` over `CertSeq`);
  integer expressions `lit/add/sub/mul/neg/var/slot/wide`, conditions
  `wahr/falsch/var/lt/le/eq/und/oder/nicht` (`>`/`>=`/`!=` normalized).
  Values narrow under `wide` exactly where the checker elaborates
  `weiter` (exact prints bare, contained prints `wide`, uncontained is
  CS005). Resource lists print as `[]`; counts/field/alias ranges resolve
  from literal declarations only.
- Refuses everything else by name, never truncated: calls with arguments,
  indirect calls, matches, loops, `let-else`, `leave`/`next`, registers,
  marks, float/global steps, division/bitwise/shifts, pointer reads and
  writes (`durch`), index variables, non-literal counts.

**Tests** (`crates/gabbro-check/tests/certstmt.rs`, new, 19 tests):
7 exact-term positives (incl. `wide` narrowing), 12 refusals covering
every code, incl. `beispiele/104-referenz.gab` (both bodies refused) and
`beispiele/04-schleifen.gab` (loop refused).

**Lean transfer** (`grammatik/Grammatik/ZeugnisStmt104.lean`, new, marked
generated, imported in `grammatik/Grammatik.lean`): demo declaration
`csD` (`CSTab/CSFeld/CSFn/csSig/csV`, lock-free so `[]` validates) plus 7
verbatim pasted certificates, each with a `decide` validity example and a
`zeugnisStmt2_sound` corollary: `csCertRet`, `csCertBind`, `csCertVar`,
`csCertWenn`, `csCertSlot`, `csCertWide5`, and `csCertDoppelt` (verbatim
output for `doppelt`, `beispiele/93-const-scalars.gab`, a real corpus
body). Section 3 records the 104 refusal output. CUTS + `#print axioms`
(standard three only). No edits to `ZeugnisStmt.lean`/`ZeugnisStmt2.lean`.
No codes/gifts/examples beyond the reservation (CS001–CS005 only).

## 2. Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (all suites green,
  incl. 19 new `certstmt` tests).
- `./lean-bau`: `Build completed successfully (116 jobs)`,
  `== 0 error line(s) in the COMPLETE output` (with the new module;
  `ZeugnisStmt104.olean` built).
- `./lean-probe grammatik/Grammatik/ZeugnisStmt104.lean`:
  `== 0 error(s) in the COMPLETE output`.

## 3. Finding: the 104 target does not hold (measured, not assumed)

The task asks for a `decide`-checked certificate for
`beispiele/104-referenz.gab`. Both bodies fall outside `CertEnd`/`CertEnd2`:

- `einzahlen`: `k.slots[i].stand = 100` writes through a pointer with an
  index-typed variable (no `CertExpr` range exists for either), then
  `lies(k, i)` calls WITH arguments (the R-2 fragment is nullary only).
- `lies`: `return k.slots[i].stand` reads through a pointer (`durch` has
  no `CertExpr` shape).

Verbatim printer output (section S):

```text
function einzahlen: REFUSED CS002: pointer write k.slots[…].stand has no CertStmt shape
function lies: REFUSED CS002: pointer access k.slots[…].stand has no CertExpr shape
```

This is not a printer gap I could close honestly: `CertStmt.call`
requires `D.params f = []`, `assignDurch` (the covered pointer write)
needs `certRange i = some (0, count - 1)` which an index variable never
has, and `durch` is booked out in `Zeugnis.lean` itself. Printing the
fixture-shaped `refCertEin` for the surface program would fabricate the
term-identity link lane 146 booked as proved nowhere. I report the
refusal instead of weakening it: the refusal is pinned in-test
(`reference_104_refused`) and recorded in `ZeugnisStmt104.lean` §3.

Second program "with a loop or a match if one fits": none fits.
Survey over `beispiele/*.gab` (this printer as instrument): `CertEnd2`
terms print only for straight-line integer bodies — `doppelt` (93),
`(.liftE .ret)` for the `abnahme`/`freigabe` bodies of 06/43/52, the
eight-variable sum of `70-kernel-namen.gab`. Every loop and every match
in the corpus is refused by name (first refusal per body).

## 4. What remains open

- Index-typed variable rows, with-arguments call rows (the `CertBlock5`
  precedent), `durch` rows, `RufPasst`-as-proof emission (CS004),
  resource-flow tracking (currently `[]`, so guarded tables fail loudly
  rather than certify), term identity (`print (elab x) = x`, booked).
- The `k3_namen` eight-sum term and the `abnahme`/`freigabe` `.ret` terms
  are generated but not pasted (seven pastes suffice for the target).

## 5. What I believe is wrong in the task

- "The printed certificate for 104 checks by decide" presumes the surface
  program fits the certificate fragment; it does not (§3). The fixture
  (`refD`, nullary `lies`) and the program (`lies(k, i)`) were conflated.
- "One more corpus program with a loop or a match" presumes a fitting
  one exists; the survey says none does. The "if one fits" hedge saved
  this half; the 104 half has no such hedge but needs one.
