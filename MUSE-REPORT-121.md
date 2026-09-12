# MUSE-REPORT-121

Lane 121: CONST CERTIFICATE FROM THE SOURCE (follow-up of lane 111).
Rust + Lean lane; branch `muse/121`.

## Merge reconciliation with lane 111 (reviewer request, 2026-09-12)

The branch predated lane 111; `master-neu` (lanes incl. 111, 118, 120)
arrived as an open merge with conflicts in `tests/konstanten.rs`,
`Grammatik.lean`, and `Grammatik/Konstanten.lean`, all resolved here:

1. **ONE evaluator**: lane 111 did not touch `Umgebung` (it reuses
   `konst_wert`), so the lane-121 nested-call binding fix in
   `auswerten_mit` (thread `werte` through the `Ruf` arm, same
   guard/arity discipline) stands as the single evaluator change.
   Self-nesting stays refused by the deliberate name guard.
2. **Certificate from the source**: `konstanten::certificate` no longer
   takes a hand `equation: &str`. It takes the translated definition
   line plus the function name
   (`certificate(name, values, fn_def, fn_name)`), and the convenience
   `certificate_of_const_fn(name, values, lean_fn, param, body,
   funktionen)` translates via `konst_lean::funktion_lean` and
   assembles. The literal reuses `konst_lean::tabelle_lean`.
   `konst_lean::zertifikat_lean` (the lane-121-only file shape) is
   removed; one path remains.
3. **ONE `Konstanten.lean`** (namespace `Gabbro.Grammatik.Konstanten`):
   lane-111 generic lemma (`konstZert`, `konstZert_nil`,
   `mem_zipIdx_aux`, `mem_zipIdx_of_getElem?`, `konstZert_mem`) plus
   the lane-121 fragment (`KBinOp`, `KUnaOp`, `KExpr`, `KBinOp.eval`,
   mutual `KExpr.eval`/`KExprList.eval`) and soundness
   (`quad_aus_syntax` + probes + `squares64_aus_syntax` +
   `quad_aus_syntax_zeuge`). No duplicated definitions: `quadTabelle`
   is gone (one table: `squares64`), `quadPruefe` is gone (one check:
   `konstZert squares64 …`), and the hand equation `i * i` is gone
   everywhere -- `squares64_zert` and `konstZert_mem_zeuge` now read
   `(fun i v => v == quad i)` with `def quad (i : Nat) : Nat := i * i`
   byte-held against the printer by the Rust exact-string test.
   `Grammatik.lean` carries both imports (`Konstanten`, `AuditW5`).
4. **ONE test file** (`tests/konstanten.rs`, 17 tests): lane 111's 13
   unchanged except `certificate_meets_witness`, which now translates
   the `quad` body instead of handing in `p.1 == p.2 * p.2`, and
   asserts the Lean file carries
   `konstZert squares64 (fun i v => v == quad i)`; plus 4 lane-121
   tests (English names): exact unified-certificate bytes, operator
   pins, nested distinct calls, no-certificate cases.

## What I did (before the merge)

Lane 111 is not in this tree (no const-certificate printer and no
hand-written defining equation exist anywhere in it), so I built the
whole path the task asks for. (Superseded in part by the reconciliation
above: lane 111 has since merged and the two paths are now one.)

1. **Printer** (`crates/gabbro-check/src/konst_lean.rs`, new, wired as
   `pub mod konst_lean` in `lib.rs`): translates a `const fn` body in the
   single-expression fragment to Lean `Nat` syntax. `ausdruck_lean`
   covers literals, `true`/`false` (as `1`/`0`), the parameter, other
   named consts (printed as-is), arithmetic (`+ - * / %`), bit ops
   (`Nat.land/lor/xor/shiftLeft/shiftRight`), comparisons and logic (as
   `0`/`1` via `if`), and calls of other const fns (Lean application,
   compound arguments parenthesised). `funktion_lean` emits the `def`
   line, `tabelle_lean` the `List Nat` literal, `zertifikat_lean` the
   whole file: translated `def`, table, and
   `List.all <table>.zipIdx (fun (v, i) => v == f i)` closed by
   `decide`. Refused (`None`): negation, `~`, wrap/saturate ops (the
   checker does not fold them either), floats, counts, built-ins,
   indirect calls. Helpers `ruf_ausdruck`/`werte_tabelle` build the
   table through the checker's OWN folder (`Umgebung::konst_wert`),
   so the values are computed from the source, not hand numbers.
2. **Checker fix** (`umgebung.rs`, `auswerten_mit`): nested const-fn
   calls dropped the parameter bindings (the `_` fallback called
   `auswerten` without `werte`), so `doppelt(plusEins(n))` evaluated to
   nothing while the printer printed it. The new `Ruf` arm threads the
   bindings with the same guard/arity discipline as `auswerten`.
   Self-nesting (`doppelt(doppelt(n))`) stays `None` by the deliberate
   name-based recursion guard.
3. **Tests** (`crates/gabbro-check/tests/konstanten.rs`, new, 4 tests):
   the printed Lean for the 64-entry square table is byte-for-byte the
   translation of `quad(i)` (values from the checker folder at 0..64,
   `def` line asserted separately); every operator family pinned;
   nested distinct calls print as application with checker agreement at
   21 (44); non-printable (`-i`) and non-evaluable (`1 / (x - x)`)
   yield no certificate.
4. **Lean** (`grammatik/Grammatik/Konstanten.lean`, new, imported by
   `Grammatik.lean`): `KBinOp`/`KUnaOp`/`KExpr` (literals, parameter,
   named consts, calls by name, operators), `KBinOp.eval` and mutual
   `KExpr.eval`/`KExprList.eval` on `Nat`; soundness
   `quad_aus_syntax : ∀ i, quadSyntax.eval leerEnv leerFns i = quad i`
   plus one probe theorem per remaining arm
   (`dreiPlusVier_aus_syntax`, `konst_aus_syntax`, `ruf_aus_syntax`);
   the 64-entry `quadTabelle`/`quadPruefe` certificate closed by
   `decide` (`quadPruefe_holds`, axiom-free); `quadTabelle_aus_syntax`
   rewrites the certificate to evaluation of the SYNTAX through
   `quad_aus_syntax`; witness `quad_aus_syntax_zeuge`
   (`eval … 7 = 49 ∧ quadPruefe = true`, both sides `decide`).
   Ends with `CUTS:` and `#print axioms` for all seven theorems.

## Exact names of new definitions/theorems

Rust: `konst_lean::ausdruck_lean`, `::binaer_lean`, `::operand_lean`,
`::funktion_lean`, `::tabelle_lean`, `::ruf_ausdruck`,
`::werte_tabelle`; `konstanten::certificate`,
`::certificate_of_const_fn`; tests
`printed_lean_is_the_translation_of_quad`,
`every_operator_family_prints_its_nat_form`,
`nested_const_calls_print_as_lean_application`,
`unprintable_yields_no_certificate` (plus lane 111's 13 in the merged
file).
Lean (`Gabbro.Grammatik.Konstanten`): `KBinOp`, `KUnaOp`, `KExpr`,
`KBinOp.eval`, `KExpr.eval`, `KExprList.eval`, `leerEnv`, `leerFns`,
`quadSyntax`, `quad`, `quad_aus_syntax` (+ `quad_aus_syntax_zeuge`),
`dreiPlusVierSyntax`, `dreiPlusVier_aus_syntax`, `constUmgebung`,
`constSyntax`, `konst_aus_syntax`, `doppelt`, `plusEins`,
`zweimalPlusEinsFunktionen`, `zweimalPlusEinsSyntax`, `ruf_aus_syntax`,
`squares64`, `squares64_zert`, `squares64_aus_syntax` (plus lane 111's
`konstZert`, `konstZert_nil`, `mem_zipIdx_aux`,
`mem_zipIdx_of_getElem?`, `konstZert_mem`, `konstZert_mem_zeuge`).
ZEUGE soundness theorem: `quad_aus_syntax`; witness: the square table
(`quadTabelle`/`quadPruefe`, 64 entries, joint witness
`quad_aus_syntax_zeuge`).

## Last build results (after the reconciliation)

- `./lean-bau`: `Build completed successfully (63 jobs).`
  (`== 0 error line(s) in the COMPLETE output`; axioms: lane-111
  lemmas `[propext, Quot.sound]` (`konstZert_nil` and `squares64_zert`
  axiom-free), soundness/probe theorems `[propext]`,
  `squares64_aus_syntax` `[propext, Quot.sound]`.)
- `./cargo-pruef`: `== exit 0; failing tests: 0` (all targets green;
  merged `konstanten` target 17/17).
- Independent check: the unified expected certificate text extracted
  byte-identically from the Rust test to scratch
  (`$TMPDIR/opencode/sq_cert.lean`) gives
  `== 0 error(s) in the COMPLETE output` under `./lean-probe`, i.e.
  `decide` closes the generated file.
- `pruefe-englisch.py` exits 0; `pruefe-zahlen.py` shows only
  pre-existing tree-wide ratchet drift (no finding names the new
  files; new files contain no German).

## What remains open

- The `quadTabelle` in `Konstanten.lean` is hand-copied from the
  printer output; only the Rust exact-string test holds the two
  together (booked in `CUTS:`).
- No proved link between the checker's `i128` folder and `KExpr.eval`
  on `Nat`; the two sides meet at the shared numbers (booked in
  `CUTS:`). `Nat` subtraction/division differ from `i128` outside
  non-negative non-underflowing use; a body leaving that range yields
  no table on the Rust side, hence no certificate.
- Numbers 225-229, probes 900-904, examples 102-103: none used (no new
  diagnostics, poison probes, or examples were needed; lane 111 owns
  K190-K194, gifts 860-864, examples 92-93).

## What I believe is wrong in the task

1. The task's `List.all (fun (i, v) => v == f i) (zipIdx table)` does
   not elaborate in Lean 4.33.1 twice over: `List.zipIdx` yields
   `(value, index)` pairs (measured: `[(10, 0), (20, 1), …]`), so the
   binders must be `(v, i)`, and `List.all` takes the list first. The
   certificate is
   `List.all quadTabelle.zipIdx (fun (v, i) => v == quad i)`.
2. The reference fixture rule does not apply to the witness: the
   soundness theorem has no premise over program syntax (only the
   `Nat` binder `i`), so there is no `refD` table to write and no run
   to reach; per the task's explicit witness instruction the joint
   concrete witness is the 64-entry table plus the `7 ↦ 49` probe
   point.
3. "The single-expression fragment lane 111 accepts" had no code in
   this tree when the lane started; the fragment boundary (above) is
   lane 121's, documented in the module header and `CUTS:`. (Superseded
   in the merge: lane 111's `konstanten.rs` pass now owns the fragment
   refusals K190-K194, and the printer covers the accepted arms.)
