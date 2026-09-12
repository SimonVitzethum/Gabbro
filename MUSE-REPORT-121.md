# MUSE-REPORT-121

Lane 121: CONST CERTIFICATE FROM THE SOURCE (follow-up of lane 111).
Rust + Lean lane; branch `muse/121`.

## What I did

Lane 111 is not in this tree (no const-certificate printer and no
hand-written defining equation exist anywhere in it), so I built the
whole path the task asks for:

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
`::funktion_lean`, `::tabelle_lean`, `::zertifikat_lean`,
`::ruf_ausdruck`, `::werte_tabelle`; tests
`gedrucktes_lean_ist_genau_die_uebersetzung_von_quad`,
`jede_operatorfamilie_druckt_ihre_nat_form`,
`verschachtelte_const_rufe_drucken_lean_applikation`,
`nicht_druckbares_ergibt_kein_zertifikat`.
Lean: `KBinOp`, `KUnaOp`, `KExpr`, `KBinOp.eval`, `KExpr.eval`,
`KExprList.eval`, `leerEnv`, `leerFns`, `quadSyntax`, `quad`,
`quad_aus_syntax` (+ `quad_aus_syntax_zeuge`), `dreiPlusVierSyntax`,
`dreiPlusVier_aus_syntax`, `constUmgebung`, `constSyntax`,
`konst_aus_syntax`, `doppelt`, `doppeltFunktionen`, `vierfachSyntax`,
`ruf_aus_syntax`, `quadTabelle`, `quadPruefe`, `quadPruefe_holds`,
`quadTabelle_aus_syntax`.
ZEUGE soundness theorem: `quad_aus_syntax`; witness: the square table
(`quadTabelle`/`quadPruefe`, 64 entries, joint witness
`quad_aus_syntax_zeuge`).

## Last build results

- `./lean-bau`: `Build completed successfully (62 jobs).`
  (`== 0 error line(s) in the COMPLETE output`; Konstanten builds in
  401ms; axioms: soundness/probe theorems `[propext]`,
  `quadPruefe_holds` axiom-free, `quadTabelle_aus_syntax`
  `[propext, Quot.sound]`.)
- `./cargo-pruef`: `== exit 0; failing tests: 0` (all targets green,
  including the new `konstanten` target, 4/4).
- Independent check: the exact expected certificate text extracted
  byte-identically from the Rust test to scratch
  (`$TMPDIR/opencode/quad_cert.lean`) gives
  `== 0 error(s) in the COMPLETE output` under `./lean-probe`, i.e.
  `decide` closes the generated file. The Lean table in
  `Konstanten.lean` carries the same 64 numbers (verified: equal entry
  lists, all `k*k`), differing only in line layout.
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
  diagnostics, poison probes, or examples were needed).

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
3. "The single-expression fragment lane 111 accepts" has no code in
   this tree; the fragment boundary (above) is mine, documented in
   the module header and `CUTS:`.
