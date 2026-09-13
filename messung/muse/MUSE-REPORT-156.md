# MUSE-REPORT-156: lock invariants in the language (lane 156)

Surface + checker + export for `lock L protects { ... } invariant <pred>`,
the language side of `SperrInv` (`grammatik/Grammatik/SperreSem.lean`).

## What was built

**(1) Surface syntax.** `lockdecl` carries an optional trailing clause:

```ebnf
lockdecl = [ "pub" ] "lock" ident "protects" "{" placelist "}"
           "rank" constexpr [ "held" "<=" constexpr "ops" ]
           [ "shared" "held" "<=" constexpr "ops" ] [ "masks" ident ]
           [ "invariant" pred ] ";" ;
```

No new word: `invariant` is vocabulary already (loops, tables, groups) and
keeps one job -- a predicate that must hold across steps. `pruefe-wortschatz`
still reads 240/240, the EBNF branch 177 rules / 0 open. Documented in
`dokumente/SYNTAX.md` (production + attribute row naming `SperrInv`,
`N275`-`N277` and obligation kind `L`).

**(2) Parser + AST.** `LockDecl::invariante: Option<Pred>`
(`crates/gabbro-syntax/src/ast.rs`), parsed in `lockdecl()` after `masks`
(`parse.rs`), read as a CONTRACT via `vertrag()` so `old`/`result` are words
there and the checker refuses them by name instead of misreading `old(...)`
as a call. The `vertrag()` doc list of contract positions names the lock
invariant (eight callers). Every pre-existing `lockdecl` parses unchanged.

**(3) Checker** (`crates/gabbro-check/src/sperrinv.rs`, wired behind
`geteilt` in `lib.rs`, no pass number of its own -- a rule of the lock
column): `N275` (a read outside the `protects` set -- `protects` entries
resolve carrier-or-field to carrier, `beispiele/10` protects field names),
`N276` (impure: `old`, `result`, any call incl. conversions/`Some`/`None`,
`Held`, reason/function values, quantifiers, membership, reachability,
`count`, array literals), `N277` (a name that is neither a protected carrier
nor a constant -- a lock declaration binds nothing). `N278`/`N279` stay
reserved (writer side, release shape). Satz `sperren.invariante` in
`saetze.rs`.

**(4) Export** (`lean_g.rs`): `LockModel::invariant`, translators
`tr_sinv_pred`/`tr_sinv_cmp`/`tr_sinv_val` (table-slot reads with literal
indices, inlined constants, `+`/`-`/`*`, comparisons; `==`/`!=` direct,
`<`/`<=` under `decide`), gate `check_locks`, and the printed family `gS :
SperrInv gD` (`orte` = `protects` set, `inv` the snapshot predicate,
`fun _ => true` where a lock carries none) plus per-lock-per-carrier
`List.elem … = true` by `decide` in both directions (carrier in `orte`,
guard in `braucht`). The emitted file imports `Grammatik.SperreSem`.

**(5) Obligation.** `pflichten::Art::Sperrinvariante`, letter `L`, one line
per lock invariant named by its lock (`K :: invariant`), printed in
`gabbro pflichten` beside the `ensures` lines with a header that adds up
over nine kinds (balance + E1-inside-the-tool extended). `gabbro prove`
sees it through the same register; `gabbro pflichten --lean` refuses it by
kind under the shared `Invariant` reason (`duty_1 L K :: invariant --
refused (table-invariant)`).

**Probes.** Positive `beispiele/118-sperrinvariante-erhaltung.gab` (two
functions over two carriers under one lock, conserved sum `== SUMME`,
signature-held à la `beispiele/01`) and `beispiele/119`
(single carrier bound through `locks` blocks à la `beispiele/10`); poison
`beispiele/gift/940` (`N275`), `941` (`old`, `N276`), `942` (call, `N276`),
`943` (unknown name, `N277`) -- each falls with its code ALONE. Emitted C of
both positives is `cc -Werror`-clean.

**Lean.** `grammatik/Grammatik/ExportSperre.lean` (new): the `gabbro lean-g`
output for `beispiele/118` pasted verbatim (minus its two import lines),
plus `gS_orte_K : gS.orte GLock.K = [.inl GTab.A, .inl GTab.B] := rfl`,
CUTS, `#print axioms …gS_orte_K` =
`[propext, Classical.choice, Quot.sound]`. `import Grammatik.ExportSperre`
appended to `grammatik/Grammatik.lean`. No TARGET statement and no `ZEUGE`
line in this task, and `gS_orte_K` has no syntax-quantified premises, so
rule 13 needs no witness.

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. new `tests/sperrinv.rs`
  -- 3 tests -- and 4 new `tests/lean_g.rs` tests; `N275`-`N277` added to
  `tests/korpus.rs` `BENANNT`).
- `./emission-pruef`: `== exit 0`.
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the COMPLETE
  output`. `./lean-probe grammatik/Grammatik/ExportSperre.lean`: 0 errors.
- Guardians: `pruefe-kennungen` ALL PASS; `pruefe-saetze` green once the new
  files are tracked (it reads `git`-known files -- see below);
  `pruefe-wortschatz` 0; `pruefe-vergabe` 0; `pruefe-syntax.sh` EBNF ALL PASS;
  `zaehle-lean.py` prints the `L` row (`L 2`, census adds up).
  `pruefe-manifest` (exit 1) and `pruefe-zahlen` (exit 1) are red at baseline
  too -- manifest output byte-identical with and without this lane, zahlen
  drops from 27 to 25 BEFUNDs, none naming this lane's artifacts. The three
  `Warnungen` build warnings (`nl`, `t`, `DeclInfo`) are pre-existing.

## What remains open / cuts

1. The release duty is recorded only -- no per-`locks`-block checking.
2. Quantifiers and option constructors are refused (`N276`); an invariant
   over ALL slots of a table is unwritable. The export fragment additionally
   excludes globals, pointer bases, non-literal indices and division.
3. `N278`/`N279` reserved, not refused.
4. The `L` duty shares the lean reason tag `table-invariant` (no constructor
   was added to `programmlogik/Gabbro/Coverage.lean` -- this lane touches no
   `.lean` file but `ExportSperre.lean`).

## What I believe is wrong (findings)

1. **`Decidable (x ∈ l)` fails over sum carriers in this toolchain.**
   Measured 2026-09-13: `(1 ∈ xs)` decides over `List Nat`, but
   `(Sum.inl T.a ∈ ys)` with `ys : List (T ⊕ Empty)` does not, although
   `DecidableEq (T ⊕ Empty)` and `BEq (T ⊕ Empty)` both synthesize and
   `List.elem x l = true` decides over the same lists. Hence the guard half
   travels as `elem`-decides, and no bare `∀ L c, …` guard universal is
   stated. "Checked by `decide` where decidable" is honored to the letter;
   the letter is narrower than the task's sentence suggests.
2. **A stash with mixed tracked/untracked files plus a guardian that builds
   (`pruefe-syntax.sh` "Warnungen") silently replaced `target/` with a build
   of the stashed sources.** Symptoms: `P001` on the new clause in a binary
   that had just passed everything. Recovery is one rebuild, but the failure
   looks exactly like a broken lane. Do not stash mid-lane; if you must,
   rebuild before measuring.
