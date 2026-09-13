# MUSE-REPORT-164 (lane 164): T2 minimal -- the correspondence certificate for beispiele/104

## What was done

Closed the certificate half of plan item 1 ("close ONE chain first",
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3.1): a Rust printer that emits the
correspondence certificate as a Lean term, and a Lean rechecker with a decidable
validity check and a soundness theorem, both restricted to the forms 104's emitted C
uses. The mechanised chain runs: `gabbro corr-lean` output (pasted as `printed104`)
-> `certOk printed104 = true` by `decide` -> `EndCorr` for both bodies
(`corrCert_sound`) -> callee relation (`ein_fn_cert`) -> the same end-to-end run
conclusion `einzahlen_zeuge` proves by hand (`einzahlen_zeuge_cert`, identical
proposition).

## Real emitted C on this tree (quoted in Korrespondenz104.lean)

`target/debug/gabbro emit beispiele/104-referenz.gab` (exit 0), bodies:

```c
static void einzahlen(Konto *restrict k, uint32_t i, uint32_t b) {
    (void)b;
    k->slots[i].stand = 100;
    lies(k, i);
}
static uint32_t lies(const Konto *restrict k, uint32_t i) {
    return k->slots[i].stand;
}
```

Byte-identical in the bodies to the quote in `CFormenZeuge.lean`. No other forms.

## Rust (new module, CLI, tests)

- `crates/gabbro-check/src/corrlean.rs` (new): `zertifiziere` walks every `impl fn`
  body (descending into modules) and certifies only `einzahlen`/`lies`-shaped bodies:
  `store100` (`param.slots[param].field = 100`), `callLies` (`lies` of two parameter
  args), `retLoad` (return of a slot load), `voidB` (emitter's `(void)x;` for unused
  params, first). Parameter map from the signature in C-local order (`Value`/`pp`/
  `ks`); layout (`n`/`ss`/`off`) from the `Tabelle` decl with `const`-resolved count
  and alias-resolved field sizes. Every other form -- other functions, other
  statements (each `StmtArt` named), other callees, other constants, unresolvable
  counts/sizes -- is a `-- REFUSAL:` line naming the form. With zero refusals the
  assembled `Cert104` literal is printed (pastable as `printed104`); otherwise no
  literal (no truncation: a body is certified whole or refused by name).
- CLI: `gabbro corr-lean <file.gab>` (English-only name, new-command precedent),
  checker-first like `emit`/`zeugnis`; wired in `crates/gabbro-cli/src/main.rs`
  (dispatch arm, `COMMAND_NAMES`, help text) and `crates/gabbro-cli/tests/fahnen.rs`
  (`UNTERBEFEHLE` register -- the lane's second failing test before the fix).
- Tests: 7 in-module (`druckt_104_zeilen_und_layout` pins the exact rows, map and
  layout plus the assembled literal; 6 refusal tests: `let`, `if`, foreign callee
  by name, wrong constant with its value, third function by name, unknown count).
  `./cargo-pruef`: exit 0, 0 failing tests.

## Lean (new file `grammatik/Grammatik/Korrespondenz104.lean`, imported in `Grammatik.lean`)

- Types: `SlotLay104` (layout facts), `CertRow` (`voidB`/`store100`/`callLies`/
  `retLoad`), `Cert104` (both row lists, layout, `vm`/`pp`/`ks` for both bodies).
- Elaboration: `rowCS`, `seqRows`, `einCS` (rows + falling off the `void` end),
  `liesCS` (single return row, `.skip` fallback unreachable under `certOk`).
- Check: `certOk : Cert104 -> Bool` (9 decided equalities).
- Theorems: `rows_of_ok`, `einCS_of_ok`, `liesCS_of_ok` (valid cert elaborates to
  `cEinBody`/`cLiesBody`), `corrCert_sound` (`certOk c = true` -> both `EndCorr`
  plus all six map equalities, so every checked field is load-bearing; built on
  `ein_end`/`lies_end`, i.e. on `cCorr_end` inputs and the T4 row lemmas -- nothing
  re-proved), `printed104` (pasted printer output), `printed104_ok` (`by decide`),
  `ein_end_cert`, `ein_fn_cert` (same shape as `ein_fn`), `einzahlen_zeuge_cert`
  (identical proposition to `einzahlen_zeuge`, proved through the certificate).
- `#print axioms`: `printed104_ok` none; `rows_of_ok`/`einCS_of_ok`/`liesCS_of_ok`
  `[propext]`; the rest `[propext, Classical.choice, Quot.sound]` (the T4 base
  classes). `CUTS:` block at file end. No `CFormen*.lean`/`CSemantik`/`CSpeicher`
  file touched (only imported). No premise quantifies over program syntax, so no
  `_zeuge` companions are owed; `einzahlen_zeuge_cert` is the joint non-degenerate
  instantiation anyway (a written table, a reached run with a memory-changing step).

## Last `./lean-bau` result line

`Build completed successfully (150 jobs).` -- lake exit 0, 0 error lines, whole project.

## Guardian / emission state

- `pruefe-kennungen.py`: ALL PASS. No codes/gifts/examples reserved or added.
- `pruefe-englisch.py`: exit 1 with 2 findings, both pre-existing in untouched lines
  (`lean_g.rs:1349 [darf]`, `main.rs:791 [mit]`); none of this lane's lines appear.
- `pruefe-cformen.py`: RED with 1 unclassified statement in
  `beispiele/38-unveraenderlicher-zeiger.gab` (lane 145's merged example). Not mine:
  this lane touches no emitter, no example, no guardian table; the classifier reads
  emission output my diff cannot change (freshly built binary, so not stale either).
- `MARKE_EMIT`/`MARKE_EMIT_G` untouched; `./emission-pruef` not rerun (no emitter or
  example change, so the count cannot move from this lane).

## What remains open (also in the file's CUTS)

1. `BlockCorr` elaboration of row lists (the `ein_block` judgement) -- the chain to
   the run goes through `EndCorr`, which is what `cCorr_ruf` consumes, so the chain
   closes without it; the row-list induction over `BlockCorr.cons` is future work.
2. Source-derived `ks` values (see below); stage-2 closing theorem; widening to
   further forms/programs (chain count still needs T2 beyond 104).

## Task feedback (one judgment call, nothing believed wrong)

The `ks` VALUES (pinned index `0`) are not in the source -- they are the Lean model's
datum (`refD` fixes the index). The printer proves position and kind and quotes the
value with a `MODEL DATUM` comment; Lean still decides it in `certOk`. Alternatives
(refuse the value and certify nothing, or invent it silently) were both worse; the
report and the file document the boundary. A future call-site analysis could derive
such values from source.
