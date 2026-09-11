# Cost ledger -- the bounds beside the C

Measured: nothing in this file. This file specifies the sidecar that records which
bound covered which function, the procedure that emits it, and the checks the
recomputer runs against it. Every figure below stands inside a plain code block next
to the command that prints it. No figure here was taken on trust.

## 1. The gap

The checker promises numbers and the emitter lowers primitives, and both facts leave
the pipeline as prose. `kosten.rs` holds `costs` against the body (`K001`), `bounded`
against each `retry` (`K006`), `per_pass` against each `forever` pass (`K007`), and
the deadline shape against its clause (`K011`/`K012`) -- but the artefact carries no
record of any of it. A recomputer that wants to re-check a shipped unit has to
re-derive the mapping from the sources: which bound covered which function, which
probe discharged which deadline, how many statements of each primitive went into the
lowering. *A number that only lives in the checking run is a number the artefact
cannot defend.*

The ledger closes the recording half of that gap. It decides nothing: the passes
stay the only place that REFUSES. It writes down, per function, what was promised
and what was counted, in a format the recomputer parses and compares field by field.

## 2. What one row carries

One row per function, qualified name (`modul::funktion`) as the key:

| field | content | source at emission time |
|---|---|---|
| `costs` | promise as written + constant value if readable + input names | `FnDecl::costs`, `Umgebung::konst_wert` |
| `per_pass` | one entry per `forever`, in source order | `Forever::je_durchgang`, `konst_wert` |
| `bounded` | one entry per `retry`, in source order | `Retry::schranke`, `konst_wert` |
| `deadline` | date as written + constant value + `arch` + falsifier name + class | `FnDecl::deadline`, `AnnahmeKlasse` tail |
| `body_ops` | computed body cost in ops, if computable | the same walk `K001` reads |
| `absenkung` | statement counts per primitive (12 fields) | one counting walk over the body |

A bound the checker cannot read as a constant is recorded as `?` with its source
text -- the SAME loud-unknown `K005`/`K011` already report. *Recording `?` is not
admitting defeat; it is naming the opening so the recomputer finds it too.*

The falsifier arrives as `(name, falsifiable)`: `Falsifizierbar(p)` gives
`(p.text, true)`; the `NichtFalsifizierbar` tail gives `("(unfalsifiable)", false)`
and the `assumed` class, so it never looks measured. `costs` counts Gabbro
primitives, `deadline` counts cycles on `arch X` -- different units, no conversion,
and the ledger performs none either.

## 3. The format

Deterministic text, `kosten-ledger v1` header, one `key value` line per field,
`function <name>` opening each row. Field separator inside structured values is an
unescaped `|`; `\`, newline and `|` in free text are escaped (`\\`, `\n`, `\p`).
`render` is byte-stable: same ledger, same bytes. `parse` rejects unknown keys,
blank lines and incomplete rows loudly -- *a sidecar the recomputer cannot read is
a sidecar that does not exist, and saying so is the reader's whole job.*

```
kosten-ledger v1
unit beispiel
function kern::handler
costs 64 + 12 * lenof(msg)|?|msg
per_pass 40|40|-
deadline 1000|1000|x86_64|sonde_frist|falsifiable
body_ops 37
absenkung assign=9 arith=4 load=6 call=2 branch=1 traverse=1 retry=0 forever=0 locks=0 observes=0 exchange=0 count=0
function kern::wartet
costs -
bounded NCORES * 8|64|-
deadline -
body_ops ?
absenkung assign=0 arith=0 load=0 call=0 branch=0 traverse=0 retry=1 forever=0 locks=0 observes=0 exchange=1 count=0
```

The reader lives in `crates/gabbro-check/src/kostenledger.rs`: `render`, `parse`,
`Ledger::verify`, `sidecar_path`. The module depends on nothing but `std`, so a
single-file check covers it:

```
rustc --test crates/gabbro-check/src/kostenledger.rs -o /tmp/kostenledger-test && /tmp/kostenledger-test
```

## 4. The ONE hook point

The ledger is emitted BESIDE the C, never inside it: generated C stays
byte-identical. The single call site is the end of `emit::emittiere_mit` in
`crates/gabbro-check/src/emit.rs`, after the C string is final (today the two
lines `aus.push_str(&rumpf);` / `aus`):

```text
    aus.push_str(&rumpf);
    // HOOK (one line, no C touched):
    crate::kostenledger::ablegen(baum, &aus, zielpfad);
    aus
```

`ablegen` (implemented at wiring time, specified here) walks the tree with
`crate::fuer_jedes_item_im_modul`, reads the already-computed numbers, renders
the ledger and writes it to `sidecar_path` -- `<stem>.kostenledger` next to the
`.c` file. The C string is only borrowed, never touched. No `lib.rs` change
belongs to this lane beyond declaring the module; no lowering walk is touched.

## 5. What the recomputer checks

The recomputer re-emits the ledger from the sources and compares with
`Ledger::verify`, which reports EVERY divergence instead of stopping at the
first. Empty output means the artefact matches its record. The comparison is
order-insensitive over functions (a walk order is not a promise) and
order-sensitive within a row (`per_pass`/`bounded` follow source order, which IS
a promise). A version skew is reported before any row, so an old sidecar never
reads as a matching one.

## 6. What this is NOT

* Not a second checker: no refusal is issued from the ledger, and no `K`-code is
  decided here. Two registers over one refusal is `W7`.
* Not a conversion: `costs` (primitives) and `deadline` (cycles on `arch X`) are
  recorded side by side and never held against each other -- a comparison would be
  a conversion lemma wearing a rule's clothes (`kosten.rs`, `K011` block).
* Not a proof: that a `bounded` budget is honest about the world, or that a
  falsifier goes red when the assumption breaks, is discharged by the probe run,
  not by this file. The ledger names the probe so the run can find it.
