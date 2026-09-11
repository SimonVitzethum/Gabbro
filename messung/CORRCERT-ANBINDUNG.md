# Correspondence call-site threading (p20)

Base: `2dc02ad`. Branch: `p20-ziel`. Status: landed.

Every figure below stands inside a plain code block next to the command that
prints it. No figure here was taken on trust. The recompute section (§7) lists
each command; the outputs beside them are the outputs those commands produced
on this worktree.

## 1. The gap

Two certificate modules stood without a call site in the emit path:

- `corrcert.rs` (lane 147) collected per-run correspondence rows
  (`CorrSite`, `CorrCert`, the four checkable legs) but was, in its own words,
  "inert: collected by nothing".
- `certemit.rs` (lane 139) printed derivation certificates per checked
  expression (`emit`) but nothing in the pipeline ever called it.

The Lean side (`grammatik/Grammatik/Erhaltung.lean` §1, read-only reference)
specifies the certificate and the four legs; the recomputer that checks it is a
later program (cut C1). This lane threads the recording half to the call site:
every emission can now return its certificate beside the C.

## 2. The hook point: one call site, not one per walk

The emitter lowers through twenty walks. Threading a builder parameter through
all twenty would touch every walk signature — twenty chances to forget one, the
same class as the 78 holes behind `unterbloecke`. The gate (`ohne_gatter`) set
the precedent: a filter in front of the emitter, not a branch inside it.

So the call site is one function beside the generator, not a change to it:

```
crates/gabbro-check/src/emit.rs, after `emittiere_mit`:
`emittiere_mit_corr(baum, absagen, bau) -> (String, CorrCert)`
```

It reads the same gate-filtered tree the generator lowers (gated items owe no C
and no row), runs the unchanged `emittiere_mit` on it, then walks the tree once
in lowering order and records one row per item whose top-level C shape is one
of the 19 named forms (`korr_form`, §4). The C string is the generator's own
return value — byte-identity is structural, and a test pins it (§7, figure 1).

The obligation convention is the row index: `gabbro_site == c_site ==` position
among the rowed items, so the recomputer's list is `0 .. rows`. Site ids stay
plain numbers; binding them to source spans is the recomputer's job — the Lean
`CorrSite` doc says so word for word, and this lane keeps the same boundary.

## 3. The `certemit` call site: one certificate per folded const

`konst_zertifikate(baum)` walks the tree and emits, for every `const` whose
value the emitter folds itself, the `certemit` certificate over
`CertExpr::Lit`: the exact value with the exact range, beside the `#define` the
Konst arm writes. The boundary is the folder's (`konst_zahl` folds a `Zahl`
literal and nothing else):

- covered: `const K : u32 = 3;` → term `(.lit 3)`, claimed `[3,3]`.
- not covered: float consts, `u64::max` words, `konstwert`-folded names. Their
  source spelling is not a literal, and a `Lit` certificate over them would
  certify the emitter's reading instead of the checked expression.

`certemit::emit_json` is the one-call form the call site uses
(`emit` then `to_json`); `Certificate::to_json` is the machine-readable sidecar
rendering beside the human-readable `render`. Ranges that need checker context
(`var` against a de Bruijn context, `glob`/`slot` against the declared world,
`div` side conditions against M1 ranges) need `lib.rs` wiring and belong to the
follow-up lane named in §6 — the emitter certifies what it folds, nothing more.

## 4. The threading table

Every `ItemArt` variant stands here exactly once: the form its emitting arm
demonstrably writes, or the reason it earns no row. Arm references are
`emit.rs` line numbers on this base.

| item | row | evidence |
|---|---|---|
| `Konst` | `literal` | `#define N lit` (1738–1783) |
| `Statisch` | `statisch` | static storage (1853) |
| `Tabelle` | `statisch` | table storage via `tabelle()` (1830) |
| `Accumulates` | `statisch` | one cell per core, static duration (2075) |
| `Atomic` | `atomar` | `_Atomic T name;` (2157) |
| `Lock` | `extern` | prototypes only (2250) |
| `Rcu` | `extern` | prototypes only (2379) |
| `Funktion`, `spec` | none | emits nothing (early return beside `funktion`) |
| `Funktion`, `asm` body | `asmEins` | one `__asm__ __volatile__` block (6273) |
| `Funktion`, `-> never` | `noreturn` | `_Noreturn` on the prototype (6016) |
| `Funktion`, bodyless foreign | `extern` | prototype and nothing else (6262) |
| `Funktion`, defined block body | none | a body is statements — booked (§6) |
| `Typ`, `Format`, `Device`, `Reason` | none | declarations whose shape is not among the 19 — booked against the open ruling table (§19.4), not guessed |
| `Check` | none | check bodies are definitions plus statements — same booking |
| `Walk`, `Entry`, `Entrust`, `Boot` | none | dispatch/startup shapes are not among the 19 — booked, not guessed |
| `Modul`, `Use`, `Assume`, `Axiom`, `Gruppe`, `Concurrent` | none | scaffolding or ghost: no C site, no row |
| `State` | none | refusal: no C site, no row |

Precedence inside `Funktion` is body first (`asm` beats `never` beats
prototype-only beats block body): the row names the shape the arms write, and
the body is what the arms write first. A refused item keeps its intended row;
the refusal travels in `Absagen`, and a refused unit's C is not shippable
anyway — rows record the lowering intent, diagnostics record the failure.

## 5. The sidecar

`CorrCert::to_json` renders rows with the Lean field names word for word
(`gabbroSite`, `cSite`, `form`), so rows compare equal across the boundary.
`CorrCert::sidecar_path` maps `<stem>.c` to `<stem>.corrcert`, mirroring
`kostenledger::sidecar_path` — one convention for both sidecars: beside the C,
never inside it. The word-level recorder `CorrCertBuilder::aufzeichnen_wort`
parses Lean-spelled form words at the boundary; an unknown word records no row
and returns `false` — never a silent pass.

## 6. What stays booked (not forgotten)

- Statement- and expression-level rows (`zuweisung`, `wenn`, `ruf`, …): thread
  the builder through the body walk in `funktion()` — one function, not
  twenty. Until then a defined block body earns no item row by construction.
- Checker-side ranges for `certemit` (`var`/`glob`/`slot`/`div`): need the M1
  range context threaded to the call site, which is `lib.rs` wiring and belongs
  to another wave.
- Declaration shapes beyond storage, atomics, literals and prototypes: open
  against the §19.4 ruling table (30 open forms); a ruling names them, this
  lane does not guess them.

## 7. Recompute

Server down; all runs local after a `free -g` gate (31 total, 11 available —
a measurement, not a hope). Scoped to `gabbro-check` with `--no-fail-fast`;
no full test, no abnahme.

Figure 1 — the new call-site tests (6 of 6):

```
$ cargo test -p gabbro-check --no-fail-fast --lib korr_anbindung
running 6 tests
test emit::korr_anbindung::konst_zertifikate_tragen_exakte_bereiche ... ok
test emit::korr_anbindung::reine_typen_einheit_hat_leeres_gueltiges_zertifikat ... ok
test emit::korr_anbindung::zeilen_tragen_form_und_ordnung ... ok
test emit::korr_anbindung::asm_und_noreturn_tragen_ihre_form ... ok
test emit::korr_anbindung::c_ist_mit_und_ohne_zertifikat_gleich ... ok
test emit::korr_anbindung::beispiel_67_traegt_asm_zeilen ... ok
test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 128 filtered out
```

Figure 2 — the scoped suite stays green (lib line; every integration target
likewise `ok`, zero failed):

```
$ cargo test -p gabbro-check --no-fail-fast
test result: ok. 134 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
...
```

Figure 3 — the certificate a run emits (micro-unit: const, static, lock, plain
function; asserted byte-for-byte by `zeilen_tragen_form_und_ordnung`):

```
{"sites":[{"gabbroSite":0,"cSite":0,"form":"literal"},{"gabbroSite":1,"cSite":1,"form":"statisch"},{"gabbroSite":2,"cSite":2,"form":"extern"}]}
```

Figure 4 — the const derivation beside it (asserted byte-for-byte by
`konst_zertifikate_tragen_exakte_bereiche`):

```
{"term":"(.lit 3)","claimed":[3,3],"sides":["lit 3: exact (3, 3) -- HOLDS"]}
```

Figure 5 — the probes rechecked leg by leg (all eight files: the four
`korr-*` fixtures plus the four new `p20-*` ones; the script recomputes the
four legs from the rows and compares against each file's `erwartet`):

```
$ python3 -c "<leg recomputation over messung/proben/corrcert/*.json>"
PASS korr-fremd.json {'vollstaendig': False, 'geordnet': True, 'geschlossen': True, 'ohne_extra': False, 'gueltig': False}
PASS korr-ok.json {'vollstaendig': True, 'geordnet': True, 'geschlossen': True, 'ohne_extra': True, 'gueltig': True}
PASS korr-ungeordnet.json {'vollstaendig': True, 'geordnet': False, 'geschlossen': True, 'ohne_extra': True, 'gueltig': False}
PASS korr-unvollstaendig.json {'vollstaendig': False, 'geordnet': True, 'geschlossen': True, 'ohne_extra': True, 'gueltig': False}
PASS p20-anbindung-fremd.json {'vollstaendig': False, 'geordnet': True, 'geschlossen': True, 'ohne_extra': False, 'gueltig': False}
PASS p20-anbindung-leer.json {'vollstaendig': True, 'geordnet': True, 'geschlossen': True, 'ohne_extra': True, 'gueltig': True}
PASS p20-anbindung-ungeordnet.json {'vollstaendig': True, 'geordnet': False, 'geschlossen': True, 'ohne_extra': True, 'gueltig': False}
PASS p20-anbindung-voll.json {'vollstaendig': True, 'geordnet': True, 'geschlossen': True, 'ohne_extra': True, 'gueltig': True}
ALL PASS
```

(The full recompute script is the `python3 -c` invocation recorded in the lane
log: it parses each probe, recomputes `vollstaendig`/`geordnet`/`geschlossen`/
`ohne_extra`/`gueltig` over the 19 Lean-spelled forms, and diffs against
`erwartet`.)
