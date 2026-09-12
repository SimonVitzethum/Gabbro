# MUSE-REPORT-91: library function declaration with payload type (lane E2)

Branch `muse/91`. Rust + Lean lane. Last `./lean-bau` result line:
`Build completed successfully (54 jobs).` Last `./cargo-pruef`:
`== exit 0; failing tests: 0`.

## What was built

The declaration side of run-time library calls (`PLAN-ERWEITUNG.md` §6,
lane E2): a library module declares a run-time function with a contract
and a payload type, and `@lib#f(args) { region }` resolves against it and
is checked exactly like an ordinary call -- then refused with the new
translation diagnostic until the translator exists (lanes E3/E5).

Exact surface (designed in `SYNTAX.md` §6/`§7.1` first, after the `kw.rs`
entries and the `zaehle-wortschatz` mark moved):

```gabbro
pub library fn kernel(n : u32) -> u32 payload KernelTab
    requires n <= 1024
    ensures result == n
    effects { pure }
    costs <= 8 ops
{
    return n;
}
```

Two deviations from the task's `e.g.` sketch, both deliberate and both
documented in `SYNTAX.md` §7.1: (1) the declaration carries a Gabbro body
(`P044` refuses `;`/`= pred`/`= asm`) -- a bodyless `library fn` would be a
foreign promise, exactly what §0c stands against, and the hull check would
have nothing to walk; (2) clauses keep the E4 fixed order (`payload`
behind the signature, then `requires` first) -- the sketch's
`effects`-before-`requires` contradicts decision E4.

### Rust, exact new names

- `gabbro-syntax/src/kw.rs`: `Library => "library", ctx`, `Payload =>
  "payload", ctx` (each with its own reason block; second mark stays 212).
- `gabbro-syntax/src/ast.rs`: `FnDecl.bibliothek: bool`,
  `FnDecl.nutzlast: Option<Pfad>` (a path, so the table may stand in
  another module).
- `gabbro-syntax/src/parse.rs`: `library` prefix in `fndecl` (own slot,
  orthogonal to klasse), mandatory `payload <path>` (`P043`), mandatory
  `Block` body (`P044`); `Kw::Library` wired into the `pub` gate, the
  `item` dispatch and `faengt_item_an`.
- `gabbro-check/src/umgebung.rs`: `module: HashSet<String>`,
  `bibliotheken: HashSet<String>`, `nutzlasten: HashMap<qual_fn,
  (decl_module, payload_text, span)>`; `bibliothek(von, lib, func) ->
  Option<BibliotheksZiel { modul, name }>`, plus `bibliothek_modul` and
  `ist_bibliothek` halves. Resolution uses the same candidate order as
  every other name (own module, enclosing, root, `use` lines).
- `gabbro-check/src/aufrufgraph.rs`: `Knoten.fremd: bool` (set from
  klasse/rumpf at build), `nimm_bibliothek`/`sammle_bibliothek` (resolved
  calls file the callee key plus argument places into `ruft`/`rufe`;
  unresolved file `@lib#f`, matching no key, so the hull turns
  incomplete), `Graph::fremde_in_huelle(start) -> Vec<String>`
  (transitive walk over resolved `rufe` keys with a visited set).
- `gabbro-check/src/m1.rs`: `ruf_aufgeloest(ziel, span, uebergang,
  argtypen, sig)` -- the extracted direct-call tail (`M143`, per-arg
  `passt`, `requires`/`M115`, `ensures` narrowing with foreign booking);
  both `LibraryCall` arms resolve through `Umgebung::bibliothek` and land
  in it (statement arm also kills facts through the resolved qualified
  path; binding arm answers the declared result). `requires_pruefen` now
  takes the callee name instead of `&Ruf`.
- `gabbro-check/src/kosten.rs`: both `LibraryCall` arms resolve and count
  the declared costs from `deklariert` like any call; unresolved keeps the
  unknown remainder with its reason.
- `gabbro-check/src/namen.rs`: `bibliothek_pruefen` replaces
  `library_call_not_checked` (the `lane_e2_checks_calls` hook is gone):
  per declaration `N060` (payload names no table, resolved from the
  declaring module) and `N059` (foreign body in the transitive hull, via
  `fremde_in_huelle`); per call `N058` (resolved -- "library call
  checked; payload translation not implemented") or `N057` (unresolved,
  naming unknown library vs unknown function, incl. the ordinary-function
  note); `N061` (direct call to a `library fn`, in statement, binding,
  `let … else` and contract position; constructors, conversions and
  place-calls never resolve and stay silent).
- New codes `N058`/`N059`/`N060`/`N061`/`P043`/`P044` (each single-site;
  `pruefe-kennungen` green); sentences `namen.bibliothek_ruf/-huelle/
  -nutzlast/-direktruf`, `parser.bibliothek-nutzlast/-rumpf`, all
  `measured`; `N057` sentence narrowed to the unresolved call.
- Effects cross the library edge through the graph (`E008` measured on a
  writing library function under a `pure` caller); `or R` is
  declaration-side automatic (`let … else` over a library call stays
  `P016`); the emitter, Lean channel, certificate and blind-spot table
  keep refusing every library call by name (checker guarantees refusal
  upstream).

### Lean, exact new names (`grammatik/Grammatik/Bibliothek.lean`)

- `BibliotheksFunktion (D)`: `params`, `nutzlast`, `erg`, `schreibt`,
  `gschreibt`. `DientBibliothek D L a`: `aparams = params ++
  [nutzlast]`, `aerg = erg`, effect agreement.
- `args_snoc`, `args_unsnoc` (argument lists split at the payload).
- `bibliotheksruf_ist_ax`: the call obligations (full argument list +
  the five `axiomCall` premises) IFF the library obligations (ordinary
  arguments + payload argument + declared-function effects) -- every
  `hDient` conjunct is used (`hap` transports the list, `herg` the
  result, `hschw`/`hgschw` the four effect premises).
- Witness: `refD` has `Ax := Empty`, so no axiom-shaped theorem admits a
  `refD` witness -- `bibD` copies the reference shape (two-slot `konto`,
  guarding lock, writer storing the cap `100`) and adds the one axiom
  (`[.int 0 10, .int 0 100]`); `bibLib`, `bibDient`, `bibArgs`,
  `bibLast`, the two-step F-run (`bib_erreicht`: lock, writing leaf),
  `bib_schreibt` (slot `0 -> 100`), and `bibliotheksruf_ist_ax_zeuge`
  instantiating all premises jointly on that non-degenerate program.
  CUTS + `#print axioms` close the file (standard
  `propext/Classical/Quot` only).

### Probes (gift numbers from 820, example numbers from 80)

- `beispiele/80-bibliothek-erklaert.gab`: declaration only, fully clean
  (calls can never be clean); emits C accepted by `cc` (`library` and
  `payload` are grammatiktafel-`gesenkt` through it).
- `beispiele/gift/820` (positive: declaration + two calls, exactly
  `N058`+`N058`), `/821` (unknown library, `N057`), `/822` (unknown
  function incl. ordinary-function note, `N057`), `/823` (wrong arg,
  exactly `M135`+`N058`), `/824` (extern in hull, `N059`+`N058`), `/825`
  (payload names no table, exactly `N060`), `/826` (missing payload,
  exactly `P043`), `/827` (bodyless `;`, exactly `P044`), `/828`
  (direct call, exactly `N061`+`N061`). `gift/805` keeps `N057`
  (unresolved) with an updated comment.
- `paesse.rs`: 11 `library_*` tests, exact Fehler sets where they carry
  the claim (`faellt_genau` helper), incl. arity (`M143`), the `E008`
  edge, and the transitive (two-hop) foreign hull.

### Registers

`SYNTAX.md` (vocabulary 226→228 table words, `fndecl` productions, §7
narrowed + new §7.1, excerpt style throughout), `PASSREGISTER.md`
(126/118/312/257 recomputed with lane entry), `TODO.md`/`README.md`/
`DONE.md` (codes, sentences, examples 71→74, gifts 550→569, terminals,
rules), `zaehle-wortschatz` mark 229→231. `pruefe-todo` went 16→3
BEFUNDE; the 3 remaining are verified pre-existing (see below).

## What remains open

- E3 (translator declaration) and E5 (translation stage with
  certificate): `N058` retires when the translator runs.
- `N025` visibility was not extended to library calls: resolution is
  `use`-aware, but a non-`pub` library function called cross-module is
  not refused on visibility grounds. Deferred to E6 linking.
- Contract-position library calls cannot parse (E1 design); contract-
  position DIRECT calls are `N061`. Indirect calls to library functions
  cannot resolve statically and stay under `E009`.
- The binding-position axiom (`Stmt.bindAxiom`, `aerg = some`) needs the
  same split with the result carried -- CUTS in `Bibliothek.lean`.
- No contract discharge in Lean: no theorem connects the axiom answer to
  `ReqAmEintritt`/`EnsAmRueck`.

## What I believe is wrong (in the task or around it)

- The task's sketch (`… costs <= …;`) cannot stand: with `;` the §0c hull
  check is vacuous and the declaration is a foreign promise. The body
  requirement (`P044`) is the load-bearing half of this lane, not a
  restriction on top of it.
- `pruefe-vergabe`'s ratchet is broken at base (23 candidates booked 20,
  80 affected probes booked 68); none of the 23 candidates is an E2 code
  (checked by name). Likewise `pruefe-todo`'s 3 remaining BEFUNDE
  (`Kennzahlen mit Befehl` 89→88 twice, `fettgedruckte` 179→180) are base
  drift: my `SYNTAX.md` adds zero bold-number table cells (16 = 16
  against base) and only additive text. The grammatiktafel ROT pair
  (`abi`, `errors`) and the `pruefe-englisch`/`pruefe-zahlen` reds
  predate this lane (my comment lines contribute zero German-flagged
  lines; verified against the detector word list).
- `MUSE-REPORT-64` (E1) says "`N057` in `BENANNT`" -- the BENANNT list
  lives in `crates/gabbro-check/tests/korpus.rs`, where `N058`-`N061`
  and `P043`/`P044` are now entered beside it.
