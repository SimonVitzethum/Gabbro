# OPUS-F — Races across the link: review E F1 closed, the Rust residue of OFFEN O28

*Opus agent F, 2026-09-26. Worktree `agent-a46ca3195966099b1`, on master `db67a4ba`
(Merge Opus E). SATZKARTE §54 (note), OFFEN O28, sentence `namen.verbund`.*

## 1. Result

| Item | State |
|---|---|
| **F1 (HIGH)**: a read behind an imported head, raced by another thread of the importer, linked green | **closed twice**: per unit (`gabbro check --with`) and at the link |
| O28 (a): threads in BOTH units refused blanket (`N503`) | **judged**: the linked program is checked whole |
| O28 (b): contracts compared as text | **compared as normal-form trees** |
| O28 (c): `gabbro build` does not call the link check | **it does**: every manifest of ≥ 2 units; `gabbro build a.gab b.gab` runs the link check (nothing compiled) |
| Lean | unchanged except one NOT CLAIMED comment line in `Spec.lean` (the F1 sentence, now false, reworded); `GabbroZiel` and `GabbroZielVerbund` untouched |

## 2. F1, per unit (`crates/gabbro-check/src/fusswache2.rs`)

The importer's footprint (`fuss`) was: own contracts, body reads, direct callee contracts. A
body-less callee (an `extern fn` head, hand-written or from `--with lib.gabi`, or an `= asm`
body) contributed its contract roots and -- through `schreibt` -- its declared WRITES, but not
its declared READS. Now:

- `kopf_liest`: the `reads`/`consumes` carriers of every body-less, non-`spec` head (table
  roots, parameters of table type resolved to their table; device registers excluded, the
  E245 boundary) join the head's footprint. So thread-locality, `N301` (write-read across
  starts), the start and child legs (`N457`/`N462`) all see them.
- A new call-site leg under the existing code `N291`: a head's declared read of a carrier
  that is not thread-local, not written by nobody, not signature-guarded, not
  invariant-protected is refused AT THE CALL. A carrier some lock protects is left to `H007`
  at the call boundary (the caller holds the lock, or the head declares `locks L` and the
  exporter's own `H007` holds every access of its body) -- "held at the access" across the
  boundary, the body leg's own exemption.

**The reproduction** (probe 1246, the verdict's program): `gabbro check --with bib.gabi
app.gab` now falls with **`N291` + `N301`** -- exactly the codes the same two modules get in
ONE file (measured: `N291` at `lies`'s body read, `N301` at the `concurrent` line). Positive
twin `rennen-bewacht-*` (the read under the library's lock, `t2` writes under it): clean alone,
links clean.

**Correspondence with Lean.** `lokBedarfB`/`getrenntVB` read `fussOrte (teilP e E₁ E₂ f) f`:
the footprint of an imported function from its OWNER's program. The Rust importer cannot see
the owner's body; the head's `effects` is the owner's summary of it (the exporter's check holds
its body to it, `E010`; the link holds the head to the body, `N503`). So "the head's reads are
the body's reads" is the Rust reading of `teilP` -- and `vm_abgelehnt`'s shape (library reads
unguarded `privB` behind its head, the app writes it) is exactly probe 1246.

## 3. The linked program (`crates/gabbro-check/src/verbund.rs`)

`verbinde_alle(es, absagen)` for N ≥ 2 units: every pair's heads against the bodies
(`verbinde`, `N501`–`N505`, as before), then -- only if no head is stale -- `pruefe_verbund`:

- `verbundtext` composes ONE source: each unit's text in order, every item another text
  already contributes blanked to spaces (byte positions kept, so each refusal maps back to its
  unit by offset). A function's body is kept from its owner and every head of it dropped; any
  other item keeps the copy in a unit's OWN text (not a `--with` preamble); a DIFFERENT second
  copy is kept so the checker names the clash; a module whose items are all blanked is blanked;
  every start (`concurrent`/`entry`/`boot`) of every unit stays. This is `verbinde e E₁ E₂` on
  the surface.
- The composed source is read and checked by EVERY pass (`gabbro_check::pruefe`); each error
  keeps its one-file code, lands in the unit its span points into, and carries a note that it
  was found on the linked program.
- `N516` (new): a module holding surviving items in two units -- no program can be composed,
  the whole-program check does not run (the same rule `gabbro build` applies across a
  manifest).

**Correspondence with Lean.** `SchnittstelleSpec.lok`/`.renn`/`.einzeln` quantify over the
composed hulls `HuelleV`; under `KeinRueckruf` (`N503`, callback) a root's graph in the linked
program IS its composed hull (`huelle_of_reach`). The Rust deciders of those components
(`fusswache2.rs`: `N290`–`N294`, `N300`–`N304`, `N456`/`N457`/`N462`) now run over the linked
program's call graphs with every start of both units. The Rust link therefore refuses at least
what `schnittstelleB` refuses; it checks MORE (every other whole-program pass too), which is
the safe direction and is said in the sentence. The one-unit caveat stays: the Rust checker is
not the Lean Bool.

**Threads on both sides.** The blanket `N503` is gone. Probe 1247: the library's thread writes
the unguarded `konto`, the app's thread reads it through `lies`; each unit is clean alone (each
sees only its own thread); the link falls with **`N291` + `N301`**. Twin `faeden-beide-*`: a
library pool over its own guarded counter, an app pool calling a pure export -- links clean
(before: `N503`).

**Both F1 fixes are independent.** Measured with `fusswache2.rs` reverted to HEAD (the rest of
the branch in place): probe 1246's `check --with` is clean again (the harness falls on
`allein-erwartet`), and `gabbro link` still refuses it with `N291` + `N301` from the linked
program.

## 4. Contracts as trees (O28 (b))

`normalform(x)`: the syntax tree's `Debug` form with every `Span` replaced by `_` and every
redundant `Klammer` around a predicate or expression removed. `requires`/`ensures` are compared
as SETS of normal-form conjuncts (top-level `&&` and the clause list flattened); effects as sets
of normal-form effect nodes; signatures by parameter names, type trees, result and reason.
So `requires (x > 0), (x < 5)` equals `requires x < 5 && x > 0`, `(x + 1)` equals `x + 1`,
`0x10` equals `16`; `(1 + 2) * 3` stays different from `1 + 2 * 3` (tested). Not claimed: a
semantically equivalent but structurally different contract (`5 > x` for `x < 5`) is still
refused -- one contract per function, as in `Verbindbar`.

## 5. The build (O28 (c), `crates/gabbro-cli/src/bau.rs`)

- A manifest with ≥ 2 units: after the per-unit loop (built or current), the units are linked
  -- each unit re-read with the preamble it was built with -- via the shared core
  `main.rs::verbinde_quellen` (the one `gabbro link` uses). A refused link makes the build red
  (`REFUSED link: …`, exit 1); the C already written stays, and the link runs again on every
  build because it is a property of the set.
- `gabbro build a.gab b.gab …` (no manifest): each file is a unit, checked against the
  interfaces `gabbro abi` writes for all the others; the link check runs; the output says
  NOTHING was compiled. Tested on 1247 (exit 1, `N291` + `N301`) and `faeden-beide` (exit 0).
- `gabbro link` takes N ≥ 2 units (`--with` in front of every unit after the first).

## 6. Probes and tests

| probe | pair | alone | link |
|---|---|---|---|
| 1246 `kopf-liest` | F1 reproduction | importer falls: `N291` `N301` | `N291` `N301` |
| 1247 `rennen-verbund` | threads in both units race | both clean | `N291` `N301` |
| 1248 `modul-doppelt` | module `werk` in both units | both clean | `N516` |
| `rennen-bewacht-*` | guarded read behind the head | clean | links |
| `faeden-beide-*` | threads in both units, nothing shared | clean | links |

Harness `crates/gabbro-cli/tests/verbund.rs`: probes are now pairs `NNNN-…-bib.gab` +
`NNNN-…-app.gab` (or a stale `.gabi` against `tabelle-*`), `-- link-erwartet:` takes a code
list, `-- allein-erwartet:` pins an importer that must fall alone. New tests
`die_zwillinge_verbinden_sauber`, `der_bau_aus_quelldateien_verbindet`; snippet tests in
`verbund.rs`: two-sided threads judged, a cross-unit race on the linked program, the composed
text keeps every body and start, `N516`, contracts as trees.

## 7. Measurements

- `free -g` before the builds: 31 GB total, 17–18 GB available.
- **Corpus diff**: all 932 files of `beispiele/*.gab` + `beispiele/gift/*.gab`, codes per
  file (errors and hints), branch vs. `fusswache2.rs` at HEAD: **identical**. The new `N291`
  call-site leg fires on no corpus file.
- `./cargo-pruef`: baseline (master) **1353 passed, 0 failed, 1 ignored**; final **1359
  passed, 0 failed, 1 ignored**.
- `./lean-bau`: **exit 0, 0 error lines, 324 jobs** (only a comment in `Spec.lean` changed).
- `./emission-pruef`: **exit 0, ALL PASS** (42 pierced, 304 of 304 translate). No emitter
  change; `MARKE_EMIT*` not touched, no delta.
- Text guardians: `pruefe-kennungen.py` ALL PASS; `pruefe-saetze.py` exit 0 (`N516` has its
  sentence); `pruefe-englisch.py` and `pruefe-todo.py` exit 1 **on master already** --
  measured with this branch's files swapped back to HEAD: the same three broken ratchets
  (7965 German comment lines vs 7949 booked, 37 vs 26 feeders, 5 vs 2 sink messages) and the
  same 16 TODO findings; this branch adds none.

## 8. What stays open (OFFEN O28)

- An independent review of this branch and of Opus E's Spec diff.
- No certificate for a linked program (the exporter exports one `Einheit`).
- Contracts: no semantic equivalence, no refinement across the boundary.
- The C link step (linked C refines linked G) -- TODO §2 "The linking theorem".
- Line numbers of refusals in a unit read with a `--with` preamble count the preamble lines
  (pre-existing in `gabbro link`, unchanged).
