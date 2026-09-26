# OPUS-E — Linking separately compiled units under the same hardware assumptions

*Opus agent E, 2026-09-26. Branch in worktree `agent-a11192d63a8d21952`. SATZKARTE §54,
OFFEN O28.*

## 1. Result

- **Lean.** `Zielsatz/Spec.lean` gains a SECOND statement, `GabbroZielVerbund`, proved as
  `gabbro_ziel_verbund` (`Zielsatz/Verbund.lean`). `#print axioms`: `propext`,
  `Classical.choice`, `Quot.sound` (also for `gabbro_ziel`, unchanged). No `sorry`, `admit`,
  `axiom` or `native_decide`.
- **Rust.** `gabbro link|verbinde [--with L.gabi]… a.gab b.gab`
  (`crates/gabbro-check/src/verbund.rs`), refusals `N501`-`N505`, sentence `namen.verbund`.
- **Build.** `./lean-bau` green (324 jobs, after merging master with Opus D and lane 260).
  `./cargo-pruef`: see §7.

## 2. The statement, and the Spec diff

`GabbroZiel` is **word for word unchanged**; no definition above the new block moved. Added
at the end of `Spec.lean`:

```
GabbroZielVerbund :=
  ∀ C D E₁ E₂ e fs ls cs,
    C.akzeptiert E₁ … = true → C.akzeptiert E₂ … = true   -- (a) each unit ALONE
    → Verbindbar E₁ E₂                                     -- (a) one link declaration
    → SchnittstelleSpec fs e E₁ E₂                         -- (a) the link check
    → NutzerTeil e E₁ → NutzerTeil (!e) E₂                 -- (b) each user, own bodies only
    → E₂.Q = E₁.Q                                          -- (c) the SAME hardware assumptions
    → HardwareAnnahmen O E₁.Q
    → Laufzeit (verbinde e E₁ E₂) sp init                  -- (d) the linked runtime
    → ∀ lebt0 K, FadenErreichbar … K → ZielF (verbinde e E₁ E₂).P.mitRuhe … K
```

- **Model.** Both units are `Einheit D` over ONE link declaration `D` (the union of their
  declarations — what `gabbro abi`/`--with` builds). `e` says who owns a function. A unit's
  program holds its own bodies and LEAF placeholders for the other unit's functions
  (`Platzhalter`: the `extern fn` head, calling nothing). `Verbindbar`: the two units agree on
  every `requires`/`ensures`, table invariant, lock invariant and the initial memory — the
  importer relies on exactly the exporter's contract. `verbinde e E₁ E₂` takes each body from
  its owner and both units' starts and run-time roots.
- **The link check** `SchnittstelleSpec` (decided exactly by `schnittstelleB`,
  `schnittstelleB_iff`): leaves; `KeinRueckruf` (an imported function's graph stays in its
  owner); and the three WHOLE-PROGRAM components of `AkzeptiertSpec` — thread-locality,
  write separation, pool safety — re-decided over the **composed hulls** `HuelleV` (a root's
  graph inside its owner, then inside the owner of every function of the other unit it
  reaches). This is how the interface carries the footprints: a unit alone sees neither the
  other unit's threads nor a read hidden behind an imported head.
- **Conclusion** is `GabbroZiel`'s own `ZielF`, so race freedom and lock discipline ACROSS
  units, spawned threads, joins, the weak-memory leg `schwach` and (after the merge) Opus D's
  invariant legs all hold on the linked program.

**NOT CLAIMED line replaced.** "linking of separately compiled units" became: what is
claimed (`GabbroZielVerbund`), and, not claimed, units with DIFFERENT hardware assumptions,
callbacks through an import, an importer relying on a contract other than the exporter's
(weaker or stronger), dynamic loading, ABI-level linking of foreign C, the C link step.

**Embedding lemmas** (review of the diff): `verbinde_leer` — linking with a partner that owns
and starts nothing is the unit itself; `verbinde_akzeptiert`, `nutzerTeil_verbinde` — the
linked unit is accepted by the concrete checker and carries the restricted duty, so chains
link by iteration. `GabbroZiel` itself is untouched, so every earlier theorem stands.

## 3. Why it holds

`gabbro_ziel_verbund` shows the linked unit meets every premise of `GabbroZiel` and applies
it with `akzeptiert_pruefer`:

- `akzeptiertSpec_verbinde`: per-body components (fragment, lock floors, answer sites,
  lock-invariant places, roots) are each owner's verdict, because a body's footprint and
  features depend only on its own text and the shared contracts
  (`endblockOrteP_mitRumpf`, a mutual structural induction over the syntax;
  `fussOrteG_teil`, `kandB_teil`). Closed call graphs: `abg_verbinde`, from each owner's
  closure, the leaves (`kante_teil`) and a new general lemma **`reachB_ruft`** — the computed
  graph `reachB` is closed on a complete member list (`erreichB_stabil`: the fixpoint is
  reached within `fs.length` rounds, a counting argument). The linked graph of a root lies in
  its composed hull (`huelle_of_reach`, from `KeinRueckruf`), so the link check's three
  components transfer.
- `nutzerPflicht_verbinde`: `KoerperGutS`/`InvGutS`/`InvGutGrund` depend on the body of `f` and
  the contracts only (`koerper_mitRumpf2` …), so each owner's duty is the linked duty; starts
  per unit over the shared initial memory.
- (c): `E₂.Q = E₁.Q`. (d): a premise on the linked unit.

## 4. Witnesses (`Zielsatz/VerbundZeuge.lean`)

| name | what |
|---|---|
| `vz_ziel`, `vz_lauf_zeuge` | library owns `wrap`/`lies`/`einzahlen` (`einzahlen` writes the lock-guarded `konto`; `wrap` exports `ensures konto[0] == 100`), app owns `haupt() = locks { wrap() }` declared twice. Each unit accepted alone (`by decide`), `schnittstelleB = true`, each user proves only its own bodies, `Q` equal. `ZielF` on every reachable thread machine; a run where both app threads step and thread 0 holds the lock |
| `vz_huelle_schreibt` | non-degenerate: the app's OWN graph does not reach the writer (`reachB vzApp … zEin = false`), the composed hull does |
| `vz_verbinde_gleich` | the linked unit is fix lane F10's pool `zPool` |
| `vm_abgelehnt`, `vm_abgelehnt_spec` | refusal, footprints: the library's `pruefeA` reads unguarded `privB` behind its head; the app's `hauptB` writes it. Each unit accepted alone; the link Bool false (`lokBedarfB` true, `getrenntVB` false); the whole-program checker also refuses the linked program |
| `vz_vertrag_zu_schwach` | refusal, contract: the library exports `wrap … ensures true`, the app relies on `konto[0] == 100`: library accepted alone, `¬ Verbindbar` |

## 5. Rust: `gabbro link`

Each unit is checked alone (`--with` preambles in front of the SECOND unit, as its own check
had it); a unit with errors links nothing. Then every `extern fn` head one unit relies on is
held against the other unit's body:

| code | refuses |
|---|---|
| `N501` | signature (params, result, error channel) differs; import of a non-`pub` function; a body in both units; a shared exported declaration (table, lock, type, …) that differs |
| `N502` | `requires`/`ensures` conjunct sets differ (a too-weak export is named as such) |
| `N503` | `effects` differ; the exporter's hull calls back into the importer; threads started in BOTH units |
| `N504` | the head promises a smaller `costs` bound than the exporter declares |
| `N505` | an `assume`/`axiom`/`device`/`profile` or a bodiless foreign `extern fn` both units name, stated differently |

**Probes** (`messung/proben/verbund/`, numbers from the reserved gift range): positive pair
`tabelle-bib.gab` + `tabelle-app.gab` links clean against the interface `gabbro abi` writes;
stale interfaces `1241`-`1244` (`N501`…`N504`) and the app `1245` (`N505`). Each importer
checks CLEAN alone against its view; `gabbro link` falls with exactly the probe's code
(`crates/gabbro-cli/tests/verbund.rs`). They are not `beispiele/gift/` files on purpose: a
link probe is two units, each clean alone, and the gift harness expects one file to fall
alone. Snippet tests in `verbund.rs`: callback `N503`, threads on both sides `N503`, body in
both units `N501`, unexported import `N501`, differing table `N501`, differing foreign
function `N505`, and the silent positive cases. **Corpus diff:** no existing corpus file is
touched and no per-unit pass changed, so `gabbro check` verdicts on `beispiele/` are unchanged
by construction; `pruefe-akzeptiert-diff.py` compares one unit's Rust verdict to the Lean
Bool and has no two-unit input, so it does not apply (not run). Certificates (Opus C): no
exported program changed; `zertifikate.rs` unaffected.

## 6. What is NOT done (OFFEN O28)

- No independent review round of the Spec diff yet.
- Rust does not port the composed-hull race check: a pair with threads on BOTH sides is
  refused (`N503`), not checked. Contracts compared as normalised text.
- Units are single files (plus `--with`); `gabbro build` does not call the link check; no
  certificate for a pair.
- The C-level link step (linked C refines linked G) — TODO §2 "The linking theorem".

## 7. Measurements

- `free -g` before builds: 31 GB total, 11–15 GB available.
- `./lean-bau`: exit 0, 0 error lines, 324 jobs (after the master merge).
- `./cargo-pruef` before the merge: 1347 passed, 0 failed, 1 ignored; after the merge and the
  records (commit 98de28da): **1353 passed, 0 failed, 1 ignored**.
