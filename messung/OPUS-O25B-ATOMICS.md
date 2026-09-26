# Opus lane O25b — the atomic rely: unguarded atomic communication in the goal theorem

*2026-09-26. Branch `opus/o25b` (worktree `.claude/worktrees/o25b`), merged with master at
`342f6ace` (Opus D invariants, lane 260, Opus E/F linking). SATZKARTE §55; OFFEN O25, O17
narrowed; TODO §2 updated.*

## 1. Verdict

**`Spec.lean` is NOT changed.** Everything below is proved standalone. The Spec diff was not made
because the thread machine (`ZielF`) and the linked statement (`GabbroZielVerbund`) are not yet
re-proved with the rely: a diff now would drop legs `GabbroZiel` has today, and the task rules
out a partial diff.

**What is proved (the headline):** `gabbro_ziel_atomar` (`Zielsatz/AtomarZiel.lean`) — in the
shape of `GabbroZiel`: for every checker for the rely (`PrueferX`, soundness target
`AkzeptiertSpecX`), every unit it accepts, the user's logic WITH the rely (`NutzerPflichtA`),
the named hardware assumptions and the runtime's start (`Laufzeit`, idle root), for every
assignment of memory orders: at every machine W reaches, `ZielAtomar` holds — every leg of
`Ziel` in its form with shared atomics. `gabbro_ziel_atomar_vor`: the premises of `gabbro_ziel`
give the same conclusion (embedding: no unit loses coverage).

`#print axioms`: every new theorem depends on `propext`, `Classical.choice`, `Quot.sound` at
most. No `sorry`, `admit`, `axiom`, `native_decide`.

## 2. The pieces

| # | what | files |
|---|---|---|
| 1 | RMW atomicity as a sub-machine of W: an `exchange` writes directly above the message it read (`RufSchrittWR`); every WR run is a W run and every G run a WR run; **`wr_kein_verlust`**: two `exchange`s of one global never read the same message | `Speichermodell/RMW.lean` |
| 2 | THE RELY: `execStmtHA`/`execEndHA` — every read (`World.lese`) passes through an atomic environment `A` that may change the read carriers of `T` and nothing else (`HavocA`); identity on bodies reading nothing of `T` (`Endblock.execHA_frei`) | `Speichermodell/AtomarSem.lean`, `SperreSemA.lean` |
| 2 | (b) with the rely: `KoerperGutSA`, `InvGutSA`, `InvGutGrundA` (against EVERY environment); `GeteiltA` (atomic, unguarded, not thread-local over the call closure), `LogikPflichtA`, `NutzerPflichtA`; **`logikPflichtA_iff_akzeptiert`**: on every unit `AkzeptiertSpec` accepts, the two obligations are equivalent | `Speichermodell/AtomarRec.lean`, `Zielsatz/AtomarPflicht.lean` |
| 3–5 | the replay with the rely: `KopfSA`/`FadenSA`/`ZielInvSA`, the recorded environment `umweltAusA` keyed by the world after the read events, `akteurSA` over all 70 rules, machine GX (G on a memory agreeing with G's outside the shared atomics `Tg`), **`ziel_ort_atomar`** (`VertragAmOrtG`, `SperrInvG`, `KeinLogikHaltG` over GX) | `AtomarReplay`, `AtomarAkteur`, `AtomarLauf` |
| 6 | **`schwach_ist_gX`**: every W step is a GX step whose presented memory is G's outside `Tg`; **`ziel_ort_atomar_voll`** adds `InvAmOrtG`, `InvAmGrundG`, `StartEndeG`, `KeinStartGrundG` | `AtomarW`, `AtomarInv` |
| 7 | the idle root under the rely (`rumpfHA_mitRuhe`, `logikPflichtA_mitRuhe`) | `AtomarRuhe`, `Zielsatz/AtomarRuheNutzer` |
| 8 | `gx_aus_w`, `ZielAtomarW`, `ziel_atomar_w`; (a) with the rely: `GeteiltV` (shared AND in no contract), `AkzeptiertSpecX` (`fuss := FussSX` over `GeteiltV`), Bool `AkzeptiertX` (`fussWXB`, `vertragsFreiB`), `akzeptiertSpecX_of`, both embeddings from `Akzeptiert`; `ziel_atomar_spec`, `rennfrei_atomar_spec` | `Speichermodell/AtomarZiel`, `Zielsatz/AtomarAkzeptiert` |
| 9 | witnesses (§3) | `Zielsatz/AtomarAkzeptiertZeuge` |
| 10 | `FortschrittG` over GA (`gaInvF`, `fortschrittG_GA`), `fadenSA_bereich`; `ZeitAb` | `AtomarFortschritt` |
| 11 | Opus agent D's four legs over GX: `InvRuheG`, `InvSichtG`, `SperrWechselGX`, `SperrSichtGX` (`invarianten_atomar`) — a GX step differs from a G step only at shared atomics, which no table invariant (tables only) and no lock invariant (guarded carriers only) reads | `Zielsatz/AtomarInvarianten` |
| 12 | `KernHaltGA` (over GA runs, every program), `RennfreiBisGA`; `ZielAtomar`; the idle-root transfer of (a) (`akzeptiertSpecX_mitRuhe`); `PrueferX`, `akzeptiertX_pruefer`, `Pruefer.alsX`; **`gabbro_ziel_atomar`**, **`gabbro_ziel_atomar_vor`** | `Zielsatz/AtomarMasken`, `AtomarAkzeptiert`, `Zielsatz/AtomarZiel` |
| 13 | Rust `N484` (§4) | `crates/gabbro-check/src/fusswache2.rs` |

**`ZielAtomar` vs `Ziel`, leg by leg:** `speicherSicher`, `vertrag`, `sperrInv`, `invRueck`,
`invGrund`, `invRuhe`, `invSicht`, `startEnde`, `keinStartGrund`, `keinLogikHalt`,
`keineVerklemmung`, `keinZyklus`, `fortschritt`, `zeit` — same statements, at W's G-part.
Changed form: `schwach` (every W step is a GX step, SC outside the shared atomics — `SchwachSC`
is FALSE on accepted flag programs, `n1_schwachSC_falsch`), `sperrWechsel`/`sperrSicht` (over GX
steps), `rennfrei`/`keinKernHalt` (over GA runs, which contain G's — `rennfreiBis_of_GA`,
`kernHaltG_of_GA`). Added: `erreicht` (GX-reachability), `exklusiv`.

## 3. Witnesses (non-degenerate)

* **The flag, covered** (`n1_ziel_atomar`, `n1E_ziel`): configuration 1 of the noninterference
  fixture — `kern` stores the atomic `konfig`, `hauptA`/`hauptB` read it with no lock. Refused by
  `Akzeptiert` (`n1_alt_abgelehnt`), accepted by `AkzeptiertX`; (b) with the rely holds
  (`n1_logikA`); `gabbro_ziel_atomar` applied with the concrete checker and the runtime's full
  start. `konfig` IS an admitted shared atomic (`n1_konfig_geteilt`), and W's stale read (hauptA
  stores the initial `konfig` after `kern` wrote 3, where G stores 3) happens on a covered run
  (`n1_stale_gedeckt`).
* **The rely bites** (`hP_havoc_bites`): `zaehlB` stores `konfig` into `tabB[0]`, then tests
  `konfig == tabB[0]` and writes 1 or 2, ensuring `tabB[0] == 1`. Accepted by `AkzeptiertX`;
  the SEQUENTIAL obligation holds at every budget (`hP_seq`); the obligation with the rely FAILS
  (`hP_rely_nicht`: an environment answering the second read with 5 drives the body to 2). So
  (b) with the rely is strictly stronger exactly where another thread can interfere.
* **Refusal** (`vertrag_atomar_abgelehnt`): a contract over the shared `konfig` is refused by
  `AkzeptiertX` at `fussWXB`, accepted by `AkzeptiertA`.
* **The per-core fold** (`faltung_akzeptiertX`, O17): accepted by `AkzeptiertX`.
* **RMW:** `wr_kein_verlust` (no two RMWs read one message on any WR run). NOT done: a concrete
  two-thread `fetch_add` program ending at 2 on WR (the counter is proved on §52's mini-machine,
  `zaehler_zwei`).
* **Message passing with a PLAIN payload:** NOT covered (item 4 below).

## 4. Rust alignment: `N484`

`fusswache2.rs::vertrag_atomar`, sentence `wirkungen.vertrag_atomar` (`pruefe-saetze.py` exit 0):
a `requires`/`ensures` reading an `atomic` no lock protects, which one started thread reaches in a
footprint while a different started thread may write it, is refused. **Measured before the
leg:** `messung/proben/o25b-vertrag-atomar.gab` (a contract `FLAGGE == 1` with a second writer
on another thread) passed the Rust checker with **0 errors** (2 hints `E246`) — the footprint
legs `N290`-`N294` never counted atomics as carriers. After: `N484`. Gift
`beispiele/gift/1204-vertrag-ueber-geteiltem-atomic.gab`; snippet tests in
`crates/gabbro-check/tests/fusswache2.rs` (fires on the gift shape; silent for a body-only shared
read, a thread-local atomic, a single thread). **Corpus diff: over every `beispiele/*.gab` and
`beispiele/gift/*.gab`, only gift 1204 draws `N484`.** `pruefe-akzeptiert-diff.py` lists `N484`
under `fuss`: 22/22 compared programs agree, 201 skips (exporter/checker), `--selbsttest` ok
(both directions). It cannot compare atomic programs (`LG001`), so the claim "Rust decides
`fussWXB`" is measured by gift and snippets, not differentially.

`N485` and gifts 1205–1210 are unused and stay with the O25 wall (the payload rule).

## 5. What remains before the ONE Spec diff

1. **The thread machine with the rely**: `FadenSchritt` over GX steps, `ZielF` legs
   (`schlafendUnberuehrt`, `schlafendFrei`, `joinFrei`, `keineVerklemmung`, `keinZyklus`,
   `fortschritt` as `FortschrittF`, `spawnSicht`) — the adaptation of `Zielsatz/Faeden.lean` and
   `zielF_aus`; the W side of spawning (W has no spawn today; `schwach` in the current Spec is
   also only over non-spawning W runs).
2. **`GabbroZielVerbund` with the rely** (Opus E/F): the link check and hull over `AkzeptiertSpecX`.
3. **The Spec diff itself**, reviewed: `Pruefer.korrekt` → `AkzeptiertSpecX`; (b) →
   `NutzerPflichtA`; `Ziel` → `ZielAtomar`'s leg forms; conclusion over W-reachable machines;
   header — NAMED ASSUMPTIONS (the order assignment is universally quantified; RMW adjacency is
   NOT assumed of `SchrittW` yet), NOT CLAIMED (unguarded PLAIN payloads stay refused/unclaimed;
   the per-core cells' merge discipline; no export of `atomic` items). The embedding
   (`gabbro_ziel_atomar_vor`, `akzeptiertSpecX_of_spec`, `logikPflichtA_iff_akzeptiert`) is ready.
4. **RMW into `SchrittW`**: every theorem of `RMW.lean` transfers the moment `SchrittW` gains the
   adjacency condition; `w_aus_g` must be re-checked (`wr_aus_g` shows it holds).
5. **Item 4 of the task, not done:** a footprint rule admitting a PLAIN payload read after an
   `awaits`/acquire of a release-published flag (`hb_uebergabe` gives the view transfer; the
   replay would need the payload stable across the hand-off).
6. **The exporter** for `atomic` items (`LG001`) — prerequisite for a differential measurement and
   for certificates of atomic programs; `Zertifikat/REGISTER.txt` untouched (no exported program
   changed).

## 6. Measurements

* `./lean-bau`: exit 0, 0 error lines, 343 jobs (after the last Lean change).
* `./cargo-pruef`: **1383 passed, 0 failed, 1 ignored** (after `N484`; 1379 before it, +4 snippet
  tests).
* `instrumente/pruefe-akzeptiert-diff.py`: exit 0, 22 agree, 0 disagree; `--selbsttest` ok.
* `instrumente/pruefe-saetze.py`: exit 0.
* `instrumente/pruefe-todo.py`: 16 findings, the same 16 as on the base tree (stale EBNF counts,
  not this lane's).
* `free -g` during the work: 31 GB total, 13 GB used, 18 GB available (laptop; all builds through
  the queued wrappers).
* Size: about 8 200 new Lean lines in 19 files.

## 7. Files

Lean: `grammatik/Grammatik/Speichermodell/{RMW,AtomarSem,SperreSemA,AtomarRec,AtomarReplay,AtomarAkteur,AtomarLauf,AtomarW,AtomarInv,AtomarRuhe,AtomarFortschritt,AtomarZiel}.lean`,
`grammatik/Grammatik/Zielsatz/{AtomarPflicht,AtomarRuheNutzer,AtomarInvarianten,AtomarMasken,AtomarAkzeptiert,AtomarAkzeptiertZeuge,AtomarZiel}.lean`
(all imported by `grammatik/Grammatik.lean`); `MaschineW.lean` (`schrittW_aus_g` gained a
conjunct, `schrittW_aus_gW` keeps the old shape), `Speichermodell/Zeuge.lean` (uses it).
Rust: `crates/gabbro-check/src/fusswache2.rs`, `saetze.rs`, `tests/fusswache2.rs`. Probes:
`beispiele/gift/1204-vertrag-ueber-geteiltem-atomic.gab`, `messung/proben/o25b-vertrag-atomar.gab`.
Instruments: `instrumente/pruefe-akzeptiert-diff.py` (`N484` under `fuss`). Documents:
`dokumente/SATZKARTE.md` §55, `dokumente/OFFEN.md` O25/O17, `TODO.md`, `AGENTS.md` (ledger).
