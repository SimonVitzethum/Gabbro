# Fix lane F10 — worker pools in the goal theorem (OFFEN O18, review G06 F1/F4), 2026-09-22

Base: `1c2a5a09` (F9) on `review-0921-integration`. Everything built and run locally (fisch
unreachable). `free -g` beside every heavy run: 31 GB total, 20 GB available.

Simon's decision (2026-09-21): switch the Spec to `PoolSicher` and PROVE the legs. Done: the
goal theorem now covers pool-safe duplicate starts; nothing below `Akzeptiert_ok` needed a new
proof.

## 1. The reviewed `Spec.lean` diff (AGENTS §2)

The text of `GabbroZiel` and of `Ziel` is unchanged. New definition `Mehrfach ws w :=
[w, w] <+ ws` ("declared at least twice"), the one notion of "twice" in the file.
`PoolSicher`/`PoolSicherW`/`EinzelnPool` (lane 245) moved before `AkzeptiertSpec`;
`EinzelnPool` restated as `∀ w, Mehrfach ws w → PoolSicherW P fs w` (equivalent to the lane-245
filter form, `mehrfach_filter`).

| Premise | Before | After |
|---|---|---|
| (a) `AkzeptiertSpec.einzeln` | `ws.Nodup` | `EinzelnPool P fs ws` |
| (a) `Getrennt` (inside `fuss`) | `∀ w₁ w₂ ∈ ws, w₁ ≠ w₂ → …` | `∀ w₁ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → …` (start OCCURRENCES) |
| (d) `Laufzeit.einmal` | `t ≠ u → same fn → (init t).1 = none` | `… → (init t).1 = none ∨ ∃ w, (init t).1 = some w ∧ Mehrfach E.ws w` |
| proof-only `StartZulaessig.einmal` | `→ Ruhig` | `→ Ruhig ∨ Mehrfach ws` |

**Why nothing is weakened.**
- (a) is a RELAXATION of `Pruefer.korrekt`'s target: every old checker is still a `Pruefer`
  (`pruefer_vor_neu`, from `akzeptiertSpecVor_neu : AkzeptiertSpecVor → AkzeptiertSpec`), so
  `∀ C : Pruefer` ranges over at least what it did.
- (d) is a relaxation: every run admitted before is admitted now (`laufzeit_vor_neu`).
- Every unit accepted before is accepted now with the same Bool: on a repetition-free `ws`,
  `Akzeptiert = AkzeptiertVor` literally (`akzeptiert_nodup_gleich`), and the old Bool accepts
  only repetition-free lists (`akzeptiertVor_nodup`, `akzeptiert_vor_neu`).
- `Ziel` is the same structure; `GabbroZiel` therefore claims `Ziel` for strictly more
  programs and runs.
- The occurrence form of `Getrennt` is not a weakening either: it is STRONGER on duplicated
  lists (it pairs a pool routine with itself) and identical on distinct ones.
- Spec header: new "WHAT CHANGED ON 2026-09-22" block; (d) list entry and NOT CLAIMED updated
  ("a busy routine declared ONCE on several threads" stays outside).

## 2. The legs

Every leg of `Ziel` is proved in `ziel_aus` over per-THREAD facts (`lokK`, `SchreibGetrenntK`,
`StartExklusiv`, rank invariant, …). Distinctness entered at exactly two places, both in
`Zielsatz/Akzeptiert.lean`; both now take a same-routine thread pair from `Mehrfach`:
- `getrenntK_of` (footprint thread-locality, feeds `vertrag`, `sperrInv`, `invRueck`, `invGrund`,
  `startEnde`, `keinStartGrund`, `keinLogikHalt`, `fortschritt` via `ziel_ort_mehrfaden_*`): from
  the occurrence form of `Getrennt`;
- `schreibGetrenntK_of` (unguarded write separation, feeds `rennfrei`): from `EinzelnPool` — a
  pool graph writes no unguarded, non-atomic carrier.
`SpurInv`, deadlock, `KeinWarteZyklus`, `ZeitAb` never used distinctness (lock ranks, `GutO`,
per-frame bounds; `StartExklusiv` from `wurzeln`, membership-based). Transfer to `P.mitRuhe`:
`einzelnPool_mitRuhe`, `mehrfach_map_inj`; `laufzeit_initRuhe` lost its `Nodup` premise
(`mehrfach_of_getElem?`), five callers updated. `gabbro_ziel` is still
`theorem gabbro_ziel : GabbroZiel`.

## 3. Witnesses (`Zielsatz/PoolZeuge.lean`, SATZKARTE §47)

- `pool_ziel_zeuge` — `zPool`: probe B's program (`haupt() = locks { wrap() }`, the graph writes
  `konto` guarded by `()`) with `haupt` declared twice. Accepted by `akzeptiert_pruefer`
  (`zPool_akzeptiert`; the pre-F10 Bool refuses it, `zPool_vor_abgelehnt`), `NutzerPflicht`
  holds, on the runtime's start threads 0 and 1 both run `haupt`; thread 0 steps, thread 1
  steps, thread 0 takes the lock (held at `M3`), and `gabbro_ziel` gives `Ziel` at `M3`.
  Non-degenerate: `zPool_schreibt` (the pool graph really writes `konto`).
- `pool_abgelehnt`, `pool_abgelehnt_spec` — `hauptB` (writes `privB` unguarded) declared twice:
  every other component accepts, `einzelnPoolB` refuses, no `AkzeptiertSpec`.
- `pool_fuss_paart_vorkommen` — `hauptA` (reads and writes `privA`) declared twice: the new
  footprint component refuses, the pre-F10 one accepted.
- G06 F4: `pool_schreibt_nicht_voll` (complete member list `mFs`, pool-safe `pruefeA`, carrier
  `privA` really written by `hauptA`) and `einzelnPoolB_iff_zeuge` (both directions on complete
  lists). The lane-245 `pool_schreibt_nicht_zeuge` stays (weak, as G06 said); the run lemma
  `pool_schreibt_nicht_lauf` has no own witness — its content is now inside `gabbro_ziel`'s
  `rennfrei`, witnessed by `pool_ziel_zeuge`.

## 4. Bool side

`einzelnPoolB`/`poolSicherWB` (moved from PoolSym into `Akzeptiert.lean`) are the `einzeln`
component; `einzelnPoolB_iff`, `poolSicherWB_iff`, `mehrfachB_iff`, `getrenntW_iff` (occurrence
form) decide exactly; `akzeptiert_iff` re-proved.

## 5. Rust aligned with Lean

**Correspondence.** For a same-name start pair `N304` is silent iff the routine has no
signature-held lock, no reason channel, and every carrier its graph may write is guarded
(`lock … protects`), atomic, or per-core — `EinzelnPool` (`N302`/`N303` already give the first
two for every start). On the exported fragment the two are EQUAL: the exporter refuses `atomic`
and `accumulates` items, so both read "every written carrier guarded". The per-core exemption
is the one Rust-wider point (OFFEN O17, unchanged). The footprint legs `N290`–`N293` always
paired thread INDICES (`lokal` in `fusswache2.rs`) — the occurrence form of `Getrennt`; pinned
by the new positive/negative probe `pool_fussabdruck_paart_vorkommen` (a pool routine reading
its own guarded-but-invariant-free written carrier in its contract: `N290`; declared once:
silent).

**Mismatch found and fixed:** `N315` refused an IDLE duplicate the new Lean Bool accepts (idle ⇒
pool-safe). `N315` is RETIRED (`fusswache2.rs`; sentence `wirkungen.rennboden` now names
`N300`–`N304`), gift `976-duplicate-idle-start.gab` removed, test renamed to the positive
`doppelter_ruhiger_start_bleibt_still`, `paesse.rs` `eigner_zweimal_gestartet_d268` now pins
`D268` alone. No new code, no gift. `bau.rs` doc rows updated.

**Exporter:** `LG001` for repeated starts (fix lane F4) LIFTED (`lean_g::check_starts`), since
the Lean side now covers pools; test `refuses_duplicate_start` → `exports_duplicate_start` (both
occurrences travel into `starts`). New example `beispiele/157-worker-pool.gab` (guarded pool,
`concurrent { arbeiter, arbeiter }`): checker clean (one `E248` hint, as 124), exports with
`starts := [⟨g_arbeiter, .nil⟩, ⟨g_arbeiter, .nil⟩]`.

**`pruefe-akzeptiert-diff.py`:** component `einzeln` → `einzelnPoolB {P} {fs} {cs} {ws}`, codes
`["N304"]`; self-test extended by the pool positive (157 accepted by the Lean Bool).
- `--selbsttest`: `104 agree`, `doubled start refuses at einzeln`, `157 (one routine twice)
  accepted at einzeln`, `SELBSTTEST: ok`, exit 0.
- full run: `compared=21 skip=191 partial=2 findings=0 not-measured=0`, exit 0;
  `beispiele/157-worker-pool.gab | rust=accept | lean=accept | agree`; `pin: einzeln true on
  19/19`.

## 6. Measurements

- `lake build` (grammatik): **283 jobs, 0 errors** (+1: `PoolZeuge.lean`); 0 `sorryAx` in the
  build log; no `sorry`/`admit`/`native_decide`/`axiom` added.
- `#print axioms gabbro_ziel`: `[propext, Classical.choice, Quot.sound]`. New/changed theorems:
  `mehrfach_filter`, `mehrfachB_iff`, `poolSicherWB_iff`, `einzelnPoolB_iff`,
  `getrenntW_nodup`, `akzeptiert_nodup_gleich`, `akzeptiert_vor_neu`, `einzelnPoolB_of_einzelnB`,
  `pool_schreibt_nicht_voll`, `pool_abgelehnt`, `pool_fuss_paart_vorkommen`,
  `einzelnPoolB_iff_zeuge`, `zPool_poolSicher`, `mehrfach_map_inj`: `[propext, Quot.sound]`;
  `nicht_mehrfach_of_nodup`, `einzelnPool_of_nodup`, `einzelnPool_paar`, `akzeptiertVor_nodup`,
  `zPool_schreibt`, `zPool_akzeptiert`, `zPool_vor_abgelehnt`: `[propext]`;
  `getrenntW_iff`, `akzeptiertSpecVor_neu`, `pruefer_vor_neu`, `laufzeit_vor_neu`,
  `laufzeit_initRuhe`, `laufzeit_voll`, `mehrfach_of_getElem?`, `einzelnPool_mitRuhe`,
  `startZulaessig_aus`, `ziel_aus`, `zPool_nutzerPflicht`,
  `zPool_start_offen`, `pool_ziel_zeuge`, `pool_abgelehnt_spec`: the standard three.
- `cargo test --no-fail-fast`: **72 collections, 1326 passed, 0 failed, 1 ignored** (baseline
  1325: +1 `pool_fussabdruck_paart_vorkommen`; two tests renamed/inverted).
- `instrumente/pruefe-emission.sh`: **ALL PASS** (37 durchgestochen, 288/288, 2 reverse probes;
  ASan not run on this machine). No `MARKE_EMIT*` touched.
- `pruefe-saetze.py` exit 0 (442 codes — 443 minus the retired `N315` —, 55 without sentence =
  ratchet); `pruefe-kennungen.py` ALL PASS; `pruefe-todo.py` 16 (= baseline); `pruefe-zahlen.py`
  37 (= baseline); `pruefe-englisch.py` red as before (7965 German comment lines);
  `pruefe-syntax.sh` SYNTAX ALL PASS, the known red "Warnungen im Bau" stage (pre-existing
  warnings only).
- **Corpus diff** (base binary built from `1c2a5a09` vs this tree, error/hint codes per file over
  all 915 `beispiele/**/*.gab` of this tree): **no file changes**; `157` (new) reads the same on
  both binaries (`E248` hint only). Removed: gift `976` (base `N315`, now clean — the retirement).

## 7. Commits

- `16a0185b` — Lean: the Spec diff, the proofs, the witnesses.
- (this commit) — Rust alignment (`N315` retired, `LG001` lifted, example 157, probes), the
  instrument, the witness `pool_fuss_paart_vorkommen`, OFFEN/SATZKARTE/TODO/AGENTS, this report.

## 8. Open

- **O17 (per-core)** stays: the Rust pool rule exempts `accumulates … per cpu`, the model has
  no notion of it; the exporter refuses such units, so they never reach (a).
- A busy routine declared ONCE on several threads stays outside (d) (NOT CLAIMED).
- The C-side chain (translation validation) for a pool unit is not built; `157` exports, its
  chain count is not measured here.
- `pool_ziel_zeuge` shows three steps of one run; `Ziel` at every other reachable machine is
  `gabbro_ziel`'s claim, not the witness's.
