# MUSE-REPORT-245 — Symmetric worker pool: N304 lifted with soundness

Lane 245 (muse/245). All six round-1 findings (F1–F6) are addressed below.
English only. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere;
every added theorem uses every premise; no conclusion restates a premise.

## 0. Result lines (last runs, quoted verbatim)

- `./lean-bau`: `Build completed successfully (275 jobs).`
- `./cargo-pruef`: `== exit 0; failing tests: 0`
- `./emission-pruef`: `== exit 0`, `== EMISSION: ALL PASS -- 37 durchgestochen,
  280 von 280 uebersetzen, 2 umgekehrte Probe(n) ==` (no marker drift; markers untouched)
- `python3 instrumente/pruefe-saetze.py`: exit 0. `pruefe-kennungen.py`:
  `KENNUNGEN: ALL PASS`. `pruefe-englisch.py`: exit 0.

## 1. What was done

**F2 — checker (core of the task).** `concurrent { f, f }` (same routine twice)
is accepted IFF the routine is pool-safe: no signature-held lock, no reasons,
and every carrier its call graph may write is guarded by a `lock … protects`
line, atomic, or per-core (`accumulates … per cpu`). Reads need nothing: with
no unguarded writer, two threads reading one carrier do not race. A
same-routine pair sharing writable state without a lock stays refused with
`N304` (narrowed condition, no new code — the task's "otherwise" branch).
`N315` (idle duplicates) is byte-identical: its verdicts never move.

- `crates/gabbro-check/src/fusswache2.rs`: new `pool_sicher` in `race()`
  (reuses `gehalten`, `funktionen.fehler`, `graph_writes`, `guarded`,
  `atomic`, `core` — the exact maps the `N290`–`N294` legs read); the `N304`
  fire condition changed from `!idle` to `!pool_sicher` (`idle ⟹ pool-safe`,
  so the change is strictly a narrowing); refusal text and both notes
  rewritten; module-head and `race()` docs updated.
- `crates/gabbro-check/src/saetze.rs`: Satz `wirkungen.rennboden` — `aussage`
  (pool-safe admission), `vorbehalt` (same-function pairs go to `N304` unless
  pool-safe), `gemessen_an` (1097/1098, inline positives, empty corpus diff),
  `fundstelle` (+ `Spec.lean` `PoolSicher`/`EinzelnPool`, `PoolSym.lean`).
- Probes, both directions:
  - poison `beispiele/gift/1097-pool-shares-unguarded.gab` (`-- erwartet: N304`,
    direct unguarded write, draws exactly `N304`);
  - poison `beispiele/gift/1098-pool-transitive-write.gab` (`-- erwartet: N304`,
    write hidden in a callee — the graph, not the body, is judged);
  - positive `pool_sauberer_arbeiter_bleibt_still` (inline in
    `tests/fusswache2.rs`: guarded writes under `L`, zero errors, one E248
    hint — the same hint 124 draws);
  - positive `pool_reine_leser_bleiben_still` (inline: pure reads, 0 errors,
    0 hints).
- Corpus verdict diff over all 818 `beispiele/**/*.gab` before/after: the ONLY
  moves are the two added gift files (both `N304`, nothing else). No existing
  file changes verdict — no corpus program exhibits a pool-safe duplicate, and
  `976` still draws exactly `N315`. Pre-existing `N304` refusals (745, 897,
  899, 912) all still fire (unguarded writes / signature locks verified by hand).
- Codes N436–440 are NOT consumed (no new refusal exists — the narrowing only
  removes fires). Gifts 1099–1101 stay reserved. A "positive gift file" cannot
  exist: every file under `beispiele/gift/` must fall, so positives live inline
  (precedent: 976's twins) — that is my reading of the reservation.

**F3 — driver.** `laufzeit/start_pool.c` (new, 218 lines, same style as
`start.c`): N pthreads on one routine, zero hardcoded unit names. Everything
unit-specific arrives as `-D`: `EINHEIT_INCLUDE`, `POOL_FN`, `POOL_N` (≥ 1),
`POOL_SPERRE` (two-level paste defines exactly `L_nimm`/`L_gib`), optional
`POOL_PRUEFE`/`POOL_ERWARTET` (the unit reports its own `unsigned`, the driver
only compares). Idle root `ruhe` kept exactly (`pause()` loop, `unused`).
Measured end-to-end on a pool-safe demo unit (`.tmp/pooldemo.gab`, quoted §5):
checker 0 errors, `emit` RC=0, `cc -Werror` RC=0, then

- N=1, 2, 4, 8: `pool: pruefe=30 (want 30)`, exit 0 (5/5 runs at N=4);
- wrong expectation (31): `pool: result 30, want 31`, exit 1 (the check bites);
- pin: source declares `concurrent { arbeiter, arbeiter }`, recipe passes
  `POOL_FN=arbeiter POOL_N=2` (N=4/8 also measured: N is a runtime choice;
  the checker admits the shape for any N by the same argument).

**F4 — Lean starts with duplicates.** The starts SHAPE needed no change:
`E.starts`/`E.ws` are already lists, so duplicates are expressible; the gates
were `einzelnB`/`Laufzeit.einmal`, not the shape. The idle root (`mitRuhe`,
`Ruhe*.lean`) is untouched — no diff there at all. Delivered, all green:

- `Spec.lean` (additive only, zero existing lines changed): `PoolSicher`
  (moved here from the first skeleton so the starts shape owns it),
  `PoolSicherW` (at the computed graph), `EinzelnPool` (every twice-occurring
  start is pool-safe). `ws.Nodup` implies it vacuously.
- `Zielsatz/PoolSym.lean` (new, wired into `Grammatik.lean` — F1):
  decidable checks `poolSicherWB`/`einzelnPoolB` with `poolSicherWB_iff`,
  `einzelnPoolB_iff`; `einzelnPoolB_of_einzelnB` + `akzeptiertSpec_pool`
  (old acceptances preserved — "never weakened", both directions pinned);
  `einzelnPool_paar` (the pair admitted exactly when pool-safe — the
  extension the old `einzeln` refused); run leg `pool_schreibt_nicht_lauf`
  (a pool thread's step writes no unguarded non-atomic carrier — applied per
  writing thread, so no write-write/write-read pair exists); lock leg
  `pool_startExklusiv` (`wurzeln` is membership-based, so `StartExklusiv` —
  the premise of the unchanged guarded leg `rennfrei_g_voll` — transfers to
  duplicates as-is). The footprint half of `SchreibGetrenntK` is NOT claimed
  (pool-safe routines may read unguarded carriers they never write) — and not
  needed, since the write side of every race pair is empty.
- Axioms: `pool_schreibt_nicht`, `_zeuge`, `_zeigt`, `poolSicher_refD_unmoeglich`,
  `einzelnPool_paar`, `pool_startExklusiv`, `PoolSicher`, `EinzelnPool`:
  `[propext]`; `poolSicherWB_iff`, `einzelnPoolB_of_einzelnB`: +`Quot.sound`;
  `einzelnPoolB_iff`, `akzeptiertSpec_pool`, `pool_schreibt_nicht_lauf`:
  the standard three. All within the project's standard set.

**F5 — rule-13 witness.** `pool_schreibt_nicht_zeuge` instantiates ALL premises
jointly on `poolD` (the lock-free `refD` variant: same table `konto`, same
guard, `haelt := []`, plus one unguarded, non-atomic, never-written global
`frei`): empty member list (graph definitionally `{einzahlen}`, no body ever
unfolded), carrier `.inr ()`, thread 0 running `einzahlen` with argument 7.
Non-degeneracy: `pool_schreibt_zeigt` (`einzahlen` writes `konto`, by `rfl`).
`refD` itself CANNOT host the witness — proved as `poolSicher_refD_unmoeglich`
(both fixture functions hold the lock by signature) — and it has no unguarded
carrier at all, so the joint witness lives on the minimal extension while
`refD` hosts the refusal direction. This answers the "vacuous premise" trap
of waves 1–2 by construction, not by assertion.

**F1** — `import Grammatik.Zielsatz.PoolSym` at the end of
`grammatik/Grammatik.lean`; the file builds as job 273/275.

## 2. Exact new names

Lean defs/theorems: see §1 (full list in `PoolSym.lean` + 3 defs in
`Spec.lean`). Rust: `pool_sicher` (`fusswache2.rs::race`). Tests:
`pool_sauberer_arbeiter_bleibt_still`, `pool_reine_leser_bleiben_still`
(`tests/fusswache2.rs`); gifts `1097-pool-shares-unguarded.gab`,
`1098-pool-transitive-write.gab`. Driver: `laufzeit/start_pool.c`
(`POOL_FN`/`POOL_N`/`POOL_SPERRE`/`POOL_PRUEFE`/`POOL_ERWARTET`).

## 3. What remains open (wave-B inputs)

1. **Emitter gap: none.** Measured: `concurrent { arbeiter, arbeiter }` emits
   exactly one `static void arbeiter(void)`; the `concurrent` item emits
   nothing (existing behavior). No wave-B emitter work is needed for
   duplicate starts. `parse.rs` untouched (duplicates always parsed).
2. **Spec field swap (specified, not performed).** Replacing
   `AkzeptiertSpec.einzeln : ws.Nodup` by `EinzelnPool` (+ `einzelnB` by
   `einzelnPoolB`, `Laufzeit.einmal`/`StartZulaessig.einmal` by a pool-safe
   disjunct, `laufzeit_voll` pool case, `EinzelnPool`-`mitRuhe` transfer)
   re-states the proved goal theorem and belongs to a dedicated review lane,
   not a parallel worker turn. Every bridge lemma it needs is proved above.
3. **Honest divergence (finding, not a bug).** Rust now accepts pool-safe
   duplicates while Lean `Akzeptiert` still demands `einzelnB`. The lane-208
   diff probe cannot see it: its denominator is exportable programs and
   `lean_g` refuses multiple starts (TODO §1 census, LG004), so pool units
   never enter it. The swap (item 2) closes the divergence.
4. **Per-core model gap.** The surface exempts `per cpu`; the model has no
   notion for it (booked in CUTS, same standing as before).

## 4. Things in the task I believe are wrong or risky

- The task's "Lean: starts shape carries duplicates" suggests reshaping
  `E.starts`; the shape already carries them (lists). The work was the legs.
- Reserving gift numbers for a "positive" misreads the corpus contract:
  gifts must fall; positives live inline. 1099–1101 are untouched.
- New diagnostic codes would have been wrong here: a narrowing has no new
  refusal by construction. N436–440 are untouched.

## 5. Toolchain pitfalls met (for other lanes)

- `nomatch e,` inside a struct update/instance eats the field-separator comma
  (multiple discriminants); `Empty.elim` parenthesised is safe. Reproduced
  minimally.
- Multi-field `{ s with a := …, b := … }` with tactic/lambda values
  intermittently fails to parse in-tree (all isolated cases pass); named
  auxiliary theorems as values always work.
- `decide` cannot evaluate through an opaque `haveI` instance (kernel gets
  stuck: "free variables"); a top-level `instance … := inferInstanceAs …`
  unfolds fine. `decide` also cannot synthesise `Decidable` for folded defs
  (`Bewacht`) or projection-typed goals — `show` the concrete form first, or
  use constructors (`List.mem_cons_self`, `cases` on `∈ []`).
- Single-file `./lean-probe` uses stale oleans: after touching `Spec.lean`,
  only `./lean-bau` refreshes dependents.

## 6. Demo unit (scratch, not committed; `$TMPDIR/pooldemo.gab`)

`table konto` (2 slots, `Stand`), `lock L protects { konto }` with
`konto[0]==konto[1]` invariant, `setze` (124's both-slots promise),
`arbeiter` (`locks L { setze(30); }`), `pruefe() -> u32` with
`requires Held(L)` returning `konto[0]` (a bare read draws H007, correctly —
first version measured it), `concurrent { arbeiter, arbeiter }`.
Checker: 0 errors, 1 hint (E248, the callee-contract hint 124 also draws).
