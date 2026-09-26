# Opus agent A — threads created at run time in the goal theorem (OFFEN O21, O22)

*2026-09-26, branch of worktree `agent-a128f79321c4a4287`, base `ba6c16a7`. Everything ran
locally (fisch unreachable), every Lean and cargo run through the queued wrappers / the shared
slots. SATZKARTE §49.*

## 1. What was asked, what was done

| task | state |
|---|---|
| 1. extend machine G with run-time spawns (`start` with join, `child`) without breaking G | **done** — `FadenMaschine.lean`: a G machine plus live set, join lists, ghost rank/clock; steps `lauf`/`start`/`kind`/`join`; no G rule changed; both bridges proved (`fadenErreichbar_G`, `fadenErreichbar_von_G`) |
| 2. spawned threads INTO `GabbroZiel`, every leg on every reachable machine, join waits in deadlock/cycle/progress | **done** — `GabbroZiel` quantifies thread-machine runs; conclusion `ZielF` = `Ziel` on the G state (every spawned thread is a G thread there) + `schlafendUnberuehrt`, `schlafendFrei`, `joinFrei`, `keineVerklemmung` (join waits), `keinZyklus` (`KeinWarteZyklusF`, locks AND joins), `fortschritt` (`FortschrittF`, `JoinWartet` named) |
| 2b. `Akzeptiert` decides the spawn conditions | **done without a new component** — a run-time root stands twice in `Einheit.ws`, so the existing components decide it (correspondence §3) |
| 3. Spec diff review, axioms | **done** — §2 below; `#print axioms gabbro_ziel` = `propext, Classical.choice, Quot.sound`; no `sorry`/`admit`/`axiom`/`native_decide` |
| 4. witnesses | **done** — §4 |
| 5. exporter + diff instrument | **`start`: done; `child`: not exportable** (§5) |
| 6. SATZKARTE, OFFEN, TODO | **done** — §49; O21 narrowed, O22's model and export rows closed; TODO §4 item |

## 2. The Spec.lean diff, reviewed (AGENTS §2)

### Premises before / after

| group | before (ba6c16a7) | after |
|---|---|---|
| unit | `Einheit := ⟨P, S, Q, starts, sp0⟩` | `+ gestartet : List (Σ w, Env …) := []` (run-time roots) |
| `ws` | `starts.map (·.1)` | `(starts ++ gestartet ++ gestartet).map (·.1)` — each root TWICE |
| (a) | `C.akzeptiert E … = true`, `Pruefer.korrekt → AkzeptiertSpec E.P E.S fs E.ws` | textually unchanged (reads the new `ws`) |
| (b) `StartPflicht.req` | `∀ a ∈ E.starts, ReqAmEintritt …` at `E.sp0` | `∀ a ∈ E.starts ++ E.gestartet, …` |
| (c) | `HardwareAnnahmen O E.Q` | unchanged |
| (d) `Laufzeit.start` | `init t = root ∨ ∃ a ∈ E.starts, …` | `… ∃ a ∈ E.starts ++ E.gestartet, …` (`lader`, `einmal` unchanged) |
| runs | `∀ M, RufErreichbarG … (RufStartG …) M` | `∀ lebt0 K, FadenErreichbar … (FadenStart … lebt0) K` |
| conclusion | `Ziel … (RufStartG …) M` | `ZielF … (RufStartG …) K` (`ZielF.g : Ziel … K.m`) |

### Why nothing is weakened — as theorems

* `fadenErreichbar_von_G` + `gabbro_ziel_g`: every G run is a thread-machine run (every thread
  live, nothing spawned), so the old conclusion `Ziel` on every G run is a corollary. Every former
  caller of `gabbro_ziel` (Korpus 59/109/124/125, GenOblig104/108 — generator updated,
  `pruefe-genlean.py` green —, Schlusssatz, PoolZeuge, Proben, CloneHandoff) now calls
  `gabbro_ziel_g` unchanged otherwise.
* `ws_ohne_gestartet`, `startPflicht_vor_iff`, `laufzeit_vor_iff`: with `gestartet = []` (every
  unit of before) `ws`, (b) and (d) are word for word the old ones.
* `pruefer_aus_vor`, `pruefer_aus_vor_gleich`: every checker of the OLD interface (`korrekt`
  against `starts.map (·.1)`) is a new `Pruefer` with the same verdict on every old unit (the
  F10 analogue `pruefer_vor_neu`).
* `gabbro_ziel_vor : GabbroZielVor`: the OLD statement verbatim (old checker interface, old (b),
  old (d), `Ziel` on G runs) over units without run-time roots, proved from the new one.
* The (a) side is a TIGHTENING only for units that have run-time roots (they must be pool-safe
  and lock-free at entry) — units nobody could state before. For them it is the MODEL HALF of
  what the Rust checker demands (`N458`, `N462`), not the same rule: `N462` bounds every carrier
  a root TOUCHES, `einzelnPoolB` only the carriers it WRITES (reads go to `Getrennt`), and
  `N458`'s parameter/result half is the exporter's. Measured in one direction only (Rust accepts
  ⇒ Lean accepts), on ONE `start` program (`faden-start-pool.gab`); see §3. *(Wording corrected
  by the Spec-diff review, `messung/URTEIL-SPECDIFF-OPUS-A-2026-09-26.md`, which found
  "exactly" larger than the measurement.)*

### New named assumptions (in the ONE list, (d))

1. A run-time root's slot is placed in the START machine: its arguments are the unit's (a
   `start` root takes none, `N458`; the exporter refuses a root with parameters by name,
   `LG001`), and its frame's ghost entry world (`s0`, the logged `eintritt`) is the start world.
   Its body reads shared memory at each step, so what it DOES is the spawned thread's behaviour
   — the same situation as a declared start scheduled late, which G always had. Consequence,
   named in NOT CLAIMED: a root `requires` must hold at `E.sp0` ((b)), not merely at the spawn
   world, and `old`-reads of a root `ensures` refer to the start world.
2. The spawn sites are the checked ones: the lowering spawns a `start` root only where the
   starter holds no lock (`N461`; the model's `start` rule carries it as side condition), makes
   the starter wait until EVERY root has finished (`join`), and enters a `child` by jump with an
   empty held set (`N456`, OFFEN O21's jump assumption) — lane 260's lowering and translation
   validation own the C side.

Over-approximated, never under-: a spawn may fire at ANY point of a live thread where the rule's
condition holds, `lebt0` is quantified (any slot may also be live from boot), and a `child`
spawn has no condition on the parent at all.

### NOT CLAIMED, replaced

Before: "a thread SPAWNED at run time … reaches `Ziel` only through `klon_ziel` … OFFEN O21."
After: spawned threads ARE claimed; not claimed: per-spawn arguments (a `child` reading handed
values), a root `requires` only true at the spawn world, `old` at the spawn world, the END of a
join wait (a named `JoinWartet` stop, like a lock wait), the handed stack (G is address-free),
the C side of the spawn.

## 3. The checker correspondence (Rust rule → Lean)

| Rust | Lean | how |
|---|---|---|
| `N458` root shape: no params, no result, no signature lock | `wurzelnB` over `ws` (no signature lock, no reasons); params: the exporter (`LG001`) | root ∈ `ws` (`akzeptiertSpec_gestartet`) |
| `N462` started root pool-safe | `einzelnPoolB` (`EinzelnPool`) | root stands twice in `ws` ⇒ `Mehrfach` ⇒ `PoolSicherW` |
| `N461` no `start` in a held context | side condition `offen spur = []` of `FadenSchritt.start` | `start_unter_sperre_kein_schritt`; it is what makes `joinFrei` and the join legs true |
| `N456` child holds nothing | `wurzelnB` for the lifted region (a region inside `locks` lifts to a root needing the lock) + `faden_schlafend_frei` | `kind_unter_sperre_abgelehnt` |
| `N457` child race rule | `einzelnPoolB` + `Getrennt`/`SchreibGetrennt` over the doubled root | as `N462` |
| `N459` duplicate root, `N460` one owner | none needed | a pool root may run on any number of threads; a root also in `starts` is judged as pool anyway |

Measured on the export (`pruefe-akzeptiert-diff.py`, §5): `N458` is booked under `wurzeln`,
`N462` under `einzeln`, both in the Rust verdict set.

## 4. Witnesses (Zielsatz/FaedenZeuge.lean)

* `sj_lauf` — on `rufPF`: thread 0 starts dormant roots 1 and 2 while holding nothing; root 1
  writes (slot 0: 0 → 2) and finishes; at that machine root 2 is unfinished and the starter is in
  `JoinWartet`; root 2 writes and finishes; the join fires; the starter calls (one frame deep) and
  writes. Six thread-machine steps, both roots' traces carry their write event.
* `kw2_lauf` — thread 0 spawns the child on 1 and never waits: parent call, child write (slot 0:
  0 → 2) and finish, parent write.
* `spawn_start_ziel` — ACCEPTED unit `zStart` (probe B's lock-guarded `haupt` as run-time root,
  `akzeptiert_pruefer` by computation, (b) and (d) proved): the idle root starts two `haupt`
  threads, both step, root 1 takes the lock, the starter waits — `gabbro_ziel` gives `ZielF`.
* `spawn_kind_ziel` — ACCEPTED unit `zKind`: a live `haupt` spawns a `haupt` child; parent step,
  child step, parent takes the lock; the child entered with an empty held set — `ZielF`.
* Refusals: `start_nicht_poolsicher_abgelehnt` (+`_spec`) — `hauptB` (writes `privB` unguarded)
  as a run-time root is refused by the Bool at `einzelnPoolB` alone, every other component
  passes, and as an ordinary start beside `hauptA` it is accepted; `kind_unter_sperre_abgelehnt`
  (+`_spec`) — `wrap` (holds the lock by signature: a region lifted from inside `locks`) refused
  at `wurzelnB`; `start_unter_sperre_kein_schritt`/`_zeuge` — no step makes a lock holder a
  joining starter, instantiated where thread 0 holds the lock.
* `klon_als_faden`, `klon_ziel_faden` — F9's clone machine is a special case (spawn = `kind`).

## 5. Exporter and the differential instrument

* `lean_g.rs`: `check_gestartet` collects every `start` root (each once, body order,
  parameterless or `LG001` by name) into `gE.gestartet` (printed only where one exists — exports
  without `start` are byte-identical, `pruefe-genlean.py` GREEN 2/2); `StmtArt::Start` leaves no
  G term (its spawn and join are thread-machine steps); a starter's lifted `locks` effect (`E008`)
  is no refusal. `analysiere` runs the same check (it succeeds exactly where the export does).
* `child` is NOT exported: every `child` needs a stack gate (`N450`), a foreign body the exporter
  does not build (`Ax := Empty`, `LG001`). The refusal stands, by name; O21 says so.
* New test `exports_start_roots_as_gestartet` (tests/lean_g.rs); probe program
  `messung/proben/faden-start-pool.gab` (checker: 0 errors).
* `pruefe-akzeptiert-diff.py`: `ws` rebuilt from the source with the `start` roots doubled;
  construction pin K5 (source roots == export `gestartet`); `N458`/`N462` in the verdict set;
  self-test extended (positive: faden-start-pool accepted; negative: a root needing a lock
  refuses at `wurzeln`); the local wrapper's verdict line is read (`== 0 error(s) …`), without
  which the instrument said NICHT GEMESSEN for every file here.

## 6. Measurements

| run | result | `free -g` beside it (total / available) |
|---|---|---|
| `./lean-bau` (full `grammatik/`) | **exit 0, 0 error lines, 289 jobs** (287 before + FaedenVor, FaedenZeuge; FadenMaschine and Faeden in the count) | 31 / 21 GB |
| `#print axioms gabbro_ziel`, `gabbro_ziel_g`, `gabbro_ziel_vor`, `zielF_aus` | `propext, Classical.choice, Quot.sound` | — |
| `./cargo-pruef` | **1327 passed, 0 failed, 1 ignored** (first run: 2 failed in `tests/obligations_g.rs`, which pinned the generated text `Zielsatz.gabbro_ziel akzeptiert_pruefer`; updated to `gabbro_ziel_g`) | 31 / 18 GB |
| `pruefe-akzeptiert-diff.py --selbsttest` | ok, both directions, incl. the two new run-time-root probes | — |
| `pruefe-akzeptiert-diff.py` | **compared=22, findings=0, not-measured=0**, partial=2 (59, 109: entry roots), skip=191; `faden-start-pool.gab`: rust=accept, lean=accept, agree (starts=5 in `ws`: chef + 2 roots twice); every pin 20/20; exit 0 | 31 / 17 GB |
| `pruefe-genlean.py` | GREEN, 2/2 byte-identical | — |
| `pruefe-kennungen.py`, `pruefe-saetze.py` | ALL PASS / 184 sentences, 0 invented | — |
| `pruefe-todo.py` | 16 findings, all pre-existing stale README numbers (not in lines touched here) | — |

## 7. What remains open

* Per-spawn arguments and the spawn-time entry world (a `child` reading its handed values; a
  root `requires` at the spawn world) — the model fixes one argument list per slot and the start
  world as ghost entry world. Closing it needs a spawn step that resets the slot's frame, and the
  G invariants re-proved for it.
* `child` export — needs the stack gate as an `Ax` (the exporter writes `Ax := Empty`) and the
  region lifted into a function.
* The lowering (lane 260) and its correspondence to the `start`/`join`/`kind` steps.
* Liveness of the join (named stop).
* Pre-existing, not touched: `pruefe-todo.py` reports 16 stale README numbers (EBNF counts
  170→179 / 233→241, bold-number counts) — none in a line this work changed.
