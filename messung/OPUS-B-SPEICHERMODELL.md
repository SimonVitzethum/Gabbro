# Opus agent B — the memory model beyond DRF-SC (2026-09-26)

*Branch `worktree-agent-afa3ea04e4972bffb`, four commits on top of `ba6c16a7`. Task: Spec.lean
NOT CLAIMED "weak memory beyond DRF-SC", plus OFFEN O17 (per-core writes). Addendum (Simon,
2026-09-26): try to make the weak semantics the semantics the goal talks about for atomics.
Everything below was measured on this machine with the queued wrappers (`./lean-bau`,
`./lean-probe`); fisch was unreachable.*

## 1. Result in one paragraph

The goal theorem is now proved over a **weak machine**. Machine W
(`grammatik/Grammatik/Speichermodell/MaschineW.lean`) is machine G over a view-based weak memory
— the promise-free timestamp machine of RC11 for exactly the orders the emitter writes — in
which a thread reads, at every carrier it reads, **any** message at or above its view. The DRF
theorem (`schwach_ist_g`, `Speichermodell/DRF.lean`) proves that on every program the checker
accepts, for **every** assignment of memory orders to the atomics, every step of W is a step of
G. `Ziel` gained the leg `schwach` (a reviewed `Spec.lean` diff, no premise moved), and
`gabbro_ziel_schwach` gives every leg of `Ziel` at every machine W reaches. The litmus shapes
(MP release/acquire forbidden, MP relaxed allowed, SB allowed and not on SC, CoRR forbidden) are
Lean theorems over the same primitives. **Not reached:** covering programs that *rely* on an
unguarded atomic read across threads (the relaxed non-SC outcomes): the checker's footprint
component refuses them, so they never reach premise (a); closing that needs a rely in the user's
sequential semantics (OFFEN O25, route named). O17 is narrowed: the pool rules agree and the
write half is covered; the read half is O25.

## 2. The model, and why this one

The emitter lowers every access to an `atomic` through an explicit `atomic_*_explicit` call
(`emit.rs`, lane 152; `C-SPEICHERMODELL.md` §1c):

| declaration | store | load | fetch RMW | CAS loop |
|---|---|---|---|---|
| `release` / `acquire` | `memory_order_release` | `memory_order_acquire` | `memory_order_acq_rel` | release / acquire |
| `seq` | `memory_order_seq_cst` | `memory_order_seq_cst` | `memory_order_seq_cst` | seq_cst |
| `relaxed` / no word | `memory_order_relaxed` | `memory_order_relaxed` | `memory_order_relaxed` | relaxed |

No fences, no `consume`. Locks: `L_nimm`/`L_gib`, which the generated driver implements with
`pthread_mutex_lock`/`_unlock` (`treiber.rs`). Per-core accumulators: `static _Atomic T
X_zellen[N]`, relaxed.

For this fragment the model is the **promise-free timestamp machine** (Kang et al., POPL 2017,
without promises; Lahav–Giannarakis–Vafeiadis, POPL 2016, for release/acquire):
`Speichermodell/Sicht.lean`.

* per location a history of messages `⟨ts, wert, sicht⟩` (timestamps = modification order);
* per thread a view; a read may return **any** message at or above the view (`Lesbar`) and
  raises the view — an acquire read joins the message's view (`beitrag`);
* a write takes a **fresh** timestamp strictly above the writer's view (`Frisch`), not
  necessarily the largest; a release write stores the writer's view (`nachricht`);
* a lock carries a view: a take joins it into the thread, a release joins the thread's into it.

`seq_cst` is modelled as release/acquire. That **over-approximates** RC11 (every C11 behaviour
of a `seq_cst` access is one of W, SB included), so every claim over W holds for the C, and no
SC-order fact is claimed. No promises: no load buffering, which RC11 forbids too (`po ∪ rf`
acyclic). Plain carriers are modelled as relaxed locations: for a race-free program that
over-approximates C11 (the happens-before-latest write stays readable); a racy one is
undefined in C anyway.

**Where the weak choice sits in G.** W's step presents the thread a memory `σ`: at every carrier
the step READS (a recorded read event, `LiestG`), some admissible message; everywhere else G's
memory; then G's own step rule runs on `σ` (`SchrittW`). That G steps record every read is the
footprint bound G's race leg already rests on (`OrteInvG`, `schritt_ev`); a step depending on an
unrecorded carrier would escape `RennfreiBis` just the same. Foreign answers (`Orakel.wirkt`,
`regLies`, `sichtbar`) stay the oracle's, over the presented world.

## 3. What is proved (all `#print axioms`: propext, Classical.choice, Quot.sound — or fewer)

| file | theorem | statement |
|---|---|---|
| Sicht.lean | `mp_ra_verboten` | MP, release store / acquire load: "flag 1, data 0" unreachable |
| | `mp_rlx_erlaubt` | MP all relaxed: "flag 1, data 0" reachable (explicit run) |
| | `sb_erlaubt` | SB with release/acquire: both reads 0 reachable |
| | `sb_sc_verboten` | the same outcome unreachable on the SC machine `LSchrittSC` |
| | `lErreichbar_sc_schwach` | every SC run is a weak run |
| | `corr_verboten` | CoRR: after reading the second write, never the first |
| MaschineW.lean | `w_aus_g` | every run of G is a run of W (every order assignment) |
| | `schrittW_kohaerent` | every program: a read's message is at/above the view, and the view reaches it after |
| | `schrittW_erwerb` | every program: an acquire read joins the message's (release) view |
| | `schrittW_g`, `schrittW_bau`, `speicher_ext` | helpers: a W step on G's own memory is G's step; building W steps with any admissible reads |
| DRF.lean | `getrennt_of_frei` | an unguarded footprint carrier is thread-local (`FussS`) |
| | `lies_fakten` | at a read: the reader's graph reads the carrier and it holds every guard lock |
| | `sichtInv_erreichbar` | the view invariant on every machine W reaches |
| | `liest_neueste`, `praesentiert_g` | every read reads the newest message; the presented memory is G's |
| | **`schwach_ist_g`**, `g_aus_w` | **the DRF theorem**: every W step is a G step; every W run a G run |
| Zielsatz/Beweis.lean | `ziel_aus` (leg `schwach`) | from `schwach_ist_g` and `Akzeptiert_ok` |
| Zielsatz/Schwach.lean | **`gabbro_ziel_schwach`** | every leg of `Ziel` at every machine W reaches |
| | `schwach_gleich_g` | on an accepted program W and G reach the same G-states |
| Zeuge.lean | `w_nicht_sc` | on the REFUSED noninterference configuration 1, W reads a stale `konfig` and stores 0 where G on the same schedule stores 3 |
| | `akzeptiert_n1_abgelehnt`, `fuss_n1_abgelehnt` | that configuration is refused, by the footprint component |
| | `schwach_pool_zeuge` | three W steps on the accepted F10 pool; every leg by `gabbro_ziel_schwach` |
| | `poolSicherRust_iff`, `proKern_schreiben_akzeptiert`, `proKern_schreiben_echt`, `proKern_lesen_abgelehnt` | O17 (§6) |

**Why the DRF theorem holds** (the invariant `SichtInv`, all lower bounds on views): the
checker's `fuss` already demands that a carrier a thread's graph reads is thread-local
(`GetrenntK`) or lock-guarded — atomic or not. Thread-local: only that thread writes it, and a
write sets its view to a fresh, larger timestamp (`frei_schreiber`). Guarded: every access holds
the lock (`zugriff_haelt`), a take joins the lock's view (`genommen_von`), a release the thread's
(`gegeben_von`), exclusivity does the rest (`exklusivG`). So at every read the view is at the
newest message, `Lesbar` admits only it, and it carries G's value (`stimmt`). Carriers with
unordered writers are exactly those nobody reads; W's G-part keeps the last executed write there
(it can differ from W's newest message), and no leg reads them — every carrier a leg reads is in
some footprint.

## 4. The Spec.lean diff review (AGENTS §2)

The edits are in clearly delimited hunks (`-- BEGIN/END weak-memory …`, "(weak-memory hunk …)")
so that Opus agent A's Spec/G edits merge separately.

| | before | after |
|---|---|---|
| imports | … `Grammatik.AntwortOrte` | + `Grammatik.Speichermodell.MaschineW` (definitions only) |
| (a) `C.akzeptiert …`, `AkzeptiertSpec` | unchanged | unchanged |
| (b) `NutzerPflicht` | unchanged | unchanged |
| (c) `HardwareAnnahmen` | unchanged | unchanged |
| (d) `Laufzeit` | unchanged | unchanged |
| `GabbroZiel` text | unchanged | unchanged |
| `Ziel` | 14 legs | 15 legs: `schwach : SchwachSC P O passes M0 M` |
| new definition | — | `SchwachSC`: for every `ord`, every W state over `M` reached from `RufStartW M0`, every W step from it is a G step from `M` |

**Why nothing is weakened.** No premise moved, `Ziel` loses no conjunct and gains one, so
`GabbroZiel` now claims strictly more of exactly the same programs and runs. Every earlier
theorem about `Ziel` still holds (consumers build/read `Ziel` by field name; checked: the only
constructor is `ziel_aus`). The leg is **not** premise-free, unlike `keinKernHalt` and `zeit`: it
uses (a) (`fuss`, closed graphs, the start's exclusivity) and (c) (`GutO`), and it is false of W
on refused programs (`w_nicht_sc`). **Embedding lemmas:** `w_aus_g` (every G run is a W run, so
W is a superset of G and the new statement covers every machine the old one did),
`schwach_gleich_g` (on accepted programs the two reach the same G-states), `gabbro_ziel_schwach`
(the goal over W).

**New named assumptions in the header** (THE ONE ASSUMPTION LIST, "assumptions of the reading"):
"the hardware is DRF-SC" is no longer assumed for accepted programs — it is the leg. In its
place: W over-approximates C11/RC11 for the emitted orders (a published model, not proved here
against an axiomatic C11); compiler and hardware implement C11 atomics and the orders as
specified; the lock primitive synchronises like a mutex (acquire at the take, release at the
give; `pthread_mutex` in the generated driver); carriers are the locations (a table or an atomic
array is one location of W; the DRF argument holds per element as well).

**NOT CLAIMED, the weak-memory line.** Replaced: "weak memory beyond DRF-SC (G is sequentially
consistent; `atomic` globals are ordered by A10 …)" becomes what is claimed (the leg, the goal
over W) and what is not: programs relying on an unguarded atomic read across threads (refused by
`fuss`; W's non-SC outcomes occur on no accepted program; OFFEN O25; the exporter refuses
`atomic` items anyway); that W is exactly RC11; atomics stay excluded from `rennfrei` (their
accesses are atomic operations, `schwach` covers their values).

**Axioms.** `#print axioms gabbro_ziel`: `[propext, Classical.choice, Quot.sound]` (measured
through `grammatik/NachpruefungZiel.lean`). No `sorry`, `admit`, `axiom`, `native_decide` in the
new files (grepped).

## 5. Rust

Nothing changed in `crates/`, and nothing had to: the DRF theorem uses no memory order at all
(it holds for every `ord`), every atomic access is an explicit atomic call (lane 152, `N270`/
`N271`), the locks are mutexes, and the Lean checker Bool is **stricter** than the Rust checker
on atomics (it refuses cross-thread atomic reads the Rust checker admits) — a coverage gap, not
a soundness one. No reserved code (N481–N485) or gift (1201–1210) was taken; they stay with O25.

`instrumente/pruefe-akzeptiert-diff.py`, measured with a freshly built `target/debug/gabbro`
(`cargo build` through the cargo slot):

* first run: **21 of 21 NOT MEASURED** and the self-test failed at 104 — the instrument only
  knew the fisch wrapper's exit line (`== lean exit code: 0`), the local `lean-probe` prints
  `== 0 error(s) in the COMPLETE output`. The apparatus, not the tree. Fixed in the instrument
  (both lines are evidence);
* after the fix: `compared=21 skip=191 partial=2 findings=0 not-measured=0`, 19 agreements,
  every component `true` on 19/19; `--selbsttest`: ok in both directions (104 agrees, doubled
  start refused at `einzeln`, 157 accepted).

`./cargo-pruef` was not run: no Rust source changed (the instrument is Python).

## 6. OFFEN O17 — narrowed

Read as what the emitter writes (`_Atomic` cells, relaxed), a per-core accumulator is a relaxed
atomic global. Then:
* `poolSicherRust_iff` — the Rust pool rule of `N304` with its "per-core" disjunct IS the Lean
  `PoolSicher` ("per-core" becomes "atomic");
* `proKern_schreiben_akzeptiert` — a pool whose instances all write one relaxed atomic is
  accepted by the concrete checker Bool, and covered by `gabbro_ziel` with the leg `schwach`;
* `proKern_lesen_abgelehnt` — a start reading an atomic another start writes (the fold, or the
  update's own load) is refused by `fuss`, while Rust exempts per-core cells there.

So the write half is covered and the read half is exactly O25. Modelling "each thread its own
cell" would in addition need a core per thread in G (pinning; O19). The exporter still refuses
`accumulates` (`LG001`).

## 7. What remains (named in Spec.lean NOT CLAIMED, OFFEN, TODO)

1. **O25 — a rely for unguarded atomic reads.** `execEndH` answers a shared unguarded atomic
   read with an arbitrary value of its type (a havoc at the read, as `Umwelt` does at lock
   moves), `fuss` exempts atomic carriers from locality, the replay carries it. Then the user's
   proof covers every value W can return, relaxed non-SC ones included; coherence and
   release/acquire are already facts of W for every program (`schrittW_kohaerent`,
   `schrittW_erwerb`). Payload hand-off (P3) needs a rely conditioned on `awaits`. Opus-sized;
   it touches the replay family (`ziel_ort_mehrfaden_ende` and around), which is why it was not
   started as a partial Spec change.
2. **Stage (b)** keeps `DRFSC` as a premise on the C side (`CNebenlaeufig.lean`); W lives on G's
   side. Connecting them needs a per-access C semantics.
3. **Exactness of W against an axiomatic RC11** is cited, not proved.
4. Per-architecture fence mappings: not started (W is the C11 level).

## 8. Measurements

| run | result |
|---|---|
| `./lean-bau` (final, 2026-09-26) | exit 0, 0 error lines, 290 jobs, 4 min 47 s wall; `free -g`: 31 total, 17 available |
| `#print axioms gabbro_ziel` | propext, Classical.choice, Quot.sound |
| `pruefe-akzeptiert-diff.py` / `--selbsttest` | 19 agree, 0 findings / ok both directions |
| `pruefe-todo.py`, `pruefe-englisch.py` | red with findings unrelated to this branch (EBNF counts, German checker messages in `crates/`, which this branch does not touch) |

Files: `grammatik/Grammatik/Speichermodell/{Sicht,MaschineW,DRF,Zeuge}.lean`,
`grammatik/Grammatik/Zielsatz/{Spec,Beweis,Schwach}.lean`, `dokumente/SATZKARTE.md` §49,
`dokumente/OFFEN.md` O17 (narrowed), O25 (new), `TODO.md` §2/§3, `instrumente/pruefe-akzeptiert-diff.py`.
Numbering note for the merger: SATZKARTE §49 and OFFEN O25 may collide with Opus agent A's
additions — renumber on merge.
