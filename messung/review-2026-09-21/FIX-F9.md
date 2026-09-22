# Fix lane F9 — the O-1 clone handoff, Lean half (review G11 F1)

*2026-09-22, branch `review-0921-integration`, on top of F8 `ace9b692`. Built and measured
LOCALLY (fisch unreachable, Simon 2026-09-21). Commit `ea2d41f0`.*

## 1. What was done

| # | task | result |
|---|---|---|
| 1 | bring in the Lean half (`2244babf`, `cde18e25`) | `grammatik/Grammatik/CloneHandoff.lean` checked out from `cde18e25`. §1–§3 (`CloneAbi`, `cloneAbiGoodB` and its soundness, the three legs, `cloneWitness`/`cloneBadWitness`) are unchanged. The run level is reworked (item 3). The file is imported by `Grammatik.lean`. The O-1 Spec diff and its ripple through 19 files were **not** taken (item 2). |
| 2 | Spec diff review | see §2. Outcome: the vacuous (d)/(d2) was not added. `GabbroZiel` is unchanged. `Spec.lean` gains one comment line in NOT CLAIMED. |
| 3 | make it non-vacuous | the child is a thread of machine G. It sits in a dormant slot and is spawned by a live parent, then steps by G's own rules. Laws and two non-degenerate witnesses are in §3. |
| 4 | axioms, Rust correspondence | the standard three everywhere. `N456` has a model-side theorem. `N457` has a stated correspondence (§4). |

## 2. Spec diff review (AGENTS §2: the goal is reviewed as a diff of `Spec.lean`)

**The O-1 diff (`cde18e25`), as proposed:**
- (d) `Laufzeit.klon : CloneStart …`: a thread that starts at a gate entry is no declared start.
- (d2) a new premise of `GabbroZiel`, `CloneAssume … (RufStartG …)`.
- `Deklaration.klon` in `Syntax.lean`, with its `mitRuhe` transport.
- Header lines in the named-assumption list and in "NEW here".

It did not weaken the goal, and it listed both assumptions. **It was vacuous**, for three
reasons:
- `Laufzeit.start` puts every thread at the root or at a declared start.
- `klon` keeps gate entries apart from declared starts.
- `CloneHandoff` reads only the start heads.

So no thread that (d2) talks about exists, and (d2) follows from (d). The brief says that a
decorative premise is worse than none, so **the diff was not applied**.

**The diff this lane actually makes to `Spec.lean`** is comment-only, one item in the NOT
CLAIMED list:

> a thread SPAWNED at run time (the `child` region of a stack gate, lane O-1): the thread
> population is fixed at the start by (d), and a spawned child reaches `Ziel` only through
> `klon_ziel` (CloneHandoff.lean, outside this statement), i.e. when the unit lists the child
> entry as a declared start and is accepted -- the exporter refuses `child` (`LG004`) and the
> emitter `C185`, OFFEN O21.

What changes and what does not:
- **Premises:** unchanged. The named-assumption list needs no new entry, because no
  assumption was added.
- **Conclusion:** unchanged.
- **Axioms:** `#print axioms gabbro_ziel` = `[propext, Classical.choice, Quot.sound]`.
- **Review question 2** ("nothing else restricts the quantified runs"): still true, with no
  qualification.
- **What is new:** the NOT CLAIMED list now names the spawned child that the goal does not
  cover. Before this lane that gap was unnamed in the Spec.

## 3. The model (`CloneHandoff.lean` §4–§9)

A clone machine is a machine-G state plus the set of live threads.
- **Step rule:** `KlonSchritt` is either a G step of a LIVE thread, or a spawn of a dormant
  slot by a live parent. The spawn changes liveness only, and there is no new G rule.
- **What the spawn over-approximates:** the time. It may fire at any point of the parent's
  run, because G has no event for an axiom call.
- **What it does not capture:** the data. The child's arguments and its entry world are fixed
  at the start.

| theorem | content |
|---|---|
| `klonErreichbar_G` | every clone run is a G run from the start with the children placed at their entries |
| `klon_schlafend_unberuehrt`, `klon_lebt_bleibt` | a dormant slot is exactly its start state; liveness only grows |
| `klon_kind_haelt_nichts` | a dormant child whose entry holds no signature lock holds nothing, whatever the parent holds (**N456**) |
| `klon_frei_nur_lebende` | `RufFreiG` reads the live threads only: a dormant child never blocks |
| `ChildNoReturn`, `CloneHandoff` (now over `entries : List D.Fn`), `cloneHandoff_empty`, `cloneHandoff_schlafend` | the handoff over threads that really start at an entry |
| `klon_ziel` | `gabbro_ziel` ∘ `klonErreichbar_G`: every leg of `Ziel` on every clone run, when the unit that lists the child entry as a declared START meets (a)–(d) (**N457** correspondence) |
| `k124_kind`, `k124_spawn`, `k124_kind_haelt_nichts`, `k124_klon_ziel`, `k124_klon_ziel_spawn` | witness on the accepted unit `beispiele/124`: `hauptB` sits dormant on thread 1 and `hauptA` spawns it. All premise groups are discharged (`laufzeit_initRuhe`, `kE_akzeptiert`, `kE_nutzerPflicht`, `kO_hw`). The declaration's lock exists, and `hauptB` holds none by signature |
| `kwSchritt1`–`4`, `kw_lauf`, `kw_nicht_degeneriert`, `kw_handoff` | witness run on `gP` (see below) |

The `gP` run:
1. The parent, on thread 0, takes its call step while the child is still dormant.
2. The parent spawns the child on thread 1.
3. The child unfolds its `if`.
4. The child takes the branch.
5. The child **writes**: slot 0 goes from 0 to 2. The write event is in the child's trace,
   and the parent's trace is empty.

`CloneHandoff` then holds for entry `true`, with thread 1 starting at that entry.

**Dropped from O-1:**
- `CloneStart`, `CloneAssume`, `cloneStart_empty` and `cloneAssume_empty`: these are the
  vacuous premise shapes.
- `cloneHandoff_start`: `cloneHandoff_schlafend` now covers it.

## 4. Correspondence with F3's Rust rules

- **N456:** no child under a held context, and the child restarts with an EMPTY held set.
  `KlonSchritt.spawn` gives the child its own trace; nothing of the parent's trace is copied.
  `klon_kind_haelt_nichts` proves the child holds no lock up to its spawn, provided the child
  entry has no signature lock. That proviso is the model's reading of "not under
  `requires Held`".
- **N457:** the region is judged like a pool routine. `klon_ziel` needs the child entry as a
  declared start of the accepted Lean unit, so the child is covered by the start-level rules
  (`Getrennt`/`SchreibGetrennt`, the lock order, contracts, time). **Only stated:** that
  N457's acceptance implies Lean acceptance of that unit. The exporter refuses `child`
  (`LG004`).
- **N450 per region, jump lowering:** the spawn may happen at any point of the parent's run.
  Every "right after the dominating gate call" time is therefore among the modelled ones.

## 5. Measured (local, `free -g`: 31 GB total, 20 GB available at every run)

- `lake build` (grammatik): **282 jobs green**. The baseline was 281, and the +1 is
  `CloneHandoff`. No errors.
- **Axioms:**
  - `gabbro_ziel`, `klon_ziel`, `k124_klon_ziel` and `kw_lauf` depend on
    `[propext, Classical.choice, Quot.sound]`.
  - The §1–§3 theorems use `propext` at most.
  - No `sorry`, `admit`, `axiom` or `native_decide` in the file.
- `cargo test --no-fail-fast`: **72 collections, 1325 passed, 0 failed, 1 ignored**, the same
  as the baseline. No Rust was touched.
- `instrumente/pruefe-emission.sh`: **ALL PASS**. 37 pierced, 288 of 288 compile, 2 reverse
  probes. No `MARKE_EMIT` counter moved.
- **Text guardians:**
  - `pruefe-kennungen.py`: ALL PASS.
  - `pruefe-saetze.py`: 55 codes without a sentence, as before.
  - `pruefe-todo.py`: 16 findings, the baseline.
  - `pruefe-zahlen.py`: 37 findings, the same count before and after this lane (measured
    with a stash).
  - `pruefe-englisch.py`: red as on the base. Its headline counts are unchanged, and no
    German was added.
- **Corpus diff:** none. No Rust, `beispiele/` or emitter change.

## 6. Open, and why

- **A child inside `GabbroZiel` itself.** The goal's thread population is fixed at the start.
  The spawned child reaches `Ziel` only through `klon_ziel`, as a declared start.
- **Spawn-time data.** The child's arguments (the gate answer and the handed values) and its
  entry world are fixed at the start machine. The child entry's `requires` is (b)'s duty at
  the start world.
- **Repeated spawns.** One slot is spawned once, so a gate that runs repeatedly is not
  modelled. Rust's `N457` is fail-safe for exactly this case.
- **`ChildNoReturn` on every run.** It is not proved: a recursive entry can log its own
  `rueck` inside the child. The C half (the stub never executes `ret` on the handed stack, and
  the child is entered by jump) belongs to lane 258 and to translation validation.
- **N457 ⇒ Lean acceptance, and `child` in the exporter.** Both are open (`LG004`).
- **The handed stack.** It has no G counterpart.

These are recorded in the file's CUTS, SATZKARTE §39 (F9 box), OFFEN O21 and the TODO O-1 row.
