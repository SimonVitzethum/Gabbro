# Fix lane F11 — same-core interrupt preemption in the goal theorem (OFFEN O19, reviews G02 F1 / G12 F1), 2026-09-22

Base: `513924b0` (F10) on `review-0921-integration`. Everything built and run locally (fisch
unreachable); `free -g` beside every heavy run: **31 GB total, 19 GB available, 20 cores**.

Simon's decision (2026-09-21): *"`D.maskiert`: `MaskenOrdnung` into `Laufzeit` (real
coverage)"*. Done as real coverage, but as a LEG of `Ziel` and not as a premise — see §1 for
why that is the right place, and §6 for what that leaves open.

## 1. The reviewed `Spec.lean` diff (AGENTS §2)

**No premise changed. `Ziel` gained one conjunct.**

| | Before | After |
|---|---|---|
| (a) `AkzeptiertSpec` | 9 components | unchanged |
| (b) `NutzerPflicht` | unchanged | unchanged |
| (c) `HardwareAnnahmen` | unchanged | unchanged |
| (d) `Laufzeit` | `lader`, `start`, `einmal` | unchanged |
| `Ziel` | 14 legs | **15**: new `keinKernHalt : KernHaltG P O passes M0 M` |
| new definitions | — | `KernPlan` (the core schedule), `KernHaltG` (the leg) |

**Why the premise groups did NOT move, though the task suggested `Laufzeit`.** A premise is a
RESTRICTION: adding the masking assumption to (d) would have made `GabbroZiel` speak about
fewer runs and would have added nothing to the conclusion, because `Ziel` had no leg that
could read it. What was missing is a STATEMENT about preemption, and that belongs in `Ziel`.
Since the leg carries its own hypotheses (which threads are handlers, which core they share,
their call graphs and the masking discipline), `Ziel` is strengthened with no premise change
at all: every program and every run covered before is covered now, and each of them now also
gets the new leg. `gabbro_ziel`'s statement text is otherwise unchanged.

**What the leg says.**

```
KernHaltG P O passes M0 M :=
  ∀ kern H Z A,  (handler threads' call graphs closed and their features)
    (∀ t, H t → MerkAbg P (Z t) (A t))                     -- the graph is closed
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t))        -- it holds at the start machine
    (∀ t, H t → ∀ f L, Z t f → (A t f).sperre L = true → D.maskiert L = true)   -- H102
    (∀ t L, ¬ AnSperre M0 t L)                             -- M0 is a start machine
    ∀ ms fs n, LaufG P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ g f L, H g → f ≠ g → kern f = kern g → AnSperre M g L →
        L ∉ offen ((M.faeden f).spur)
```

`KernPlan kern H ms fs n` is the hardware, named and split in two:

* **entry only when unmasked** — a handler takes its FIRST step only where no other thread of
  its core holds a lock declared `masks irqs`. That is what `cli`/`sti` do: while such a lock
  is held, interrupts are off on that core, so the handler is not entered there.
* **run to completion** — from that first step on, no other thread of its core steps while the
  handler is unfinished. That is what preemption IS on one core: the handler displaces the
  thread it interrupted, and that thread continues only afterwards.

**Why nothing is weakened.** `Ziel` gains a conjunct and loses none, so `GabbroZiel` is
strictly stronger; the premises are literally the same text. `KernPlan` is not an assumption
of the theorem but of the leg's own quantifier, so no run was removed from the statement: a
run that no core schedule admits still gets the other fourteen legs.

**Why the program side is a hypothesis of the leg and not a component of (a).** `Einheit` does
not say WHICH declared start is a handler — the exporter drops `via idt`, and `Spec.lean` has
modelled dispatch roots as ordinary starts since 2026-09-15 — and machine G has no cores. A
checker component would therefore have had to invent the handler set. Named in the Spec header
NOT-CLAIMED list and in OFFEN O19 (narrowed), with exactly what would close it.

## 2. The proof (`grammatik/Grammatik/Zielsatz/Masken.lean`, new, 233 lines)

* `handler_sperre_maskiert` — THE PROGRAM SIDE (`H102` in the model). If every lock the
  feature set of a thread's call graph admits is declared `masks irqs`, then at every machine
  of the run that thread stands only at masked locks. The carrier is the existing frame
  invariant `MerkInvG` (FadenMerkmal.lean): `Merkmal.sperre` is exactly "which locks the
  bodies may take", and `GRest.mR` carries it through every step (`merkInvG_lauf`, proved
  along a run from any start machine, the twin of `merkInvG_erreichbar`).
* `kernHaltG_gilt` — THE SENTENCE, for every program of G, with no premise from (a)–(d)
  (like `speicherSicher`). Proof: the lock the handler stands at is masked (above); by "run to
  completion" no thread of its core stepped since the handler's first step, so that thread's
  state — and its held locks — are the ones it had THEN (`laufG_fremd` on the sub-run); by
  "entry only when unmasked" the handler could not have entered there. The case where the
  handler never stepped is closed by `anSperre_start_falsch` (a start machine's residue is the
  whole body, `.ende`, never a `.dann` layer).
* Helpers, each its own theorem: `merkInvG_lauf`, `anSperre_gleich` (standing at a lock head
  is a fact about the thread's own state), `anSperre_nicht_fertig`, `anSperre_ende_falsch`,
  `anSperre_start_falsch`, `sperre_merkmal`, `erster_index`.
* `maskM`, `maskenDisziplinB`, `merkAbg_maskM` — `H102` as a Bool over the member list, and
  the bridge into the leg's hypothesis.

`ziel_aus` (Zielsatz/Beweis.lean) discharges the new field with `kernHaltG_gilt P O passes _ M`
— nothing else in the proof moved.

## 3. Witnesses (`Zielsatz/MaskenZeuge.lean`, new, on `Korpus59.lean`)

* **`masken_zeuge` — a real preemption, non-degenerate.** On the runtime's own start of
  `beispiele/59` (thread 0 runs the entry dispatch root `takt_verteiler`, thread 1 the root
  `ruf_verteiler`), both bound to core 0: thread 1 unfolds its body and TAKES `RING`; then the
  handler steps and stands at `locks TAKT`, the lock declared `masks irqs` — it entered while
  the thread of its core was inside its critical section, and it is the only thread of that
  core that steps from then on. Every hypothesis of the leg is discharged concretely (the
  handler's call graph `kZT`, its feature set `kAT` with `sperre := D.maskiert`, `MerkAbg`,
  `MerkInvG` at the start machine, the three-step `LaufG`, `KernPlan`), and the leg — taken
  from `korpus59_ziel`, i.e. from `gabbro_ziel` with the concrete checker — gives
  `KLock.takt ∉ offen (M3.faeden 1).spur`: the deadlock `H102` refuses does not happen.
* **`masken_disziplin_460` — the refusal.** The discipline Bool is `false` on
  `ruf_verteiler`'s graph (it takes `RING`, which declares no `masks irqs`) — the shape of
  `beispiele/gift/460` — and `true` on `takt_verteiler`'s (`masken_disziplin_59`).
  `masken_disziplin_nicht_pruefer` records that the checker's Bool accepts the unit either
  way: the refusal is the handler discipline, not (a).

## 4. Rust side — the correspondence of `H102`, measured

`kontexte.rs` (`H102`): for every context whose `unterbricht` is true (an `entry … via idt`),
every `locks L` in the effect hull of its call graph must have `masks irqs`. The Lean
`maskenDisziplinB P fs w` says the same over `reachB P fs w`. **Measured with the binary of
this tree:**

| file | Rust | Lean Bool |
|---|---|---|
| `beispiele/gift/460-eintritt-nimmt-unmaskierte-sperre.gab` | `error: [H102] … takes 'TAKT', which does not declare 'masks irqs'` (1 error) | `masken_disziplin_460 : … = false` |
| `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` | 13 items, 0 errors, 0 hints | `masken_disziplin_59 : … = true` |

**No mismatch was found, so no code, no gift and no example was added** (AGENTS §7 row: F11
takes no numbers). Two differences of scope are named, both already named in `kontexte.rs`:
Rust skips a lock the unit does not declare (it will not guess its `masks` clause), and it
fires on `via idt` only, so `beispiele/57`'s IPI is silent. The Lean Bool runs over the one
unit's declaration, where every lock is known.

`pruefe-akzeptiert-diff.py` needed no change (the leg is not a checker component):
`--selbsttest` `SELBSTTEST: ok`, exit 0; full run `compared=21 skip=191 partial=2 findings=0
not-measured=0`, exit 0, `59` still `rust=accept | lean=accept | PARTIAL` (partial for the
entry/boot roots, as before).

**Emitter:** unchanged, and it writes no `cli`/`sti`. Recorded in the Spec NOT-CLAIMED list
and in OFFEN O19: the C realises no masking, so the translation-validation chain has nothing
to relate `KernPlan` to.

## 5. Measurements

- `lake build` (grammatik): **285 jobs, 0 errors** (+2 files: `Zielsatz/Masken.lean`,
  `Zielsatz/MaskenZeuge.lean`); no `sorry`/`admit`/`axiom`/`native_decide`.
- `#print axioms gabbro_ziel`: `[propext, Classical.choice, Quot.sound]`.
  New theorems: `anSperre_gleich`, `anSperre_nicht_fertig`, `anSperre_ende_falsch`,
  `anSperre_start_falsch`, `sperre_merkmal`: `[propext]`; `merkAbg_maskM`,
  `masken_disziplin_59`, `masken_disziplin_460`: `[propext, Quot.sound]`; `merkInvG_lauf`,
  `handler_sperre_maskiert`, `kernHaltG_gilt`, `kAT_abg`, `kAT_start`, `masken_zeuge`: the
  standard three.
- `cargo test --no-fail-fast`: **72 collections, 1326 passed, 0 failed, 1 ignored** — exactly
  the baseline (this lane changes no Rust).
- `instrumente/pruefe-saetze.py` exit 0 (442 codes, 55 without sentence = ratchet);
  `pruefe-kennungen.py` ALL PASS; `pruefe-todo.py` **16** (= baseline);
  `pruefe-zahlen.py` **37** (= baseline); `pruefe-akzeptiert-diff.py` 0 findings.
- **Corpus:** no `.gab` file was touched and the checker binary is unchanged, so there is no
  corpus diff to measure; the two files above were re-measured by hand (table in §4).

### The one red: `pruefe-emission.sh`, and it is NOT this lane

`instrumente/pruefe-emission.sh` exits 1 in stage 9 with

```
FUND: 126 statt 125 emittierende Dateien in beispiele/ -- die Marke gehoert nachgezogen
```

`MARKE_EMIT` stands at 125 (`instrumente/pruefe-emission.sh:3121`, last moved in `dc651170`),
and **126** files under `beispiele/` emit today. The 126th is
`beispiele/157-worker-pool.gab`, added by **fix lane F10** (`513924b0`), whose report says
"emission ALL PASS" — an erratum. This lane adds no `.gab` and changes no Rust: its whole diff
is under `grammatik/` and `dokumente/`, which `pruefe-emission.sh` never reads. Per the brief
("do not touch `MARKE_EMIT`; report the measured value") the counter was NOT moved:

> **measured value: `MARKE_EMIT` must go 125 → 126, reason: `beispiele/157-worker-pool.gab`
> (fix lane F10) emits.**

Everything the run reached before the abort was green (stages 1–8, 289 of 289 emitting files
compile under `cc` and `clang`, 2 reverse probes bite); ASan does not start on this machine
(stage 6b `NICHT GEFAHREN`, as for every lane of this chain).

## 6. What stays open (OFFEN O19, narrowed; SATZKARTE §48)

1. **Handlers and cores are not in the unit.** `kern`, `H`, the call graphs and the masking
   discipline are hypotheses of the leg. Making them part of (a)/(d) needs a field in
   `Einheit` (the `via idt` dispatch fact, carried by `lean_g.rs`) and a core in machine G.
2. **The C masks nothing.** The emitter writes no `cli`/`sti`, so the model's `KernPlan` has
   no counterpart in the emitted program; the TV chain for it is not built.
3. **First entry only.** The leg constrains the handler's FIRST entry; re-entry of the same
   handler thread and handler-on-handler preemption are outside it (in G a handler thread runs
   once). `Unterbrechung.lean` §5 has the level generalisation over the event log, unconnected
   to this leg.
4. **`Unterbrechung.lean`'s `MaskenOrdnung`** (over `Lauf`, the event log) and the new
   `KernPlan` (over the G run) are twins that are not linked by a theorem.
5. The witness shows one three-step run; `Ziel` at every other reachable machine is
   `gabbro_ziel`'s claim, not the witness's.

## 7. Commits

- `f5d83439` — `Spec.lean` (the leg and its two definitions, the reviewed-diff header
  block, the assumption and NOT-CLAIMED lists), `Zielsatz/Masken.lean`,
  `Zielsatz/MaskenZeuge.lean`, `Beweis.lean` (`keinKernHalt := kernHaltG_gilt …`),
  `Grammatik.lean`, SATZKARTE §48, OFFEN O19, TODO, AGENTS §2/§7, this report.
