# Goal assessment 2026-09-10: the goal is not reached

**Verdict first, as the folder demands: the goal is NOT reached.** The goal is that a
Gabbro user verifies their program by proving only their own logic and their hardware
assumptions — assuming Gabbro verified. What follows is the measurement that refutes the
standing claim, with file, line, and command beside every number, and the repairs that
landed the same day.

> **On the two GO verdicts of 2026-09-09.** Four agents (two pairs) confirmed the goal
> twice — before and after implementation. Both verdicts were wrong in the same place:
> where the *shape* of a specification stood in for a *proof*. This document withdraws
> the parts that do not hold and keeps the parts that do. *A folder that withdraws its
> own triumphs on measurement is the one property of this project no competitor has.*

Both Lean trees built locally for this assessment (`free -g`: 31 GB total, 13 GB
available): `grammatik: lake build` → 10 jobs green, 0 `sorry`, all `#print axioms`
`propext`/`Classical.choice`/`Quot.sound` only; `programmlogik: lake build` → 8 jobs
green, `exec_sicher`, `pruefe_sicher`, `schluss_sicher`, `logik_grundfaelle` likewise.

---

## 1. What a user proves today: a fragment, not a program

Not "only their own logic" — a slice of their logic over a fragment of their program:

| channel | measured reach |
|---|---|
| **A** (`gabbro pflichten --lean`) | 75 obligations, 9 sentences, 66 refused (`PLAN-VERIFIKATION.md` §0) |
| **B** (`gabbro lean`, hand-written spec) | 89 of 277 bodies exportable = 32 %; 5 specifications over two files written for the channel (§4, V7) |
| **trust base** | 4 items, of which item 2 (`lean.rs`, 1834 lines of export) is unproved — *"dass das exportierte Datum das Programm IST, steht in keinem Satz"* |

And the bolt that decides the question: the export hangs on the checker's verdict
(*"a unit with errors carries no register"*, 23 units without one). Whoever verifies
today verifies what the checker let through first — and the checker is unverified Rust.

**Deeper, and conditional-proof-proof:** `stuck ⇒ own logic` stands as a theorem
(`exec_sicher`, 0 `sorry`) — but over a model in which, by its own finding list, index
overflow and width overflow are not errors at all (`World := Place → Value` is total,
`Body.lean`:147/:473). For the first rows of the plumbing table the sentence is empty.
And `Sicherheit/*.lean` checks a checker these same files wrote out of `SPRACHE.md` —
nobody measures the seam to `crates/` (W16, Finding 6).

**Repaired 2026-09-10 (this document's occasion, not its subject):** the outcome that
collided with the abolished keyword is `Logik.vorzustand` now (`Semantik.lean`:284,
`SYNTAX.md` §§7/16 — PFLICHTEN.md «B26» already called it that).

---

## 2. Data races under "assuming verified": half, with gaps at the seam

`Ziel.lean` IS the question as a sentence, and three sentences really carry it
(`kein_wettlauf`, `kein_wettlauf_global`, `keine_ueberkreuzung`): over EVERY
interleaving of event traces satisfying `Gesittet`, two accesses of different threads
to a guarded carrier are happens-before ordered — or the global is atomic. That is real,
not cosmetic, and complete for locks and marks.

**Repaired 2026-09-10:** the first missing bridge now stands proved —
`Wettlauf.lean:lauf_aus_brav`: every interleaving (`IstVerschraenkung`) of executions
well-behaved from empty traces (`Brav`, via `exec_spur`) satisfies W1 (consistency) and
W2 (good events), by `Brav.konsistent_von_leer`, `Brav.gut_von_leer`,
`Konsistent.drop` (`Satz.lean`). Axioms clean, 0 `sorry`. What it does NOT close is
stated at the theorem, not in a footnote.

Four things stand beside it, two of them re-measured because the documents book them
differently:

1. **No `exec → Gesittet` sentence existed** — `Lauf` in `Wettlauf.lean` is any list of
   steps; `exec` occurs in the file twice, both prose. W1/W2 were claimed as consequences
   of `exec_spur`, but the bridge was never built. Now built for W1/W2 (above); W3–W5
   stay premises by construction (below).
2. **The expensive bridge is still open:** `exec`/`exec_sicher` compute over one `World`,
   sequentially. That sequential `requires`/`ensures` stay valid under interleaving does
   NOT follow from HB order — that is the Owicki–Gries/separation-logic step, and it
   stands nowhere. Race freedom and the logic proof are two unconnected sentences.
   (`exec_rahmen` is the candidate premise for it: disjoint write sets. Unbuilt.)
3. **Three of five premises come from outside:** W3 = the lock primitives exclude (a
   foreign body, `assume`), W4 = mark in one thread, W5 = shared — and W5 is discharged
   by a Rust pass (H013), exactly the kind of instance the grammar was supposed to
   replace. Under "assuming verified" the pass would be verified; today it is the same
   class it replaces.
4. **HB has two edges:** program order and `gibt L → nimmt L`. A `publishes`/`awaits`
   pairing without a lock is no synchronisation edge; visibility is hardware
   (`sichtbarkeit` A10), and A10 is unfalsifiable — *"durch Ausführung nicht
   widerlegbar"*. Same for the atomic branch: *"dann ordnet die Maschine"*. Matches
   `RACE.md` (forms 17 and 22).

Unchanged and open: **alias.** Places are `DecidableEq` in the model — two names for
the same bytes do not exist there. A2/A3 of 28 race forms carry nothing, and in the
corpus `udp-echo.gab` reads a stale checksum at 0 errors (a copied value, not a view —
but the census counts the forms uncovered either way). And a device is no thread:
CPU↔DMA races fall entirely under `assume dma_visibility_in_order`.

> Data races are thus covered under the assumption as far as the lock discipline
> reaches — resting on the spinlock primitive, the C11 memory model, an alias
> analysis that does not exist, and the bus. More than before 2026-09-09, and less
> than `README.md`:37 (*"nine of eleven carried"*) reads.

---

## 3. Time: sorted, not proven — and that is a decision, not an oversight

| half | state |
|---|---|
| budget (`costs`, `held <=`, `bounded`, `per_pass`) | computed in `kosten.rs` (K001–K012) — in ops, not cycles |
| deadline (`deadline <= n ops arch X falsifier p`) | named hardware assumption `fortschritt a` + manifest entry `frist_<fn>_eingehalten` |

What it does NOT contain: no cache, pipeline, branch-prediction or memory-latency
model; no interrupt/preemption/bus contention; no liveness (`SPRACHE.md`:341: *"no
mechanism addresses it"*). `kosten.rs` itself says `costs` on a recursive function
is an assumption, and an input-dependent bound silences the pass. And the probe that
gives the date its value: 29 named falsifiers, TWO existing as programs
(`sonde_boot_unerreichbar` plus, since today, `sonde_tick` for
`frist_zaehle_werte_eingehalten` — sample currency R15/W10, locks excluded and said
so). A date is today "named, once run" — twenty-eight to go.

**Repaired 2026-09-10 (withdrawals, both):**

- `Ziel.lean:ziel_zeit_ist_hardware` is GONE — the sentence, not the definition. It
  claimed `∃ e, fristAlsAnnahme a = e`: an existence statement over a total function,
  which EVERY definition satisfies. Nothing could damage it, so it measured nothing —
  the same class as the trivial `bedeutung_total`/`wert_total`, which the folder
  confirms AS trivial, and this line did not. What stays is the definition
  (`fristAlsAnnahme`): the mapping date → assumption. The date is measured by the
  probe below, not by any sentence here. (`SYNTAX.md` §§6/18 cite the definition now.)
- `Ziel.lean:absenkung` stands flagged UNMEASURED (W7: a number without a search
  path). `⟨4, by decide⟩` is a constant in the model with no connection to `emit.rs`
  — and quantitative CompCert is CerCo, not the production compiler, whose promise
  is sequential, race-free, without `__asm__` and without C11 `_Atomic` (measured in
  our own product: 39 `_Atomic`, 120 `volatile`, 2 `__asm__`). For a multicore kernel
  with DMA, CompCert is no line one can substitute. The search path is written at the
  constant: per-primitive C-statement counts against `emit.rs`.
- `Ziel.lean:CForm` no longer claims closure: 19 named shapes, with `BEWEIS.md`
  Gegenstand 2 beside it (64 measured forms, 30 unruled). Whoever closes the list
  rules the 19 one by one, the way `?:` was ruled.

**Measured 2026-09-10 (first running date probe):** `sonden/sonde_tick.c` for
`frist_zaehle_werte_eingehalten` (`beispiele/71`): 20000 iterations, fixed seed,
LFENCE-bracketed RDTSC, locks excluded and said so; min 116 / p50 252 / p99 337 /
max noisy (scheduling tail — verdict on p99, not max); booked C=512 (~50 % above
p99); default run exits 0, `--max-cycles 1` exits 1; UBSan clean. Sample currency
(R15/W10): the date is now *measured, not run* — two of 29, twenty-seven to go. The
probe belongs to exactly one obligation (N024); register row 39 PROGRAM,
`SONDEN_MIT_PROGRAMM` entry and quota move to (6, 39) are booked below, not asserted
here.

---

## 4. Verdict

| question | answer |
|---|---|
| Does a user today prove only their own logic? | **No.** As a sentence over the sequential core yes, under S1/S2/U1/U2 — as a statement about the language in eight named classes no; and in practice 32 % export, 9 channel-A sentences and a checker-dependent export reach no whole program. |
| Would races be covered if Gabbro were verified? | **Half, with gaps at the seam.** Lock discipline ⇒ HB order is proved (+ W1/W2 bridge since today); missing are the Owicki–Gries step (sequential logic under interleaving), alias, and the device. |
| Would time be covered? | **No — by decision.** Budget in ops is proved; cycles are a named assumption with (since today) two of 29 running probes. Whoever reads "time covered" reads "time named". |

**The three cheapest items with the largest effect, in order:** (a) ~~exec → Gesittet~~
BUILT today for W1/W2 (`lauf_aus_brav`; W3–W5 stay premises, Owicki–Gries stays open);
(b) ONE running probe per date — first one built AND integrated today (`sonde_tick.c`:
register row 39 PROGRAM, `SONDEN_MIT_PROGRAMM`, quota (5,39)→(6,39), A_p 6/39 = 0.1538;
sample currency, locks excluded), 28 to go;
(c) S4 (`checker_agrees` witness pairs per unit) — BUILT today (`lean::witness`,
`tests/seam.rs`): 189 routines over beispiele/, 119 witnessed — 53 both-accept, 66
rust-only, 0 lean-only; ten findings (F3 index-`IntIn` largest, F4 = Finding 5).
The W16 seam now fails loudly per routine per run instead of silently. Status in
the Sicherheit lane's file, not duplicated here.

### S4 scope (built 2026-09-10 — see above)

`PLAN-SICHERHEIT.md`:230 + `PLAN-VERIFIKATION.md` §3/V5: `gabbro lean` writes, per
unit, `theorem checker_agrees : pruefeBlock P erg [] ⟨body⟩ = some _ := by decide`
with `P` filled from the declarations. A unit the Rust checker accepts and `pruefe`
refuses (or the reverse) then fails LOUDLY at `lake build`, per unit, per run. What it
measures: agreement on the corpus — not identity of the functions. First run WILL find
differences (Finding 5 guarantees some: `pruefe` gives `/` no range, `typen.rs` does);
each is either a rule `pruefe` lacks (add it) or a rule `gabbro-check` has that the
spec does not state (the expensive kind — a checker claim with no meaning). Build
order: emitter side first (`lean.rs` writes the theorem; my lane's file), Lean-side
acceptance coordinated with the Sicherheit lane that owns `programmlogik/Gabbro/*`.
Falsifier: a corpus unit where the two disagree silently — then the seam, not the
theorem, is the finding.

---

*Evidence beside every number: commands were `lake build` (both trees), `cc
-std=c11 -O2 -Wall -Wextra -Werror` + `--max-cycles 1` control, `grep -c` over the
grammatik sources. No number here was taken from a document on trust — including,
as of today, the documents this folder wrote yesterday.*
