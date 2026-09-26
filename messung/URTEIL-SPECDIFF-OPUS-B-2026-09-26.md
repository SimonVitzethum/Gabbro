# Verdict — the Spec diff of Opus agent B (weak memory, machine W, the leg `schwach`)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-afa3ea04e4972bffb`, commits
`37b291be`, `d9491bac`, `c2b818ce`, `203e6d08` on base `ba6c16a7`; report
`messung/OPUS-B-SPEICHERMODELL.md`. Measured in the worktree through the queued wrappers only
(`./lean-bau`, `./lean-probe`). One text fix committed separately (`7eec8730`, OFFEN O17).
Nothing merged, nothing pushed.*

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| `Speichermodell/Sicht.lean`: view discipline, litmus MP/SB/CoRR | **SOUND** (facts about the instruction machine `LSchritt`, not about W — honestly stated) |
| `Speichermodell/MaschineW.lean`: machine W, `w_aus_g` | **SOUND** (granularity caveat, F5) |
| `Speichermodell/DRF.lean`: `schwach_ist_g` | **SOUND, and for the right reason** — but it is DRF *by exclusion* (§2) |
| `Spec.lean`: `SchwachSC`, the leg `schwach` | **SOUND** — no premise moved, the leg is contentful; its non-triviality is **argued, not proved** (F3) |
| `Spec.lean` header: "hardware is DRF-SC" replaced by four reading assumptions | **OVERCLAIMED** — two assumptions narrowed or stated as fact (F1, F2) |
| `Zielsatz/Schwach.lean`: `gabbro_ziel_schwach`, `schwach_gleich_g` | **SOUND** |
| OFFEN O17 narrowing, `poolSicherRust_iff` | **OVERCLAIMED in wording** (F4; one sentence fixed in `7eec8730`) — the lemma itself agrees with `N304` as implemented |
| OFFEN O25 | **SOUND** |
| `instrumente/pruefe-akzeptiert-diff.py` | **SOUND**, superseded by master's version at merge (§6) |

**Safe to merge: yes, after F1 and F2 are written into the header, and with the two semantic
merge repairs of §6.** No Lean soundness gap was found.

## 1. Build and axiom evidence (measured)

| Measurement | Result |
|---|---|
| `./lean-bau` | **`exit 0`, 0 error lines in the complete output, 290 jobs** (replayed; `free -g`: 17 GB available) |
| `#print axioms gabbro_ziel` (via `./lean-probe`, `import Grammatik`) | **`[propext, Classical.choice, Quot.sound]`** |
| `#print axioms gabbro_ziel_schwach`, `schwach_ist_g`, `w_nicht_sc`, `schwach_pool_zeuge` | the same three |
| `#print axioms mp_ra_verboten`, `poolSicherRust_iff`, `proKern_*`, `akzeptiert_n1_abgelehnt` | subsets (`propext`, `Quot.sound`) |
| `sorry` / `admit` / `native_decide` / `axiom` in the five new files | **none** (grep exit 1) |
| `cargo` | not run: no Rust source changed on the branch |

## 2. The DRF theorem — right reason, and what it really covers

`schwach_ist_g` rests on `SichtInv` (four lower bounds on views plus `stimmt`) and on three
static facts: `lies_fakten` (a read carrier is in the reader's graph footprint and every guard
lock is held at the START of the step — `ereignis_haelt`, pre-existing), `frei_schreiber` (an
unguarded read carrier has one writer, from `getrennt_of_frei` over the pre-existing
`FussS … (lokK P K)`), and the lock view joins. I checked the proof path: the read is checked
against the pre-step view, and the invariant places that view at the newest message, so
`Lesbar` admits only it. Correct.

**Plainly: it is DRF by exclusion.** `FussS` (pre-existing, unchanged by this branch) already
demands that every carrier a thread's graph reads is signature-guarded, local, or lock-guarded
— atomics included. So on an accepted program no thread ever reads a carrier another thread
writes without a lock. The weak memory is exercised on accepted programs only where nobody
looks: write-only multi-writer atomics (e.g. `proKern_schreiben_akzeptiert`) may get
non-maximal timestamps, and W's G-part there keeps the last *executed* write, not the
modification-order maximum. No theorem reads such a carrier; the report's "every carrier a leg
reads is in some footprint" is informal.

What the leg therefore **does** buy: the classic DRF-SC theorem for lock- and
locality-synchronised programs, proved over a published operational model instead of assumed
("hardware is DRF-SC" becomes "C11 mutex + C11 atomics + W ⊇ RC11"). What it does **not**
buy: any flag, counter, spin, `publishes`/`awaits` hand-off or per-core fold — all refused by
`fuss` (O25, correctly recorded; the Rust checker admits them, so this is a coverage gap
between the checkers, not a soundness gap of the goal).

**`seq_cst` as release/acquire.** The DRF theorem holds for every `ord`, so the declared
orders play no role in the claim at all. Modelling `seq_cst` as RA only adds behaviours to W,
which weakens the assumption "every C11 behaviour is a W behaviour". That is the safe
direction.

## 3. Findings, ranked

### F1 — MEDIUM: oracle reads became silently sequentially consistent

W presents G's memory at every carrier a step does not *record* (`SchrittW.ungelesen`). The
oracle reads memory without recording: `axiomAntwort O a σ` / `O.wirkt`, `O.regLies m σ`,
`O.sichtbar g σ` (`Semantik.lean`). `RennfreiVoll.lean` §"What is NOT covered" lists exactly
these as unrecorded. So in W, foreign code, device-register answers and `awaits` visibility
see the SC memory (the last executed write). The C's foreign code sees C11 memory. Before this
branch that was covered by the blanket reading assumption "the hardware is DRF-SC". After it,
the four named assumptions do not cover it, and `MaschineW.lean`'s header says the opposite
("not a new assumption").

**Repair (header text, Spec.lean "assumptions of the reading"):** add a fifth assumption:
*"answers of foreign code, register reads and `awaits` visibility (`Orakel.wirkt`, `regLies`,
`sichtbar`) are taken over G's memory at carriers they do not record; that the foreign side
sees that memory is assumed, not derived."* Also correct the MaschineW header sentence.

### F2 — MEDIUM: the lock-primitive assumption is stated as a fact of the driver

The header says the lock primitive synchronises like a mutex because "the generated driver uses
`pthread_mutex_lock`/`_unlock` (`treiber.rs`)". That holds for driver-defined locks only. Also
accepted are:

* **own lock primitives** — a bodied `<name>_nimm`/`<name>_gib` over a declared atomic, `N323`
  (`namen.rs:147`);
* **`extern fn` and `asm` primitives** (trust base, `N042`).

`N323` checks atomicity, "order" (the body *reads* an atomic) and hold time. It does **not**
check memory orders. A spinlock with relaxed loads and stores passes `N323` and does not
synchronise like a mutex in C11, and then the DRF argument does not transfer to the C.

**Repair:** state the assumption for every lock primitive: *"every `<L>_nimm` is an acquire
and every `<L>_gib` a release: driver-defined (`pthread_mutex`), own (`N323`, memory orders
NOT checked), or foreign."* Record a follow-up in OFFEN or TODO: `N323` should demand
acquire/acq_rel on the take and release on the give.

### F3 — LOW-MEDIUM: non-triviality of the leg is argued, not proved

`w_nicht_sc` shows that on the refused configuration 1, W reaches `W1` with `W1.g = r1M1 sp0`
and takes a step whose G-part writes `tabA[0] = 0`, while the particular G successor `r1M2`
writes 3. It does **not** prove `¬ SchwachSC nP nO 0 (RufStartG nP sp0 init1) (r1M1 sp0)`,
because there is no determinism lemma for `RufSchrittG` (none exists in the tree). The
informal argument is convincing: a `blatt` step is a function of the head statement, so thread
0's only G step from `r1M1` reads 3. The leg is therefore contentful — unlike `keinKernHalt`
(§3 of the 2026-09-23 verdict), it is false of some programs. But "the leg is not true of every
program" is a sentence without a theorem. **Recommended:** `schwach_nicht_trivial` as that
negation, via a determinism lemma for `blatt` steps, or soften the header to "W takes a step G
does not take on the same schedule".

### F4 — LOW: the O17 narrowing is nominal

`poolSicherRust_iff` agrees with `N304` as implemented. `fusswache2.rs:1299–1306` checks:

* the root holds no lock by signature (`gehalten`, `requires Held`);
* the root declares no reason (`fehler.is_none()`);
* every graph write is `guarded || atomic || core`.

That is `PoolSicherRust`. Under the hypothesis `hk` (per-core ⇒ atomic) the lemma is a
propositional relabelling, and it carries the modelling choice that the N cells
`X_zellen[N]` are ONE location. The covered "write half" is a pool that only writes the
accumulator. A real `accumulates` update loads its cell first, and so does the fold, and
both are refused (`proKern_lesen_abgelehnt`). In addition, the exporter refuses
`accumulates` (`LG001`). So no per-core program is newly covered. OFFEN also cited
`schrittW_kohaerent` (read coherence) for write coherence. **Fixed in `7eec8730`** (text
only). TODO's "writes are covered" is acceptable with that reading.

### F5 — LOW: granularity and the wording of the reading assumptions

The paragraph still reads "machine G is the meaning of the C …; the hardware is DRF-SC." A hunk
follows it that withdraws the second clause. Edit the sentence in place at merge. W steps are
G's coarse steps, which has three effects:

* all reads of a step are checked against the pre-step view;
* a release message carries the view before the step's writes, so it lacks the step's own
  earlier writes;
* nothing interleaves inside a step.

The first two make W weaker than C11, which is safe. The third is exactly the old assumption
"G is the meaning of the C". "W over-approximates RC11" therefore holds at G-step granularity,
jointly with the translation-validation reading, not on its own. One clause in the header
would say so.

### F6 — INFO

* Stage (b) keeps `DRFSC` as a premise (`CNebenlaeufig.lean`), correctly recorded in TODO §2.
* The litmus facts are about `LSchritt`, not W. On W only the generic `schrittW_kohaerent` and
  `schrittW_erwerb` are proved, plus the concrete stale read `w_nicht_sc`. That is enough for
  calibration and is stated honestly.

## 4. The Spec diff, line by line

* **Imports:** + `Speichermodell.MaschineW`, definitions only.
* **(a)–(d), `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`, `GabbroZiel`:**
  unchanged (checked in `git diff ba6c16a7..203e6d08 -- grammatik/Grammatik/Zielsatz/`).
* **`Ziel`:** + `schwach : SchwachSC P O passes M0 M`. Its only constructor is `ziel_aus`, and
  the field is supplied there from `schwach_ist_g` with the premises `Akzeptiert_ok` already
  destructured (`hAbg hW hFuss hex`) and `GutO` (`hH.1`). Every consumer reads fields by name.
* **`SchwachSC`:** quantifies over every `ord`, every W state reached from `RufStartW M0` with
  `W.g = M`, and every W step. Its proof does not use M's G-reachability, because `SichtInv`
  carries its own `erreicht`. That matters for §6: the leg transfers to `ZielF.g` at `K.m`
  unchanged.
* **Non-degeneracy:**
  * W steps exist on accepted programs: `schwach_pool_zeuge`, with three real W steps lifted
    by `schrittW_aus_g` and thread 0 holding the lock after the third. Every leg holds there
    via `gabbro_ziel_schwach`, not `gabbro_ziel`.
  * The weak choice is real: `w_nicht_sc`, see F3.
  * The memory effect in the pool witness is SC-shaped (writes at `T + 1`), as expected on an
    accepted program.

## 5. Named assumptions — old versus new

| Before | After | Still needed by the proof or the reading? |
|---|---|---|
| "the hardware is DRF-SC" (reading) | (1) W ⊇ RC11 for the emitted orders; (2) compiler and hardware implement C11 atomics; (3) the lock primitive is acquire/release; (4) carriers are locations | (1)–(4) are needed. **Missing: oracle reads over SC memory (F1).** (3) is stated too narrowly (F2) |
| `atomic` "ordered by A10" | atomics excluded from `rennfrei`, `schwach` covers their values | Fine. `O.sichtbar` (A10) is still an oracle answer, see F1 |

## 6. Merge with Opus agent A (already on master, `a346748f`)

Measured with `git merge-tree --write-tree master 203e6d08`. OFFEN auto-merges, and O25 is free
because master's highest is O24. `Grammatik.lean` auto-merges.

| File | Conflict | Resolution |
|---|---|---|
| `Zielsatz/Spec.lean` | (i) the "NEW here" list: A appends `Einheit.gestartet … ZielF`, B appends `SchwachSC` and the leg; (ii) imports: `Grammatik.FadenMaschine` against `Grammatik.Speichermodell.MaschineW` | Take both: one sentence listing both additions, and both imports. The two WHAT-CHANGED blocks auto-merge (A first, B second), which is fine |
| `Zielsatz/Beweis.lean` | imports: `Zielsatz.Faeden` against `Speichermodell.DRF` | Take both. `ziel_aus` is unchanged on master, so B's `schwach :=` field merges cleanly |
| `dokumente/SATZKARTE.md` | both add **§49** | A keeps §49 (merged first) and B becomes **§50**. Update B's references to "§49": report, OFFEN O17/O25, TODO, the Spec header if cited. Keep the "(End of file …)" line once, at the end |
| `TODO.md` | the pool line: A adds the `[x]` item for threads at run time; B appends the O17 "Narrowed" sentence | Keep both: B's sentence on the O17 line, A's item after it |
| `instrumente/pruefe-akzeptiert-diff.py` | both taught the instrument the local wrapper line | **Take master's.** It is anchored (`(?m)^== 0 error\(s\) …`), a strict superset of B's in intent and stricter against false positives. Drop B's hunk |

**Semantic breaks that the textual merge will not show — build after merging:**

1. `Zielsatz/Schwach.lean`: `gabbro_ziel_schwach` calls `gabbro_ziel C D E … hL M hM`. On master,
   `gabbro_ziel : GabbroZiel` is over the thread machine (`lebt0 K hK → ZielF`), so this must
   become `gabbro_ziel_g C D E … hL M hM`. Master's `PoolZeuge.lean` made the same change.
2. `Speichermodell/Zeuge.lean`: `schwach_pool_zeuge` builds `zPool` evidence with
   `show Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] = true`. On master, `Einheit`
   has the sixth field `gestartet`, and `E.ws` may need `List.append_nil`. Master's
   `zPool_nutzerPflicht` needed that.
3. **Statement scope after the merge:** `gabbro_ziel_schwach` speaks about W runs from the
   all-live start, i.e. G runs. `ZielF.g.schwach` holds at every thread-machine state `K.m`,
   because the leg never uses G-reachability of `M`. W does not model spawn and join as
   synchronisation points (`pthread_create`/join). Under DRF by exclusion that costs nothing,
   since a child reading what its parent wrote is refused by `fuss` unless the carrier is
   guarded. The merged header should say "the weak machine over G's runs; spawn/join order not
   modelled in W".
4. `#print axioms gabbro_ziel` must be re-measured on the merged tree.

## 7. What was checked and was fine

* `w_aus_g` (every G run is a W run, with the SC shape `SCForm`), `schrittW_g`, `schrittW_bau`.
* `lies_fakten` uses guard locks held before the step, so a take and a read in one step cannot
  slip through.
* The lock view joins match `pthread_mutex` semantics: a take joins the lock's view, a give
  joins the thread's final view.
* RMW atomicity is not enforced in W (a read and a write in one step need not be adjacent in
  modification order). That makes W weaker, which is the safe direction, and it is irrelevant
  on accepted programs.
* O25's "what would close it" is a credible route. Its classification as a coverage gap, not
  a soundness gap, is correct.
