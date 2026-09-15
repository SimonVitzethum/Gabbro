# OPUS-BERICHT-PFLICHT — the transfer chain closed on two real programs

*Opus agent `pflicht`, 2026-09-15. Server directory `gabbro-opus-pfl`. Branch
`worktree-agent-a8a6796ff39c017ab`. NOT merged, NOT pushed.*

**The task:** lane 198 made `gabbro lean-g` produce a full `Zielsatz.Einheit gE` and `gabbro
obligations --g` state `NutzerPflicht gE` beside the per-program theorem `gP_gabbro`. The
missing middle link was the PROOF of that duty over the new export — in particular the
`LogikPflicht` body triples at every budget, which lane 198 explicitly left open.

**It is closed, for `beispiele/104-referenz.gab` and `beispiele/108-disjoint-start-locks.gab`,
with no open hypothesis but the named hardware and runtime ones — and those two are
discharged here as well.**

## Files touched (complete list)

| File | What |
|---|---|
| `grammatik/Grammatik/GenOblig104.lean` | **REGENERATED** from the current exporter (+96/−84). Byte-identical to `gabbro obligations --g beispiele/104-referenz.gab`. |
| `grammatik/Grammatik/GenOblig108.lean` | **NEW**, generated (234 lines). Byte-identical to `gabbro obligations --g beispiele/108-disjoint-start-locks.gab`. |
| `grammatik/Grammatik/Pflicht104.lean` | **MIGRATED** to the new export (ported, not replaced — see §"port or replace"). |
| `grammatik/Grammatik/Pflicht108.lean` | **NEW**. |
| `grammatik/Grammatik.lean` | two imports added. |
| `instrumente/pruefe-genlean.py` | **NEW** guardian. |
| `README.md` | guardian row: 42 → 43, 68/71 → 69/72 (re-measured). |
| `TODO.md` | the lane-198 item records the closed middle link. |
| `dokumente/SATZKARTE.md` | §34. |
| `messung/RUECKLAUFWERTE.md` | 65/71 → 66/72 guardians that can cut mid-run, 409 → 414 exit places. |
| `messung/muse/OPUS-BERICHT-PFLICHT.md` | this file. |

**Not touched:** `crates/gabbro-check/src/lean_g.rs`, `obligations_g.rs`, `Parser/`, `m1.rs`,
`saetze.rs`, `emit.rs`, `MARKE_EMIT`. **No Rust source was changed at all.**

## 1. What is proved, conjunct by conjunct

`Zielsatz.NutzerPflicht E` (`Zielsatz/Spec.lean:523`) is
`logik : LogikPflicht E.P E.S E.Q` and `start : StartPflicht E`, where
`LogikPflicht = (∀ passes f, KoerperGutS ∧ InvGutS ∧ InvGutGrund) ∧ SperrInvLokal S ∧ AxEnsLokal Q`
and `StartPflicht = ⟨sperren, req⟩`.

| Conjunct | 104 (`oblig_*`) | 108 (`p108_*`) |
|---|---|---|
| `logik.1` **`KoerperGutS`**, every budget | `oblig_koerper` — `koerperGutS_ohne` (no body holds `locks`) over `KoerperGutZ`, lifted to every budget by `koerperGutS_alle` (no `forever`: `oblig_ohneEwig`). `einzahlen` by frame reasoning against the declared frames (`oblig_einzahlen_R`), `lies` by `KoerperGutV` (`oblig_koerper_lies`); the no-`logik` half by `programmLogikFrei_ok`. | `p108_koerper` — same skeleton; both bodies are one `return <slot>`, so `p108_koerperV` closes the value half by `p108_ens` and the `logik` half by case analysis on the `.ret`. |
| `logik.1` **`InvGutS`** | `oblig_inv` = `invGutS_leer rfl` (`gD.invs = []`) | `p108_inv`, same |
| `logik.1` **`InvGutGrund`** | `oblig_invGrund` = `invGutGrund_ohneGrund` (neither function declares a reason) | `p108_invGrund`, same |
| `logik.2` **`SperrInvLokal S`** | `oblig_S_lokal` — the exported family for lock `M` is `fun _ => true`, so it reads nothing | `p108_S_lokal` — this declaration has no lock at all |
| `logik.3` **`AxEnsLokal Q`** | `oblig_ax_lokal` = `axEnsLokal_wahr` (`gE.Q` is the constantly true family; `gD.Ax = Empty`) | `p108_ax_lokal`, same |
| `start.sperren` | `oblig_start_sperren` | `p108_start_sperren` |
| `start.req` | `oblig_start_req` — **VACUOUS**: `gE.starts = []` | `p108_start_req` — **two declared starts**, `read_a` and `read_c`, `requires` `true` at `gSp0` with their declared `.nil` arguments |

**Nothing is assumed.** `oblig_nutzer : Zielsatz.NutzerPflicht gE` and
`p108_nutzer : Zielsatz.NutzerPflicht gE` take no hypothesis. That they are the SAME
proposition the tool states is pinned by `oblig_nutzer_ist_stated : G104_…_oblig.nutzerPflicht`
and `p108_nutzer_ist_stated` — the exporter's `def` and the user's theorem, held against each
other rather than restated.

## 2. The closing theorems

`oblig_ziel` and `p108_ziel` apply the exporter's own `gP_gabbro` and give
`Zielsatz.Ziel gE.P.mitRuhe gE.S.mitRuhe O.mitRuhe passes (RufStartG …) M` at every reachable
machine. All three premises of `gP_gabbro` are discharged in the file:

* the user's duty — §1 above;
* **`Zielsatz.HardwareAnnahmen O gE.Q`** (`oblig_hw`, `p108_hw`) — `gD.Ax`, `gD.Reg` and
  `gD.Glob` are all `Empty` in both declarations, so every oracle meets it, this one included.
  *This is the named hardware assumption, and on these two programs it is empty rather than
  believed.*
* **`Zielsatz.Laufzeit gE sp init`** (A4) — `laufzeit_initRuhe gE (by decide)`, i.e. the
  runtime's OWN start: the loader establishes `gE.sp0`, the declared starts run on threads
  `0 …`, the idle root everywhere else.

So the remaining hypotheses of `oblig_ziel`/`p108_ziel` are only `passes`, the machine `M` and
its reachability — nothing about the program, the hardware or the runtime.

## 3. Witnesses (rule 13) — non-degenerate

**104:**

* `oblig_ruf_bewegt` — `einzahlen(k, 0, 7)` from the DECLARED initial memory ends `ok` and
  moves the slot `0 → 100`. The duties are duties over a program that does something.
* `oblig_ens_faellt` — the exported `ensures` of `einzahlen` (`old(stand) <= stand`) **FAILS**
  on the return world that lowers the slot from `100` to `0`. *A duty no world can break would
  say nothing about the body.*

**108:**

* `p108_starts_laufen` — in the start configuration `p108_ziel` speaks about, thread `0` runs
  `read_a` and thread `1` runs `read_c`.
* `p108_starts_zwei` — `gE.ws = [read_a, read_c]` and the two are different functions (not one
  counted twice).
* `p108_ruf_liest` — `read_a` answers slot `0` and `read_c` answers slot `1` of the one shared
  table, both `ok`, both from `gSp0`.

## 4. THE FINDING — 104's goal theorem is true about an IDLE machine

**Stated as a finding and not repaired by weakening the duty**, as the task demands.

`beispiele/104-referenz.gab` declares no `concurrent` block and no `entry`/`boot` root. The
exporter therefore writes `starts := []`. That is FAITHFUL to the source — 104 says its two
functions both hold `M` by signature and deliberately declares no thread (the file's own header
says so, citing N240). But it has a consequence that must be said out loud:

> `Zielsatz.Laufzeit gE sp init` demands `∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, …`.
> With `E.starts = []` the right disjunct is unsatisfiable, so **every** admissible start
> assignment runs the runtime's idle root on **every** thread. `oblig_ziel` is a true theorem
> about a machine in which nothing of 104 runs, and its concurrency legs (`rennfrei`, no
> deadlock, `KeinWarteZyklus`) and its contract legs carry no weight there.

Equally, `StartPflicht.req` on 104 is vacuous for the same reason — the table in §1 says so
rather than hiding it behind a green tick.

**Is this a defect of the exporter?** No — and that is the measured part of the answer. The
exporter's `starts` is the faithful image of what the source declares, and `Spec.lean` says
explicitly that a different `starts` is a DIFFERENT program (`laufzeit_nur_erklaert`). The
honest repair is not to invent a start for 104 but to put a program beside it that declares
one — which is exactly what `Pflicht108.lean` is. **`beispiele/124` was the other candidate and
is not one:** `gabbro lean-g` refuses it with `LG004` (a floored caller into a floorless
callee), confirmed here, so 108 is the only concurrent demonstration available today.

**What this means for the claim that may be made:** "the goal theorem holds for this program,
with the user's duty proved and the hardware/runtime assumptions discharged" is true for 104
and for 108. "…and its concurrency guarantees were exercised" is true only for 108.

*Second, smaller observation, also about the exporter rather than the proof:* the generated
first line echoes the program path AS GIVEN on the command line, so a generated file produced
with an absolute path is not byte-identical to one produced with a repo-relative path. The
guardian below pins the repo-relative spelling (it passes the path exactly as the marker
spells it, from the tree root). Found by the guardian on its first real run — it reported a
finding about the caller's working directory, which is the `W16` class, and the fix is in the
guardian and documented there.

## 5. Port or replace — the measurement the task asked for

`Pflicht104.lean` was **ported, not replaced**, and the cost says why:

* Its §1 and §2 (the `KoerperGutZ` proofs, 110 lines of frame reasoning about `einzahlen`,
  and the budget lift) needed **zero** changes: the exported `gD`, `gP`, `gS`, `gFs`, the body
  and contract definitions and the `gDarf_*`/`gHp_*` lemmas all kept their names and their
  types across the regeneration. Only the four names the old obligation section defined
  (`pflicht`, `pflichtInv`, `startPflicht`, `gP_ziel`) disappeared, and those are exactly the
  ones the new `NutzerPflicht`/`gP_gabbro` replace.
* Its §3 (the old `oblig_chain`) was **replaced**, and is smaller for it: the old chain kept
  `StartExklusiv` as an open hypothesis and assembled the conclusion by hand from
  `ziel_ort_sperre_ende` with thirteen arguments; the new one is
  `gP_gabbro oblig_nutzer oO oblig_hw passes _ _ oblig_laufzeit M hr` and has no
  start-configuration hypothesis at all, because the goal theorem derives exclusivity from the
  DECLARED starts.

So: port. Rewriting §1 from scratch would have cost the 110 lines again for no gain.

## 6. The guardian — `instrumente/pruefe-genlean.py`

**Why.** `GenOblig104.lean` and `GenOblig108.lean` are proved against. The proofs are about the
COMMITTED TEXT. If the exporter moves and the committed file does not, the proofs stay true and
stop being about this tree. That is the same hole `instrumente/pruefe-ctext.py` closes between
`emit.rs` and the pinned C — this is that idea on the generated Lean, and it is the only reader
that closes the loop between `lean_g.rs`/`obligations_g.rs` and the files `gabbro_ziel` is
applied in.

**How it finds its work.** From the file itself: a generated file names its generator in its
FIRST line, because the generator writes it there
(``-- GENERATED by `gabbro obligations --g beispiele/104-referenz.gab` …``). The marker counts
only on line 1, so a file that merely quotes the sentence is not a generated file, and
`Export108.lean` — a deliberate PARTIAL paste with its imports dropped — carries no marker and
is not measured, rather than being measured wrongly. **No register beside the tree**: a second
list over one thing is the half that ages (W7).

**The three exits** are `pruefe-ctext.py`'s: `0` green, `1` a finding with the first differing
byte printed, `2` ABBRUCH (no binary, stale binary, no generated file, generator silent past
the 120 s deadline). `LC_ALL=C`; work count beside the verdict.

**Measured.**

| Run | Result |
|---|---|
| `--probe` (speech test only) | 7 of 7 directions ok, exit 0 |
| real run on fisch | `2 of 2 generated files byte-identical, 18 582 bytes`, `== GENLEAN: GRUEN ==`, exit 0 |
| **red direction, on the real object**: one space inserted in `GenOblig104.lean` | `BEFUND … first difference at byte 6451`, `1 BEFUNDE`, exit 1 |
| after restoring the byte | green again, exit 0 |
| `pruefe-waechter.py` | `ok pruefe-genlean.py` — all four static requirements |

## 7. Everything measured

| Run | Result |
|---|---|
| `lake build` (whole library, fisch `gabbro-opus-pfl`, warm cache) | **254 jobs, exit 0**, 0 errors, no new warning |
| `#print axioms` on `oblig_logik`, `oblig_nutzer`, `oblig_ziel`, `oblig_ruf_bewegt`, `oblig_ens_faellt` | `[propext, Classical.choice, Quot.sound]` each |
| `#print axioms` on `p108_logik`, `p108_nutzer`, `p108_ziel`, `p108_starts_laufen`, `p108_ruf_liest` | `[propext, Classical.choice, Quot.sound]` each |
| `#print axioms gabbro_ziel` | `[propext, Classical.choice, Quot.sound]` — **unchanged** |
| `sorryAx` anywhere in the build log | **0** |
| `cargo test --no-fail-fast` (whole workspace, fisch) | **1024 passed, 0 failed, exit 0** |
| `pruefe-genlean.py` | green, 2 of 2, 18 582 bytes |
| `pruefe-waechter.py` | 69 of 72 carry the four static requirements (was 68 of 71); the new guardian `ok` |
| `pruefe-todo.py` | 13 findings here **and 13 on a throw-away tree at `HEAD`** — identical |
| `pruefe-zahlen.py` | 24 findings here, **24 on the throw-away tree at `HEAD`, the same 24 line for line** (`diff` empty). The two that this work introduced — the instrument counts in `README.md` and the two figures in `messung/RUECKLAUFWERTE.md` — are booked, not left standing. |
| `pruefe-englisch.py`, `pruefe-zitate.py`, `pruefe-kennungen.py`, `pruefe-syntax.sh` | last line identical to the throw-away tree at `HEAD` in each case |

*The baseline is MEASURED and not assumed:* `git archive HEAD` into a scratch directory, the
same guardians run there, the finding lists compared with `diff`. Booking only one's own
increment leaves a wrong number that looks booked (`RUECKLAUFWERTE.md`'s own note on the same
line says so).

## 8. What is still open

1. **Two programs are not the corpus.** The width — how many of the exportable corpus programs
   can carry a proved `NutzerPflicht` — is not measured. What is measured is that the two that
   matter for the transfer chain do.
2. **`beispiele/124` still does not export** (`LG004`). Booked in lane 198's report; unchanged
   here, and not worked on.
3. **The `LogikPflicht` proofs are hand-written per program.** Nothing here generates them.
   The body-triple proof for `einzahlen` is 60 lines of frame reasoning; a program with a real
   loop or a real lock section would be far more. That is the next cost to attack, not a gap in
   what is claimed.
4. **`pruefe-genlean.py` measures only files that carry the generator's first line.**
   `Export108.lean` (a partial paste) is therefore NOT covered — deliberately, since it is not
   byte-comparable, but it is a real uncovered surface and is named here rather than left
   silent.
5. `abnahme.py --voll`, `pruefe-emission.sh` and the Isabelle run were **not** run (no emitter,
   no corpus and no proof file was touched).
