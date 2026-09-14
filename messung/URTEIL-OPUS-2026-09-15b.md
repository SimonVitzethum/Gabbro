# Verdict on the repaired `GabbroZiel` (independent Opus reviewer, fourth round, 2026-09-15b)

*Base: `master` at `ad43ef5f` (the worktree already contained it). Lean 4.33.1. The server
directory is `~/gabbro-muse/opus-urteil4/` on ki-pc-fisch-101. There,
`lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben Grammatik.Zielsatz.SpecProben
Grammatik.Zielsatz.AkzeptiertZeuge Grammatik.Zielsatz.RuheZeuge` exits 0 (85 jobs).
`gabbro_ziel` prints `[propext, Classical.choice, Quot.sound]`, and so does every theorem of
`Proben.lean` except `p1_akzeptiert` and `register_ohne_traeger_konstant`, which print
`[propext]`. My probe file is `grammatik/.tmp/urteil_opus15b.lean`. It is NOT committed.
`lake env lean` on it exits 0 with 0 errors, and every probe prints either `[propext]` or
`[propext, Classical.choice, Quot.sound]`. No cargo was run and nothing was pushed. Rust
statements come from reading `crates/` at `ad43ef5f`. I read `URTEIL-OPUS-2026-09-15.md`, but no
`URTEIL-*-2026-09-15b*` file.*

> **Goal (owner):** a Gabbro user proves only their OWN logic plus named hardware
> assumptions. Memory safety, data-race freedom, contracts where claimed in concurrent runs,
> and time are carried by the language.

## VERDICT: **`GabbroZiel` is the goal with named gaps.** One of the gaps (F1) is not named yet.

**The three repairs hold, and I re-checked each with my own probes (§4).**
- **P1.** An unsatisfiable lock family now refutes (b), even when it is not constant and the
  checker accepts the program.
- **P2.** The real starts of `akP3` are refused. A duplicate start is refused.
- **P3.** Payloads are in the race leg, and only `atomic` globals are exempt.

The run class cannot be emptied, because the idle root always meets (d). Every premise now
belongs to exactly one group. For concurrency the theorem is strong. The user proves
sequential facts per function. The theorem gives them back on the interleaved machine, together
with race freedom, the global lock-invariant fact and progress. None of those three is in (b).

**One new hole is in the probe-A class: F1, a deterministic stop labelled "hardware".**
- A float literal outside its declared range ends a body in `Hardware.ieee` for EVERY oracle.
  The kernel IEEE model decides this; no machine assumption is involved.
- `KoerperGutS` constrains only `zurueck` and `logik` outcomes. So probe A with every `ensures
  false` meets (b), passes the concrete checker with `haupt` DECLARED and RUNNING, and
  `gabbro_ziel` certifies it (`hw_ziel`, §4).
- The conclusion tells no lie: nothing returns. But the header uses `fortschritt` to argue
  that "the safety legs are not vacuous by G getting stuck", and that argument fails here.
- Float range is the user's own logic under the kernel IEEE model, yet it becomes a permitted
  "hardware" stop. The header also says "no float assumption on G's side". **The class is
  neither in (b) nor honestly in (c).**

This does not empty the statement for programs without floats, and non-returning bodies are
already admitted by partial correctness (recursion, named). So it is a gap and not a refusal
of the statement. It must be named or repaired before the header's claims hold.
**Repair (small):** add `≠ EndAusgang.hardware .ieee` to `KoerperGutS`, or make an
out-of-range float result a `logik` outcome, as `narrow` already treats integers.

---

## 1. Question 1: each leg against its words

| Leg | Predicate | Verdict |
|---|---|---|
| **memory safety** | `SpurInv` | **Yes, for the model.** Every recorded access carries its carrier's guards, and those locks are held. Bounds and types are intrinsic to `Programm D`: an index has an `.index n` type, pointers are declared tables, and there is no heap. **Correction to the header.** It says this leg comes "from the checker and G". In fact `spurInv_erreichbar` needs only `GutO` (Beweis.lean:93), so the leg holds for EVERY well-typed program of G. It is carried by the intrinsic typing, which is literally "by the language", but only for Lean terms. Its force for a `.gab` file rests entirely on `.gab → Programm D` (§5). Stack depth is not covered (named). |
| **data-race freedom** | `RennfreiBis` | **Yes.** Every pair of accesses to one carrier by different threads, with at least one write, is lock-ordered (release, then acquire). This holds for every carrier except `atomic` globals. Payloads are included since P3. The granularity is the whole table or global, which is conservative. The one exemption is A10 on atomics, and it rests on the emitted C using seq_cst atomics (§5). |
| **contracts where claimed** | `vertrag`, `sperrInv`, `invRueck`, `invGrund`, `startEnde`, `keinStartGrund`, `keinLogikHalt` | **Yes, as partial correctness.** `requires` holds at every logged entry, `ensures` at every logged value return, and owed invariants at value and reason returns. `startEnde` is partial: IF the start frame returns, its `ensures` holds. `keinLogikHalt`: no thread stops at a loop-invariant or transition check. **Weaker than the words:** a body that never returns meets any `ensures`, whether by recursion (named), by a `forever` without `leave`, or by a stop the user caused (F1, not named). |
| **progress** | `keineVerklemmung`, `fortschritt` | **Weaker than the words, in two ways.** **(F2)** `keineVerklemmung` reads `(∀ t, ¬Fertig → Wartet) → ∀ t, Fertig`, which is GLOBAL deadlock only. At a machine where two threads wait on each other while a third can step, the premise is false, so the leg holds. Lock ranks rule out such cycles anyway (the proof, `rangInvG_erreichbar`, is a rank argument), but the STATEMENT does not say so. **(F3)** `HaltBenannt` counts as a "hardware" stop an `awaits` whose flag is not visible (`Hardware.sichtbarkeit`), and an out-of-range float (F1). An `awaits` on a flag that no thread ever publishes is a program bug, and it is reported as a hardware stop. The same holds for a thread stopped at F1 inside `locks L`: every other thread that needs `L` then satisfies `WartetG` forever, and `Ziel` holds. |
| **time** | `ZeitAb` | **Much weaker than the word** (named). It bounds the thread's own G-steps by the syntax-computed `kostenTief`, only for frames with a finite call tree. `forever` is bounded by `passes`, which is universally quantified, so that is no bound. It holds for every program of G with no premise, it counts no waiting, and it does not use the declared `costs`. The §21 waiting bound is not in `Ziel`. |

## 2. Question 2: what `Ziel` gives beyond `NutzerPflicht`, leg by leg

(b) is sequential: `execEndH` for one body, against every callee answer meeting the callee's
contract, every oracle in the (c) class, and every lock move keeping the invariant. On top of
that, `Ziel` gives:

1. **speicherSicher.** Not in (b). It comes from G plus the typing, and needs no checker (see §1).
2. **rennfrei.** Not in (b). It comes from the checker (`fuss`, `renn`), the start, and G. This
   is real content: the checker's syntactic facts become a run-level DRF fact on an
   interleaved machine.
3. **The contract legs.** (b)'s sequential clauses, carried to the interleaved machine G. This
   is the core of "contracts where claimed in concurrent runs". Other threads interfere only
   through `HavocOk` moves at `locks`, and through carriers the checker proved thread-local.
   For single-threaded, lock-free code these legs are close to a restatement of (b), as the
   header says.
4. **sperrInv.** New. Every free lock's invariant holds in shared memory at every reached
   machine.
5. **keineVerklemmung and fortschritt.** New, with the weakenings F2 and F3.
6. **zeit.** New but weak (see §1).

**Is that enough to call the theorem strong?** For concurrency, yes. Items 2 to 5 are a sound
lift of a CSL-style lock-invariant discipline to a concrete interleaved semantics, and the user
never reasons about interleavings. It is not strong for time. It is not strong for crash
freedom: there is no leg saying "no stop the user caused", and F1 shows such stops pass as
hardware. It is not total correctness, which is named.

## 3. Question 3: premise groups, and whether each assumption really is hardware or runtime

| Premise | Group | Remark |
|---|---|---|
| `C.akzeptiert E … = true`, for every `C` | (a) | Still decoration, as in round 3: the quantifier over `Pruefer` makes (a) the Prop `AkzeptiertSpec E.P E.S fs E.ws`. The concrete Lean Bool `akzeptiert_pruefer` exists and is decidable. |
| `LogikPflicht` | (b) | `KoerperGutS`, `InvGutS` and `InvGutGrund` hold at every budget, which closes probe D. `SperrInvLokal` and `AxEnsLokal` are really well-formedness checks on the specs the user wrote; putting them in (b) is harmless but misfiled. |
| `StartPflicht` | (b) | **Correctly the user's.** It fixes P1. It is stated over `E.sp0` and `E.starts`, both fields of the program. |
| `GutO` | (c) | Foreign code (`extern`, `prim`, `asm`, `entry`, `entrust`). That is **software**, not hardware, but it is not Gabbro code and it is named ("hardware and foreign code"). The owner's sentence says only "hardware", so this is a named widening. |
| `RegLokal` | (c) | **Stronger than hardware** (named, not repaired). A register without `depends` is constant in every world (`register_ohne_traeger_konstant`). Even with `depends`, an autonomous device change is invisible unless an axiom writes the carriers. A polling loop on a status register, the common driver shape, is modelled wrongly, and user proofs may exploit `r1 == r2`. The user sits inside the same quantifier (`KoerperGutS: ∀ O', RegLokal O' → …`). |
| `AxVertragO E.Q` | (c) | The contract of foreign code or a device, written by the user and visible. **Header imprecision:** "`Q := false` makes (c) unsatisfiable" is true only for axioms without a result. For an axiom with a result, `AxVertragO` constrains only answers that fit the type (`einpassenErg … = some v`). So (c) stays inhabited by oracles that answer out of type, and every call then stops at `Hardware.annahme`. Both readings are honest vacuity. The sentence should say which one applies. |
| `Laufzeit.lader` | (d) | Loader or toolchain. Really runtime. |
| `Laufzeit.start` / `.einmal` | (d) | Thread creation. Really runtime, and it covers every subset of the declared starts. The restrictions are named: one thread per busy start, starts without signature locks or reasons (`wurzeln`), no SMP-symmetric code. |
| `fs`, `ls`, `cs` as `Aufzaehlung` | by type | Harmless. |
| `passes`, `O`, `sp`, `init`, `M` | ∀ | Correct. |

**A second assumption channel that the ONE list does not list.** `HaltBenannt`/`KopfHardware`
permits six stop classes in the conclusion. Each is a place where the theorem gives up. The
ONE list should name them, each with its justification:

| Stop class | What it is |
|---|---|
| `annahme` | An axiom answers outside its type. Foreign code, fine. |
| `register`, `geraet` | A register answers outside `D.rtyp r`, or against `D.rzusage r`. This is the device plus a promise the user declared. Honest, but `rzusage` is a hardware assumption that is absent from (c). `requires false` on a register makes every read a stop, the same honest vacuity as `Q := false`. |
| `sichtbarkeit` | A10. It also covers a flag that is never published (F3). |
| `fortschritt` | The `forever` budget. This is an artifact of G and not hardware. It is harmless because `passes` is universally quantified. |
| **`ieee`** | **Not hardware under the kernel IEEE model: F1.** |

## 4. Question 4: adversarial probes (`grammatik/.tmp/urteil_opus15b.lean`, 0 errors)

**F1: probe A through a deterministic "hardware" stop. NEW, NOT NAMED.**
```lean
def crash : Stmt zD V false Γ Λ Λ := .ite .wahr (.gleitLit (2, 1) (0, 1) (1, 1) .nil) .nil
def hwP : Programm zD where                        -- every `ensures false`
  invariante := fun i => nomatch i; requires := fun _ => .wahr; ensures := fun _ => .falsch
  rumpf f := .cons crash (paP.rumpf f)
def hwE : Einheit zD := ⟨hwP, zS, axWahr zD, [⟨zHaupt, .nil⟩], zSp⟩
```

| Probe | What it shows | Axioms |
|---|---|---|
| `lit_ausser` | `gleitPasst (0,1) (1,1) (bruch (2,1)) = none`, by `rfl` | `[propext]` |
| `hw_lauf` | `execEndH S O' U passes R (hwP.rumpf f) σ ρ = .hardware .ieee` for EVERY `S`, `O'`, `U`, `passes`, `R`, `f` | |
| `hw_nutzer` | `NutzerPflicht hwE` | |
| `hw_akzeptiert` | `Akzeptiert hwP zS zFs [()] [.inl ()] [zHaupt] = true` | `[propext]` |
| `hw_erfuellbar` | `Erfuellbar hwE`: all four groups jointly, with the declared start running on a thread | |
| `hw_ziel` | `gabbro_ziel akzeptiert_pruefer` applied: every leg on every run | `[propext, Classical.choice, Quot.sound]` |

This is the round-3 P1 shape (probe A accepted, (b) met), with one difference: the start is
admissible and runs, and it stops at once at a stop named "hardware".

The float forms are in the fragment. `Block.gOk` passes `gleit*`, and `gleitLit` carries no
proof that its value is in range (Syntax.lean:574). The same holds for `gleit op`: a
user-declared result range that the computation leaves is `Hardware.ieee`, while integers get
intrinsic ranges or `narrow … else`. Whether the Rust checker refuses a literal outside its
range was not checked.

**P1 closed** (own probe, beyond the shipped constant `sFalsch`).
- `sUnerf := ⟨fun _ => [.inl ()], fun _ s => decide ((s.slots () 0 ()).n = 101)⟩` is a
  NON-constant family that reads the protected table. No memory satisfies it, because the
  field type is `0..100`.
- `sUnerf_akzeptiert`: the Bool accepts probe A under it.
- `sUnerf_widerlegt`: every `E` with that family fails (b), through `StartPflicht.sperren` and
  the type bound (`omega`).
- `havocOk_bewohnt` (shipped) makes the move class inhabited under (b), for every family. The
  (b) oracle class contains the (c) class (`GutO → RahmenO`). So whenever (c) is inhabited, the
  oracle quantifier of (b) is too, and no choice of `Q` empties (b) without also emptying (c).

**P2 closed.**
- `akP3_zwei_abgelehnt`: `Akzeptiert akP3 akS akFs [()] akCs [akA, akB] = false`. The real
  starts are refused.
- `doppelt_abgelehnt`: `[zHaupt, zHaupt]` is refused (`einzeln`).
- `laufzeit_nur_erklaert` ties every busy thread to `E.starts`. `ws = []` is now "a different
  program" that runs nothing.
- **Remaining:** this is honest only if a tool produces `E` from the source. None does: the
  exporter writes `requires := fun _ => .wahr` (lean_g.rs:2803), and it never emits an
  `Einheit`, `starts` or `sp0` (§5).

**P3 closed, by reading.**
- `RennfreiBis` and `AkzeptiertSpec.renn` mention only `AtomarAusgenommen`.
  `PaarungAusgenommen` survives only in older files (`RennfreiVoll.lean:658`, `RennfreiG.lean`),
  which `Spec.lean` does not use for `Ziel`.
- `zwei_schreiber_abgelehnt_gilt` covers payloads.
- The conclusion quantifies every access pair, so a gap in the `fuss` argument could not hide
  in the statement.
- **Price (named):** the publish/await hand-off of an unguarded payload is refused, so
  `publishes`/`awaits` is useful across threads only for guarded payloads.

**Other user-controlled choices tried, with no new defect:**

| Choice | Result |
|---|---|
| `sp0` | Only a field of the program. (d) forces the machine to start from it, and (b) must hold there. |
| `starts` | `[]` is honest, with nothing running. Duplicates are refused. Starts with signature locks or reasons are refused (coverage, not vacuity: `beispiele/104` is covered only by idle roots, `gP_akzeptiert` with `[]`). |
| `mitRuhe` | The root writes nothing and has `requires true`. It makes (d) always satisfiable (`laufzeit_ruhe`), so satisfiability of (d) is no evidence of content. The shipped positives rightly demand that every declared start runs (`Erfuellbar`). |
| `Pruefer` | Every `C`, so no choice. |
| The oracle class | See P1 above and the `Q`/`rzusage` rows in §3. Only a false, visible, named assumption empties it. |
| A callee with `requires false` or `ensures false` | Standard modular partial correctness. |
| Recursion or `forever` without `leave` | Meets any `ensures`. This is partial correctness and is named (stack depth, termination). |

## 5. Question 5: the distance between the model and the binary

- **The checker.** `C.akzeptiert` is the Lean Bool. The Rust checker computes neither
  `einzeln` nor `wurzeln` (N240 bans only COMMON signature locks between starts; no rule bans
  a start's own signature lock or its reasons), nor the payload-inclusive `renn` as one Bool.
  H013 is stricter per entry. The two disagree in both directions: in round 3, `beispiele/108`
  was accepted by Rust and refused by the Lean Bool. Nothing in `crates/` computes
  `Akzeptiert`.
- **The program.** No `.gab` file reaches an `Einheit`. The exporter drops the source
  `requires`, and produces neither `starts` nor `sp0` (lean_g.rs:81, :365, :2803). Every
  covered program is a hand-written term (`mE`, `zEB`, `zEC`), contrary to PLAN §4, which asked
  for an exported witness. Memory safety and intrinsic typing are proved of Lean terms. For a
  binary they rest on T3 (a Lean parser) and T1 (certificate soundness).
- **The C side.** T1–T5 are open. The chain count is 1 of 101: `schlusssatz_104`,
  single-threaded, with its own machine and start premise. It does not compose with
  `GabbroZiel`: under `GabbroZiel`, 104 runs only idle threads. Stage (b) (DRF-SC, the lock
  primitives, thread creation and seq_cst atomics for A10) is not started. So the number of
  programs with BOTH a closed C chain AND a non-vacuous `GabbroZiel` instance is **0**.
- **What may be said.** *"The goal theorem is proved over the model, with a witness and
  non-degeneracy."* Not: *"Gabbro is verified."* README §6 says exactly this.

## 6. The gaps

**Not named, to be named or repaired:**
1. **F1: `Hardware.ieee` is deterministic in G.** Float-range logic is neither in (b) nor
   really in (c). It lets probe A through, with a running start. Repair: one conjunct in
   `KoerperGutS`, or make out-of-range floats `logik`. Then correct the header's "no float
   assumption on G's side" and the `fortschritt` anti-vacuity argument.
2. **F2: `keineVerklemmung` is global deadlock only.** Repair: state that no set of waiting
   threads waits in a cycle, or that the holder of a lock some waiter needs is not waiting.
   The rank proof should carry it.
3. **F3: an `awaits` on a never-published flag is a "hardware" stop.** It should at least be
   named as a program-level wait that is not covered.
4. **The permitted stop classes** belong in the ONE assumption list, each with its
   justification (§3).
5. **Header corrections:**
   - `speicherSicher` needs no checker.
   - "`Q := false` makes (c) unsatisfiable" is true only for axioms without a result.

**Named, and may stay named:**
- time as a syntactic step count of the thread's own G-steps: no waiting bound, no declared
  `costs`, no termination;
- stack depth, and partial correctness through recursion;
- `RegLokal` register constancy, and autonomous device change;
- `GutO` and `AxVertragO` as foreign SOFTWARE assumptions under the name "hardware";
- one thread per busy start, and starts without signature locks or reasons;
- invariants at returns only;
- the publish/await hand-off refused for unguarded payloads;
- weak memory beyond DRF-SC, and A10 on atomics;
- the exporter produces no `Einheit`, and covered programs are hand-written;
- the Rust checker does not compute `AkzeptiertSpec`;
- T1–T5, a chain count of 1, and no program with both a chain and a busy `GabbroZiel` start.

---
CUTS: this file proves nothing by itself. The probe theorems live in the uncommitted
`grammatik/.tmp/urteil_opus15b.lean`, checked on ki-pc-fisch-101 with EXIT 0 and 0 errors. The
server's `.lake` came from `stage/lake3`, and lake REPLAYED the Zielsatz modules on matching
traces instead of recompiling them. Rust behaviour comes from reading source; no checker
binary was run. F2 and F3 are from reading the definitions: no machine exhibiting them was
constructed. Probe A through recursion is from reading (the header names it); it was not built.
No existing file was changed.
