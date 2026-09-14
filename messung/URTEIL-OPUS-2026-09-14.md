# Verdict on the project goal (independent Opus reviewer, 2026-09-14)

*Base: `master` at `bb2cdde1` (worktree fast-forwarded before reading). Lean 4.33.1.
Local `lake build` of `ZielOrtStart MehrfadenZeuge MehrfadenLauf Verklemmung Schlusssatz104
ZielOrtSperreZeuge ZielOrtGanzZeuge ZielOrtZeuge`: exit 0, 88 jobs, every printed axiom
record `[propext, Classical.choice, Quot.sound]` (`schlusssatz_104_praemisse`:
`[propext, Quot.sound]`). Probe file `grammatik/.tmp/urteil_opus14.lean` (NOT committed),
checked on `ki-pc-fisch-101` with `lake env lean`: **0 errors**, all seven probe theorems
`[propext, Classical.choice, Quot.sound]`. Checker runs: the existing local binary
`target/debug/gabbro` (built 2026-09-11, i.e. BEFORE lanes 156/160-170 -- every checker
statement below that rests on it says so); no cargo, no push. The previous round's
verdicts (`URTEIL-OPUS-2026-09-13.md`, `URTEIL-MUSE-2026-09-13.md`) were read; no
`URTEIL-*-2026-09-14*` file was read.*

> **Goal (owner's words):** a Gabbro user who wants to formally verify a Gabbro program
> proves only their OWN logic plus named hardware assumptions; everything else -- memory
> safety, data-race freedom, contracts holding where claimed in concurrent runs, and
> time -- is carried by the language.

## VERDICT: **not reached**

The distance on the MODEL side shrank a lot since 2026-09-13: probes A, B and C now behave
as the goal demands against the current flagship `ziel_ort_mehrfaden_ende` (re-run below),
axiom ensures, callee frames, registers, lock invariants, table invariants, start
functions and several active threads are in ONE theorem, and deadlock freedom is proved.
It is still not "reached for the Lean model", for two reasons: **probe D** (new, §5) -- the
flagship certifies, at the `forever` budget `passes = 0` every witness uses, a program
whose emitted C violates every `ensures`; the statement leaves `passes` as free DATA where
it has to be universally quantified -- and the **time** leg is still a per-frame step
bound plus deadlock freedom, with no waiting bound and no termination. On the
IMPLEMENTATION side the chain source -> model -> C is closed for exactly one sequential
corpus program with trivial contracts (`beispiele/104`), by per-program Lean work; no
tool produces the user's obligation, the checker does not compute the flagship's
decidable premises, and nothing about the concurrent part reaches the C.

---

## 1. The previous separation list (§6 of 2026-09-13), item by item

| # | item | status | what closes it / what is left |
|---|---|---|---|
| 1 | stuck hole (loop invariants, table invariants, `vorzustand`) | **partly** | `logik` outcomes: CLOSED by `KeineLogik` in `KoerperGutZ`/`KoerperGutS` (`ziel_ort_ganz`, carried into the flagship); probe A refuted (`paP_nicht_sperre`, `paP_halt`; re-run below for EVERY `passes`). Table invariants: CLOSED (`InvGutS`, `InvAmOrtG`, `ziel_ort_sperre_inv`; refutation `ivPschlecht_verletzt`). Start functions: CLOSED for value returns (`StartEndeG`, `ziel_ort_ende`). **Reopened in a new form: a spent `forever` budget is a `hardware` outcome the obligation does not exclude, and the budget is chosen by the prover -- probe D (§5).** Termination/`abstieg`: open (named). |
| 2 | shared-state contracts across a lock; locks-block readers | **closed (model)** | lock-invariant family `SperrInv`, `execStmtH` with acquire moves `HavocOk` and release checks (`ziel_ort_sperre`); probes B and C certified BY THE CURRENT FLAGSHIP (`opusB_flagship`, `opusC_flagship`, probe file) and by `zPB_lauf` on a reached run. The move class is non-empty whenever `hSstart` + `SperrInvOk` hold (`havocOk_misch`), so no vacuity through an empty class. |
| 3 | one theorem with callee frames, registers/awaits, axiom ensures | **closed (model)** | `ziel_ort_ganz` carries `Q`/`AxVertragO`; the flagship has `hO`, `hRL`, `hQ`, `hlok` together. `RegLokal` stays strong (a device register that changes with no carrier write is outside, `audit_regwechsel_braucht_traeger`). |
| 4 | transfer to the checker; model typing vs checker (note T) | **partly** | Note T: closed IN THE MODEL (`RufPasst.hh` is `⊆` with lock floors, `HelferZeuge`), but the exporter still refuses it: `lean_g.rs:1041-1049` demands `caller_holds == callee_holds` (LG004 "`RufPasst.hh`"), and floors (`StufenOk`/`StufenM`) have no Rust rule. The flagship's footprint check `fussMehrB` (and `fussSperreB`) has NO Rust rule; the Rust rules E245-E249 compute the OLD `fussOrtGB` (hint level), which is strictly STRONGER than the flagship needs and refuses probes B/C and the witness `mP` (`mP_fussG_falsch`). `programmImFragmentG` is decided by Lean on the exported term (`example … := by decide`, `lean_g.rs:1404`), not by Rust. |
| 5 | mechanical `.gab` -> `Programm D`; obligation a user can state | **partly** | Rust exporter `gabbro lean-g` (straight-line bodies of slot writes, direct calls and a final `return`; `locks` blocks, loops, `if`, globals, devices, axioms, entries refused LG001-LG004); Lean parser/elaborator T3 (104 fragment, generic declaration lane 162); Lean statement-certificate print for 104. **No tool states `KoerperGutS`/`InvGutS` for a program**, and `gabbro prove` still targets `programmlogik/Gabbro/Body.lean` ("no heap, no separation logic, no pointers and no concurrency", `lean.rs`), with no bridge to `grammatik/`. |
| 6 | one corpus program with real sharing certified mechanically | **open** | The only corpus program through the goal theorem is 104 (sequential, one active thread). The only `concurrent` corpus file (108) has two READERS of DISJOINT tables; it is exported with its decidable checks (`Export108.lean`) but no goal-theorem instance exists. The two-writer programs (`sP`, `mP`) are hand fixtures. A `.gab` of `mP`'s shape (two `concurrent` roots, `locks K { setze(k, x) }`) is ACCEPTED by the checker (probe `zwei_ohne_inv.gab`: 8 items, 0 errors, 0 hints; 2026-09-11 binary, lock-invariant clause removed because that binary predates lane 156) and cannot be exported (LG004). |
| 7 | model -> C for the concurrent part | **open** | `schlusssatz_104` is stage (a), sequential; its CUTS: "Stage (b): concurrency (DRF-SC, lock primitives, thread creation) is not addressed". The T2 form families (`Korrespondenz.lean`) have no `locks`/`forever`/thread rows. A1-A5 are prose in a CUTS block, not premises. |
| 8 | time | **partly** | NEW: deadlock freedom `keine_verklemmungG` (from rank floors; start functions without signature locks). Unchanged: per-frame step bound (`frame_schritte_beschraenkt`), no waiting bound under a named fairness/hold-time assumption (TARGET 4), no termination, `kostenPasst` not wired to K001, no ops->cycles premise in a stated theorem. §16.6 itself: "Deadlock freedom is not starvation freedom". |

## 2. Premise table of the current flagship `ziel_ort_mehrfaden_ende` (`ZielOrtStart.lean:142`)

Classes: (a) own logic, (b) named hardware assumption, (c) decidable program fact,
(d) other. "Rust today" = computed by `crates/` on the source (the exporter printing a
Lean `decide` goal is NOT a Rust rule; it is marked "Lean via export").

| premise | class | Rust today | remark |
|---|---|---|---|
| `P : Programm D` | DATA carrying the whole typing judgement (intrinsic typing) | Lean via export for a straight-line fragment (3 corpus files pass `lean-g` per `KETTE-2026-09-13.md`); T3 Lean parser for the 104 fragment | exporter lags the model's typing (held-set equality, §1 item 4) |
| `O`, `fs`, `sp`, `init`, `Q`, `S`, `e0` | DATA | `fs`/`S` printed by the exporter; `init` NOT (the idle root is runtime data, `gP_kein_ruhig`, A4) | `e0` cosmetic |
| **`passes`** | **classified DATA; is in fact a prover-chosen assumption** | n/a | probe D (§5): must be `∀ passes` for the conclusion to describe the C |
| `K : Faden → D.Fn → Bool` | DATA (`reachB`) | no | |
| `hO : GutO O` | (b) | n/a | per axiom body |
| `hRL : RegLokal O` | (b), strong | n/a | |
| `hQ : AxVertragO Q O` | (b) | n/a | per `extern` ensures |
| `hlok : AxEnsLokal Q` | (c) | no rule found | axioms are not exportable at all (LG001) |
| `hS : SperrInvOk S` | (c) | **partly**: N275 (read half), N276 purity, N277 names (lane 156); guard half Lean via export | |
| `hvoll` | (c), trivial | Lean via export (`gFs`) | |
| `hFrag : programmImFragmentG` | (c) | Lean via export only | |
| `hAbg : ∀ t, AbgK P fs (K t)` | (c) (`abgB`) | **no** | |
| `hWurzel` | (c) | **no** | |
| `hFuss : ∀ f, FussS P S (lokK P K) f` | (c), decidable by `fussMehrB` when threads from `N` on are idle | **no** (E245-E249 compute the stronger old `fussOrtGB`, hint level) | thread-locality judged on DECLARED write permissions |
| `hK : ∀ f, KoerperGutS P passes Q S f` | (a) | n/a -- and no tool states it | sequential per function, over every frame-respecting handler, `Q`-meeting register-local oracle and `HavocOk` move |
| `hI : ∀ f, InvGutS …` | (a) | n/a | trivial without owed invariants |
| `hStart : StartGut` | (a) boot duty | n/a | |
| `hSstart : ∀ L, S.inv L sp` | (a) boot duty | n/a | |
| `hex : StartExklusiv init` | (c)/(d) | **N240** (`startexklusiv.rs`) for constant starts | |
| deadlock theorem `StufenM P` | (c) | **no** (floors are model data; H003/H006 are the analogous rank walks) | |
| deadlock theorem `hLeer` | (c) | no rule; 104/108/118 violate it (every root holds a lock by signature) | so `keine_verklemmungG` does not apply to any exported corpus program |

**Count:** of the decidable facts the flagship and the deadlock theorem need
(`hlok`, `hS`, `hvoll`, `hFrag`, `hAbg`, `hWurzel`, `hFuss`, `hex`, `StufenM`, `hLeer`, the
typed term), Rust computes **one fully (N240)** and **one partly (`SperrInvOk`, N275-N277)**;
three more are decided by Lean on an exported term. The footprint premise -- the one that
decides which concurrent programs are in -- has no Rust rule in its current form.

## 3. Vacuity and ordinary programs

**Joint satisfiability, non-degenerate: yes, on hand fixtures.** `mP_zertifiziert`
(`MehrfadenZeuge.lean`): two ACTIVE threads, private unguarded tables, a shared table
under a lock with invariant `konto[0] == konto[1]`, a caller duty provable only from the
invariant at the acquire, reached runs in `MehrfadenLauf.lean`. The move class, handler
class and oracle class are inhabited (§1 item 2). No premise is contradictory.

**But every witness fixes `passes = 0`** (`mP_zertifiziert`, `zPB_zertifiziert`,
`schlusssatz_104`), and at `passes = 0` the obligation says nothing about any `forever`
body (probe D). For the witnesses this is harmless (none contains `forever`); for the 7
corpus files with `forever` it is the whole question.

**Ordinary corpus programs:** 105 files in `beispiele/`.
* Through the goal theorem, mechanically anchored: **1** (`104-referenz`, via
  `schlusssatz_104`). Its contracts are degenerate: `einzahlen` ignores its argument `b`,
  writes the constant `100`, and its `ensures old(stand) <= stand` holds because the
  field's type is `0 .. 100`; `lies` returns the slot. It runs on one active thread.
* Exported with decidable checks but no goal instance: 108 (two readers, disjoint
  tables, signature locks), 118 (lock invariant, both functions signature-locked,
  sequential by N240).
* Cannot reach the flagship mechanically at all: every file with a `locks` block (18),
  a loop, `if`, a global, a device, an axiom or an entry (LG001-LG004). The concurrency
  repairs of §§14-16 (locks blocks, lock invariants over `locks` bodies, several active
  threads) have **no** corpus program behind them.
* Chain counter: `KETTE-2026-09-13.md` (addendum 2026-09-14) reads every-sieve 1, closed
  0; the plan (`2d9a8eb0`) books chain count 1 since `schlusssatz_104`. Not re-run here
  (it needs a current binary; the local one is from 2026-09-11; the counter's "closed"
  test is "a `Schlusssatz*.lean` names the file and re-checks green").

## 4. Faithfulness to the emitted C: what `schlusssatz_104` establishes

Statement `Schlusssatz104.lean:1395`, one premise `certOkG c = true` (discharged by
`decide` for the printed certificate). For ONE program `gP` (what the Lean parser produces
from the comment-free source string `src104`):
1. parse fidelity `uebersetze104 src104 = .ok (gP, gFs)` -- I measured that `src104` equals
   `beispiele/104-referenz.gab` with comments stripped and whitespace collapsed (python,
   equal); that equality is not in Lean;
2. the Lean print of `gP`'s two bodies IS the Rust-printed statement certificate, accepted;
3. `gP` passes fragment and (old) footprint checks and meets `KoerperGutS`/`InvGutS`
   (proved by hand, `gP_koerperS`);
4. for every C state related to ANY Gabbro world and related arguments, the
   contract-CHECKING sequential call `rufAt … = .ok` (so `requires`/`ensures` hold), the C
   call has a run, and every run ends related -- in the C semantics of `CSemantik`/
   `CSpeicher`, at the call depth the tree needs;
5. the machine runs `gPB` = `gP` renamed (proved) plus a runtime idle root; the goal
   conclusion (without `StartEndeG`) holds on every reachable machine of `gPB` from every
   start memory with thread 0 in any source function.

**Under** A1 (the compiler implements that C semantics), A2 (the C text is the hand
transcription `refCProg`; byte identity with `gabbro emit` measured on 2026-09-13, not
proved; no C parser in Lean), A3 (struct layout, bounded by `_Static_assert` pins),
A4 (the runtime starts one thread in one source function, all others idle; the driver is
not emitted), A5 (kernel + the definitions a human must read). None is a hypothesis of
the theorem; all live in the CUTS block.

**What separates it from "every accepted program":**
* everything is keyed to `gD`: `certOkG` checks FIXED rows, `printEnd104` covers the 104
  shapes, the renaming `renE`/`renEnd` is partial, `rufEin_ok`/`rufLies_ok` are
  per-program computations standing in for a general "obligations imply `rufAt` ok",
  the C bridge of part 5 is copied per function;
* the certificate's locals MAP is `gP`'s, not what `corrlean.rs` prints (the printer prints
  `refD`'s map) -- rows and layout are the printer's, the map is hand-fixed;
* parts 4 and 5 run in parallel over the same `gP`; G against `rufAt` (adequacy
  `rufG_adaequat_ruf`) is not instantiated, and part 5 has no `StartEndeG` conjunct (the
  root's `ensures` is carried only by part 4);
* stage (b) is absent: no statement about threads, the lock primitives `L_nimm`/`L_gib`,
  thread creation, or the weak memory model (DRF-SC not a premise anywhere);
* the program itself has trivial contracts and one active thread (§3).

So `schlusssatz_104` is a genuine, well-audited *existence proof of the chain shape* for
a sequential straight-line program. It is not a pipeline.

## 5. New adversarial probes

All in `grammatik/.tmp/urteil_opus14.lean` (not committed), 0 errors.

* **Probe A, re-run, strengthened.** `opusA_alle_passes`: for EVERY `passes`, `¬ ∀ f,
  KoerperGutS paP passes Q (SperrInv.leer zD) f` (the existing refutation was stated at
  `passes = 0`; `traverse` does not read the budget, so it holds at all). The flagship's
  `hK` cannot be discharged for probe A. **Closed.**
* **Probes B, C, re-run against `ziel_ort_mehrfaden_ende`.** `opusB_flagship`,
  `opusC_flagship`: every premise jointly (call graph "all functions" for every thread,
  `hFuss` from `fussSperreB` via `fussS_frei_mehr`), full conclusion incl. `InvAmOrtG`
  and `StartEndeG`. **Certified, as the goal requires.**
* **Probe D (NEW): probe A with `forever` instead of `traverse` -- CERTIFIED by the
  flagship.** `fvP` on `zD`: every function `ensures false`; every body
  `forever progress a invariant false { leave }; return`.
  `opusD_zertifiziert`: every premise of `ziel_ort_mehrfaden_ende` at `passes = 0`,
  jointly (the obligation is vacuous: `fvP_lauf0` -- the sequential `foreverLauf` at budget
  `0` answers `hardware (fortschritt a)` BEFORE the first pass, so the `zurueck` clause,
  the caller duty and the no-`logik` clause all hold; G has no rule at `ewig 0`).
  `opusD_passes1_falsch`: at `passes = 1` the same obligation is refuted (the loop is
  entered, the invariant fails) -- the certificate rests ONLY on the budget choice.
  `fwP` (invariant `true`): obligation holds at `passes = 0` (`fwP_koerper0`), while at
  `passes = 1` the body RETURNS (`fwP_passes1_zurueck`) with `ensures false`.
  **The C:** the checker accepts the surface form (`fe.gab`: `forever schleife … progress
  eingabe_endet invariant t.slots[0].v > 100 { leave schleife; } return 7;` with
  `ensures result == 5` -- 5 items, 0 errors, 2026-09-11 binary) and `gabbro emit`
  produces `for (;;) { goto schleife_ende; } schleife_ende: ; return 7;`: the invariant is
  not tested, the loop runs once, the `ensures` is violated. The same shape is in the
  corpus: `beispiele/04-schleifen.gab`, `manifest_pruefen` (`forever pruefer … progress
  eingabe_endet { leave pruefer; } return 0;`). **Diagnosis:** `passes` is a free
  parameter, classified DATA (§13.3/§14.3/§16.4), while it plays the role of a hardware
  assumption ("the environment ends every `forever` within `passes` passes"); a run in which
  the loop ends by its own `leave` after more passes than the chosen budget is
  attributed to the assumption failing, although the named assumption (`eingabe_endet`:
  "the loop ends") holds. Any finite budget has the same defect for loops that act (call
  with a violated `requires`, break an `ensures`) after that many passes. No theorem in the
  tree quantifies the obligation over all `passes` or proves budget-independence
  (`grep "∀ passes"`: none). **Repair (model, small):** state the goal as
  `∀ passes, (∀ f, KoerperGutS P passes …) ∧ … → …`, i.e. demand `hK`/`hI` for every
  budget (or prove that `forever`-free bodies do not depend on it and that the obligation
  is monotone in it), and re-classify `passes` in the premise tables.
* **Float range as a deterministic "hardware" stop (tried, failed).** A `gleit` result
  outside its declared range is `hardware ieee` in the model, i.e. would be vacuous. The
  checker refuses the deterministic case (`fl.gab`: `let y : f64 in 0.0 .. 1.0 = a * b`
  with `a, b` in `2.0 .. 3.0` -> `M101`, "the value has `f64 in 4.0 .. 9.0`"). Not a hole
  at the surface; the model alone would admit it.
* **Empty quantifier classes (tried, failed).** `HavocOk S` is inhabited whenever
  `hSstart` + `SperrInvOk` (`havocOk_misch`); the handler class by `hwRuf`; the oracle
  class needs `AxVertragO Q O` for the REAL oracle, so a false declared axiom ensures
  is a false named hardware assumption -- vacuity there is the honest kind.
* **Checker vs model on real sharing (observation).** The checker accepts the two-writer
  shape (`zwei_ohne_inv.gab`, §1 item 6); the model certifies its hand twin (`mP`, `sP`);
  nothing links the two, and the exporter refuses the `locks` block.

## 6. VERDICT: **not reached**

Neither "reached" nor "reached for the Lean model": probe D is a model defect of the same
class as last round's probe A (the flagship certifies a program whose C breaks every
`ensures`), and the time leg is not carried in the model. The implementation side is
where most of the distance is.

**Model (Lean) -- what still separates:**
1. **The `forever` budget.** Quantify the flagship over every `passes` (or prove budget
   monotonicity/independence) and classify `passes` honestly; test: probe D must fail
   (`opusD_zertifiziert` must no longer be derivable from a `∀ passes` obligation).
2. **Time.** A waiting bound under a named fairness + hold-time assumption (TARGET 4),
   termination of non-`forever` code (recursion `abstieg`), and the ops->cycles assumption
   as a premise of a stated theorem. Today: per-frame step bound + deadlock freedom
   (the latter only for start functions without signature locks).
3. Smaller, named in §§15.6/16.6: general adequacy for `else` blocks inside loops; the
   caller's shape at a pop (§13.5 item 6); `StartEndeG` for reason returns; infinitely
   many active threads (`fussMehrB` needs all threads from some `N` idle; a routine run by
   two threads never gets thread-local carriers).

**Implementation -- what still separates:**
4. **Checker rules for the flagship's decidable premises:** `fussMehrB`/`FussS` (the rules
   E245-E249 compute the obsolete, stronger `fussOrtGB`), `AbgK`/`reachB`, floors
   (`StufenOk`/`StufenM`), `hLeer`, `AxEnsLokal`; align the exporter with the relaxed
   `RufPasst.hh` (LG004 still demands equality).
5. **A general `.gab` -> `Programm D` path** beyond straight-line bodies (at least `locks`
   blocks, `if`, loops, `concurrent` with its start assignment and the runtime's idle
   root), and a tool that STATES `KoerperGutS`/`InvGutS` for the user (or a proof that the
   `Body.lean` obligation of `gabbro prove` implies them).
6. **One corpus program with real sharing** (two threads writing a lock-protected carrier,
   non-trivial contracts) through that path and the flagship -- today zero.
7. **Translation validation beyond 104 and beyond one thread:** general certificates
   (per-program pieces of `schlusssatz_104` replaced by `gcert_sound`-style general
   theorems, the printer's map fixed), G composed with `rufAt` adequacy, and stage (b):
   the lock primitives' specification, thread creation, and DRF-SC of the C/hardware
   memory model as HYPOTHESES of the theorem, with A1-A5 moved from CUTS into premises.
8. **Costs in the checker:** `kostenPasst` wired to K001 so the step bound the model proves
   is the number the checker prints.

What is real and should be said plainly: for hand-written programs in the model, with
standard axioms only, the flagship now proves requires-at-entry, ensures-at-return, lock
invariants at every free lock, table invariants at returns, start-function completion,
race freedom on guarded carriers and progress at every check, over several active
threads with private and shared state -- and the three probes that sank last round's
flagship now behave correctly. The remaining model defect (probe D) is a quantifier, not a
design flaw. The gap that decides the verdict is that none of this is yet reachable from a
`.gab` file a user writes, except for one sequential program with trivial contracts.

---
CUTS (this verdict file): proves nothing itself; the probe theorems live in an uncommitted
scratch file (`grammatik/.tmp/urteil_opus14.lean`) and in three uncommitted `.gab` scratch
files in the session scratchpad. Checker observations use the 2026-09-11 binary (before
lanes 156 and 160-170); a current binary could not be used (no cargo; running a binary
from another directory on the server was refused by the permission system). Corpus
counts are `grep` heuristics over the 105 files of `beispiele/`. No existing file was
changed.
