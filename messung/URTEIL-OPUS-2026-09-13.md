# Verdict on the project goal (independent Opus reviewer, 2026-09-13)

*Base: `master` at `896c92e1` (ZielOrtRahmen merged). Worktree fast-forwarded before any
reading. Lean 4.33.1: `lake build Grammatik.Referenz104Rahmen Grammatik.AuditFinal
Grammatik.AuditZiel Grammatik.KostenG Grammatik.RennfreiVoll` exited 0 (50 jobs, all
replayed); every `#print axioms` in them reports `[propext, Classical.choice, Quot.sound]`.
One probe, `.tmp/urteil_opus.lean` (not committed), checked with `lake env lean`: 0 errors,
axioms standard. No cargo, no ssh. One checker run on a scratch file with the existing
binary `target/debug/gabbro` (built 2026-09-11 17:58; see §1, note T).*

> **Goal (owner's words):** a Gabbro user who wants to formally verify a Gabbro program
> proves only their OWN logic, plus named hardware assumptions; everything else -- memory
> safety, data-race freedom, that contracts hold where they are claimed in concurrent runs,
> and time -- is carried by the language (its checker/model).

## VERDICT: **not reached**

Not "reached for the Lean model, not yet for the implementation" either: the Lean side
has two defects of substance that are not implementation work (§2 probe A, §3 probes
B/C), in addition to the implementation side having essentially no link to the model
(§1, §5). What *is* true, and it is real work: over machine G, with standard axioms only,
`ziel_ort_rahmen` proves requires-at-entry / ensures-at-return on every reachable machine
from premises that are mostly in the right classes; data-race freedom on lock-guarded
carriers and a per-frame step bound are proved; the witnesses are non-degenerate.

---

## 1. Every premise of `ziel_ort_rahmen`, classified

Statement: `ZielOrtRahmen.lean:1136-1143`. Classes: (a) user's own logic, (b) named
hardware assumption, (c) decidable program fact the checker should compute, (d) other.
"Rust today" = is it computed by `crates/` now.

| premise | class | Rust today | remark |
|---|---|---|---|
| `P : Programm D` | DATA, but it **carries the whole typing judgement** (intrinsic typing: `darf`/`gdarf` = H007, `RufPasst` incl. `hh`, rank order, ranges, write rights) -- effectively a (c) premise "this program has a typed term" | **no link.** The checker computes analogous judgements (M1, H006, H007, E005, ...), but nothing produces a `Programm D` from a `.gab`: statement certificates exist Lean-side for 38/49 constructors (`ZeugnisStmt.lean`), and `certemit.rs` prints expression certificates only (MUSE-REPORT-136 §"Rust side"); the parser in Lean (T3) is not started | The model's typing is **stricter** than the checker's (note T below): some checker-accepted programs have no term |
| `O`, `passes`, `fs`, `sp` | DATA | -- | |
| `init` | DATA | -- | the correspondence of Lean threads (`Faden = Nat`, all started at once, each runs its root once) to `concurrent` members and `entry`/`boot` roots is informal |
| `e0 : Ereignis D` | the docs say (d); I classify it **DATA, cosmetic** | -- | any declaration can be padded with one unused lock (`Lock := Unit`, used nowhere), which changes no run and yields `e0 := .gibt ()`. The "carrier-less programs are out" cut (24 of 91 corpus files declare no table/static/lock/atomic/format) is an artefact, not an exclusion |
| `hO : GutO O` | (b) | n/a (assumption) | axiom answers stay in the declared write frame, keep the held locks, record their trace. Legitimately named per `extern`/`asm`/`prim`/`entrust` body |
| `hRL : RegLokal O` | (b) | n/a | named, but **strong**: a register answers only from the carriers `D.rtraeger r`, and G has no asynchronous device step, so an autonomously changing status register violates it (`audit_regwechsel_braucht_traeger`). The geraet witness's contract `x == y` over two reads is exactly a property real devices break |
| `hvoll` | (c), trivial | implicit (closed world) | |
| `hFrag : programmImFragmentG P fs` | (c), Lean-decidable | **not computed.** `grep` over `crates/` finds no counterpart; `SYNTAX.md` §16.2 says "not yet a checker rule" | contentually it restricts only indirect calls (`KandOk`); every other form passes `gOk` |
| `hFuss : fussOrtGB P fs` | (c), Lean-decidable | **not computed.** Nearest rules check different things: E220/E221 (`wirkungen.rs:1439`, contract reads covered by `reads`/`writes`), H007 (guard per access), W001-W003 (`nebeneinander.rs`; its lock exemption is pair-level, "no held-set analysis exists", `saetze.rs:4119`), H013/H222 (unshared carriers) | this is the premise that decides which concurrent programs are in (§3) |
| `hK : ∀ f, KoerperGutR P passes f` | (a) -- **but incomplete as "the user's logic"** | n/a | it constrains only `zurueck` outcomes and `logik (vorbedingung _)`. Loop invariants (`logik schleife`), table/group invariants (`logik (invariante _)`), state pre-states (`logik vorzustand`) are never demanded -- see probe A. Also: no tool states `KoerperGutR` for a real program; the automated proof channel (`gabbro prove`/`gabbro lean`) targets a **different** model (`programmlogik/Gabbro/Body.lean`: "no heap, no separation logic, no pointers and no concurrency", `lean.rs:18-19`), which does not import `grammatik/` |
| `hStart : StartGut` | (a), boot duty | n/a | |
| `hex : StartExklusiv init` | (d) in the docs; (c) for finite/constant assignments | **computed: N240** (`startexklusiv.rs`, lane 137) -- the only goal premise transferred to the checker | |
| hidden in `D`: `eigner_nie_erzeugt`, `geteilt_bewacht`, `invarianten_gehalten`, `ggeteilt_bewacht` | (c), declaration well-formedness (`Syntax.lean` Deklaration) | named after checker rules (H013 etc., "U003"), no link | |

**Note T (model typing stricter than the checker).** `RufPasst.hh` (`Syntax.lean:273`)
demands that a callee's signature-held lock set equal the caller's held set exactly. The
scratch program below, where a pure helper is called both inside `locks L { … }` and from a
lock-free function, is accepted by the checker (`6 items, 0 errors, 0 hints`; binary of
2026-09-11 -- no commit since touches a held-set rule) and has **no** `Programm D` term
(no single `haelt` list for `helfer` satisfies both call sites; only a clone-per-held-set
translation would give one, and none exists):

```gabbro
impl fn helfer(x : u32 in 0 .. 10) -> u32 in 0 .. 10  ensures result == x  effects { pure } costs <= 4 ops { return x; }
impl fn frei() -> u32 in 0 .. 10  effects { pure } costs <= 8 ops { let z = helfer(3); return z; }
impl fn setze() effects { reads T.slots, writes T.slots, locks L } costs <= 40 ops
{ locks L { let y = helfer(5); T.slots[0].v = y; } }
```

**Summary of (c):** of the four decidable goal premises (`programmImFragmentG`,
`fussOrtGB`, `StartExklusiv`, the typed term), **one** is computed by the Rust checker
today (N240). None is linked by a certificate.

## 2. Vacuity

**Joint satisfiability by a non-degenerate concurrent program: yes.** `zP`
(`ZielOrtZeuge.lean`) satisfies all premises (via `ziel_ort_lokal_aus_rahmen`): every
thread runs `haupt = locks { wrap() }`, `wrap` calls `lies` (ensures `result == konto[0]`)
and `einzahlen` (ensures `old(konto[0]) <= konto[0]`), and `audit_cross_thread_return`
shows thread 0 returning a value written by thread 1. The other witnesses are weaker:
`geP` (two threads on **disjoint** tables), `r4P`/104 (thread 0 runs the driver, **every
other thread is idle** -- `r4Init`, `Referenz104.lean:325`), the `voll` witness (one
thread, `true` contracts). In every witness the contract at the lock boundary
(`wrap`, the thread roots) is `true` -- this is forced, see probe B.

**Probe A -- the conclusion is vacuous past a false loop invariant, and the premises do
not prevent it** (`.tmp/urteil_opus.lean`, `vP_zertifiziert`, `vP_nie_rueck`). On `zD`,
the program `vP` gives **every** function `ensures false` and the body
`traverse () invariant false {}; return`. All premises of `ziel_ort_rahmen` hold
(`KoerperGutR` because `execEnd … = .logik .schleife`, so the `zurueck` clause is
vacuous; fragment and footprint by `decide`), so the theorem certifies it:

```lean
theorem vP_zertifiziert : ∀ M, RufErreichbarG vP zO 0 (RufStartG vP zSp zInit) M → VertragAmOrtG vP M :=
  ziel_ort_rahmen vP zO 0 zFs zSp zInit (.gibt ()) zO_gut zO_lokal zFs_voll vP_fragmentG vP_fussG
    vP_koerperR vP_start zInit_exklusiv
theorem vP_nie_rueck … : RufEreignisF.rueck g rho v s0 s1 ∉ (M.faeden t).log
```

G never logs a return because its `dannTrav` rules fire only when the invariant evaluates
true (`RufMaschineG.lean:710, 751`) -- the thread is stuck. The emitted C does not check
loop invariants (the `traverse` lowering at `emit.rs:10424` never reads the invariant;
invariants are "named, not checked", `emit.rs:14267`): the C loop runs two passes and
returns, and every `ensures` is violated. The CUTS say "stuck states are not violations";
the point here is stronger: **a user who proves only `KoerperGutR` has not proved their
loop invariants, and the language does not carry them either** -- so "the user proves only
their own logic" is satisfied by *omitting* part of that logic. The same shape applies to
`logik vorzustand` (a `state` transition from the wrong pre-state) and to table
invariants, which are not in `VertragAmOrtG` at all (it states requires/ensures only,
`ZielOrt.lean:67`). The body channel of `gabbro prove` demands exactly the strong form
("the body runs to an end *and* the postcondition holds", `lean.rs:28-29`) -- the goal
theorem does not.

## 3. Coverage

`gOk` itself excludes almost nothing (indirect calls without `KandOk`; one corpus file,
`49-dispatch-tabelle`, uses `fn(…)` types). The effective fragment is decided by
`fussOrtGB` + `StartExklusiv` + the typed-term requirement:

* **Probe B -- no contract over shared state at a lock boundary** (`zPB_fussG_falsch`).
  In `zP`, change `wrap`'s `ensures true` to `konto[0] == 100`. This contract is true on
  every run (`wrap` holds the lock for its whole life and its last action is
  `einzahlen`, which writes 100), yet `fussOrtGB zPB zFs = false`: the caller `haupt`
  holds no lock by signature, its footprint contains `wrap`'s contract carriers, and the
  table is written. Since a thread root cannot hold a lock by signature (N240, and
  nobody would take it for the whole thread), **every function called at a lock boundary
  must have contracts that do not mention the protected carriers, and so must every
  `requires` it needs**. There is no lock/resource invariant in the model. "Contracts
  hold in concurrent runs" is therefore established only for contracts that are local to
  one critical section or to unshared state.
* **Probe C -- the canonical critical section is outside** (`zPC_fussG_falsch`):
  `haupt = locks { konto[0] = konto[0] }` (a read inside the block) makes `fussOrtGB`
  false. Corpus: 14 of 91 files take a lock inside a body; at least 04, 05 (the counter
  `locks … { if c.wert < GRENZE { c.wert = c.wert + 1 } }`), 18 and 71 read the
  protected carrier directly inside the block and fall; the others depend on callee
  contracts.
* **Concurrency in the corpus:** one file declares `concurrent` (108: two *readers* of
  *different* tables under disjoint locks); 109 has two entries writing *different*
  tables. **No corpus program with two threads sharing a written carrier is translated
  or certified.** The one certified corpus file (104) is sequential (it had to drop
  `concurrent` because N240 refuses it).
* **Same lock-holding routine on two threads** is excluded (`audit_same_lock_start_excluded`,
  now also N240).
* **Hand translation only:** 0 of 91 corpus files have a machine-produced `Programm D`;
  two hand translations exist (`ReferenzB`/`Referenz104`, the same program), with
  NO-FORM items listed in `Referenz104.lean` (constants, widths, address spaces, hold
  budget, `reads`, fall-off return, `rw`→`r` coercion, `old(p->f)`).
* **Named hardware contracts of axioms** (`extern … ensures`, 30 files use `extern`) are
  usable only in `ziel_ort_voll_ax`, which has neither callee frames nor registers; no
  single theorem combines them (`ZielOrtRahmen.lean` CUTS).

Does it undermine the goal for real programs? **Yes for concurrent programs**: the claim
that distinguishes the goal ("contracts hold where claimed in concurrent runs") is
available only for programs whose cross-thread contracts say nothing about shared state.

## 4. The four properties

| property | status | where / limits |
|---|---|---|
| memory safety | **proved in the model by construction; not proved for the implementation** | intrinsic typing: an unsafe access has no term (`zwei_fehler`, `exec_rahmen`, `SYNTAX.md` §16.1 "no thirteenth row"); G memory steps carry `HeldGenau`. Pointers are table references with value `()` (no arithmetic); the emitted C has 491 pointer-arithmetic sites with the alias obligation open (`Erhaltung.lean` §2). Checker-accepted ⇒ typed term is not linked (§1) |
| data-race freedom | **proved for the model, with limits** | `rennfrei_g_voll`/`keine_datenrasse_g` (premises `GutO`, `StartExklusiv` only): every two accesses by different threads to a lock-guarded carrier are ordered by a release/acquire of a guard. Out: unguarded (unshared) carriers by definition (Rust H013/H222 duty, unlinked), atomics and published payloads by design (A10), any C11/hardware memory model (G is an SC interleaving), the lock primitives (extern prototypes `L_nimm`/`L_gib`, `emit.rs:2479`, named in no theorem) |
| contracts at their place | **proved on G with serious limits** | `ziel_ort_rahmen`: requires/ensures only (no table/loop invariants); vacuous past `logik` stuck states the premises do not exclude (probe A); unusable for shared-state contracts at lock boundaries (probes B/C); reason returns carry no frame; axiom ensures not combined |
| time | **a step bound, not time** | `frame_schritte_beschraenkt`, `kosten_passt_deklaration`: a frame's own G-steps ≤ syntax cost / declared cost under `kostenPasst`. Not cycles; no waiting bound (fairness and hold time are named only in `KostenG.lean` CUTS, in no theorem -- TARGET 4 not stated); no termination; `forever` relative to `passes`; indirect calls excluded; `kostenK` is a hand reading of `kosten.rs`, and `kostenPasst` is not a checker rule |

## 5. Faithfulness

* **Adequacy is to the sequential semantics, and partial:** forward (`RufAdaequatG`,
  `RufAdaequatRufG`) is existential and against the contract-ignoring `rufRumpf`, needs
  `Tief` admission, excludes axioms and indirect calls; the converse (`RufUmkehrRufG`)
  covers the loop-free, axiom-free, oracle-free fragment. (The goal theorem does not need
  adequacy -- it replays internally -- but adequacy is the only evidence that G means
  what the language means.)
* **There is no link from G to the C.** `CSemantik.lean` (5 sequential forms) and
  `CSpeicher.lean` (memory model, plan step 1) do not mention `RufMaschineG`; `Erhaltung.lean`
  keeps the per-slot semantic rulings cut. The emitter produces **no threads** (MUSE-REPORT-141:
  "the emitter produces no thread notion"); threads, the scheduler and the lock
  primitives come from outside and are trusted, and none of that trust is a named premise
  of any goal theorem.
* **Known divergences G vs C:** G blocks where C continues (false loop invariant,
  `state` pre-state, spent `passes`, `leave`/`next` in `else`) -- probe A shows this
  is not harmless; G interleaves sequentially consistently while the C runs on a weak
  memory model (DRF-SC is the missing named assumption); G starts all threads at once.
* **What "translation validation planned, not done" means for the claim:** today the goal
  theorem is a theorem about hand-written Lean terms on machine G. For a program a user
  writes, nothing proves that its Lean term exists (T1/T3), that the checker's acceptance
  implies the decidable premises (two of them have no rule), or that the emitted C
  behaves like G (T2/T4, estimated 21k-52k Lean lines in `PLAN-UEBERSETZUNGSVALIDIERUNG.md`).
  The claim "carried by the language" currently means "carried by the Lean model, for a
  program someone translated by hand".

## 6. What separates the current state from "reached"

1. **Close the stuck hole (model).** The user obligation must exclude every `logik`
   outcome (loop invariant, table invariant, `vorzustand`, `abstieg`), or G must not
   block where C continues and the replay must then use the invariant. Add table
   invariants to the conclusion or name them as not carried. Test: probe A must fail.
2. **Shared-state contracts across a lock (model).** Add lock/resource invariants (or an
   equivalent) so a lock boundary can carry a contract over the protected carriers, and
   cover locks-block readers. Tests: probes B and C must become certifiable.
3. **One goal theorem** combining callee frames, registers/awaits and declared axiom
   ensures (`ziel_ort_voll_ax` ∪ `ziel_ort_rahmen`).
4. **Transfer (checker):** `programmImFragmentG` (KandOk) and `fussOrtGB` as rules with
   gifts; align the model's typing with the checker (the `RufPasst.hh` held-set
   equality, note T) -- one of them has to move.
5. **A mechanical path `.gab` → `Programm D`** (statement certificates printed by Rust,
   remaining 11 constructors, parser T3), so the user can *state* `KoerperGutR` for their
   program; and either retarget `gabbro prove` to that obligation or prove the Body.lean
   obligation implies it.
6. **One corpus program with real sharing** (two threads writing a shared carrier, with
   non-trivial contracts) certified through that mechanical path.
7. **Model → C:** translation validation for the concurrent part too: the lock primitives'
   specification, thread creation by the runtime, and DRF-SC of the C/hardware memory
   model as named assumptions in the theorem, not in prose.
8. **Time:** a waiting bound under a named fairness + hold-time assumption (TARGET 4), and
   the ops→cycles assumption as a premise of a stated theorem; `kostenPasst` wired to K001.

Items 1-3 are model work and are why the verdict is not "reached for the Lean model".
Items 4-8 are implementation work.
