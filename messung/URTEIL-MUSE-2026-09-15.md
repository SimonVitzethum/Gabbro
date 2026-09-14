# VERDICT: IS GabbroZiel THE GOAL? (lane 189, third independent review, 2026-09-15)

Owner's goal: "a Gabbro user proves only their OWN logic plus named hardware
assumptions; memory safety, data-race freedom, contracts where claimed in
concurrent runs, and time are carried by the language."

**Verdict: `GabbroZiel` is the goal with named gaps (list in §6).**

As a STATEMENT, `GabbroZiel` (`grammatik/Grammatik/Zielsatz/Spec.lean:317-330`,
proved as `gabbro_ziel`, `Zielsatz/Beweis.lean:112-116`) says the four legs and
nothing weaker (§1), its premises sit in exactly one group each (§2), and
adversarial emptying fails everywhere I probed except two acknowledged
joint-vacuities that the witnesses guard (§3). As a PROJECT STATE, the language
does not yet carry what the statement carries: the checker Bool has no Rust
rule, the user obligation has no tooling, the C link is one single-threaded
program, and time is own-step bounds (§§2, 4, 6).

Base: branch `muse/189`. No existing file changed. Probes:
`.tmp/sonde189.lean` (scratch, not committed): `./lean-probe` **0 errors**
(`prueferFalsch`, `sperrInvFalsch`, `startZulaessig_falsch_unsat`,
`havocOk_falsch_leer`, `axVertragO_mono`; axioms standard, §3).
`./lean-bau`: **Build completed successfully (224 jobs)**.
I did NOT read `messung/URTEIL-OPUS-2026-09-15*`.

## 1. Does `Ziel` say the four legs, and nothing weaker?

`Ziel` (`Spec.lean:296-314`) has 13 conjuncts. Per leg:

**Memory safety — `speicherSicher : SpurInv M`.** `SpurInv`
(`RennfreiVoll.lean`, `Spec.lean:64-66` review entry): every thread trace is
`Konsistent` and every access event is `e.gut` = carries its carrier's guards
(locks AND marks) in `Λ`, whose locks are really held (`Ereignis.gut`,
`Satz.lean:263`). Typing and in-range are intrinsic (`World` slots total over
`Int`; `.index` values in-range by type) and G's rules fire only on success
outcomes. What it means: every RECORDED access held its guard. Unrecorded
memory change is not this conjunct's subject — but the race leg's `ZugriffG`
(recorded event OR memory change, `RennfreiVoll.lean:333`) closes that
direction for races. Verdict: means what the words mean, modulo the
trace-recorded framing, which is visible in the predicate.

**Data-race freedom — `rennfrei : RennfreiBis P O passes M0 M`.**
(`Spec.lean:229-236`): on every run `M0 → M`, two accesses by different threads
to ONE carrier, one a write, force `∃ L, Bewacht c L ∧ GeordnetG …` (release by
the first, acquire by the second). Unconditionally unguarded carriers are
included: no such order exists without a guard, so the pair must not exist.
Two EXCEPTIONS are premises, hence visible to any reader: `¬ AtomarAusgenommen
c` (atomic globals) and `¬ PaarungAusgenommen c` (publish payloads) — ordered
by A10, not by locks, per the Spec header. Verdict: DRF-with-named-exceptions;
the exceptions are in the statement, not the fine print.

**Contracts where claimed — six conjuncts.** `vertrag : VertragAmOrtG P M`
(requires at every logged entry, ensures at every logged return, actual
parameters/results, entry world as `old` — `ZielOrt.lean:67`, no `∀ rho`/`∀ v`
quantification-away); `sperrInv : SperrInvG S M` (free locks' invariants in
memory); `invRueck : InvAmOrtG P M` and `invGrund : InvAmGrundG P M` (owed
invariants at value AND reason exits — the reason half is new in Spec);
`startEnde : StartEndeG P M` (start functions' value completion with ensures +
owed invariants); `keinStartGrund : KeinStartGrundG M` (no start frame at a
reason return); `keinLogikHalt : KeinLogikHaltG O passes M` (loop invariants
and transition pre-states hold where G tests). Named boundaries, all visible:
invariants at returns only (never while held, never at entries); reason exits
carry owed invariants but NO ensures (callee `grund` by design outside the
slogan); start functions cannot end in reasons at all — `KeinStartGrundG` is
proved from `StartOhneGrund` (`gruende = 0`), which `ziel_aus` derives from the
checker's `wurzeln` via `wurzel_of` (`Beweis.lean:81`). The 2026-09-14
start-reason edge is therefore closed here by a CHECKED premise that refuses
reason-bearing starts, not by certifying them. Verdict: "contracts where
claimed", with the claim boundary drawn in the statement.

**Progress — `keineVerklemmung` + `fortschritt`.** Deadlock freedom is the
conditional "all unfinished wait → all finished" (needs `StufenM` + lock-free
starts, `keine_verklemmungG`); `FortschrittG` (`Spec.lean:284-286`) is "every
thread finished, waiting, at a NAMED hardware stop, or stepping", where
`HaltBenannt` (`:277-280`) enumerates spent `forever` budget and the failing
side conditions of every hardware rule (`KopfHardware` `:248-265`: mistyped
axiom answers, register answers against promise/outside type, invisible
`awaits`, float out of range). Verdict: "no UNNAMED stuck state" — not
liveness, termination, fairness, or a waiting bound (all named NOT CLAIMED in
the Spec header). Matches "progress" only in this weak, stated sense.

**Time — `zeit : ZeitAb P O passes M`.** (`Spec.lean:289-293`): a frame entered
at `M` whose calls nest at most `n` deep takes at most `kostenTief P passes (n
+ 1) g` OWN steps on every run while active. Conditional per frame on
`rufTief` admission — recursive/indirect programs get no bound, with no
program-wide premise owed (`Beweis.lean:101-102`); scheduler delay is excluded
by construction (`segZaehle` counts own steps, `KostenG.lean`). Declared
`costs` are not in `Deklaration`; `zeit` is the syntax-computed bound.
Verdict: the weakest leg — own-step bounds, not timing/WCET (named NOT
CLAIMED). It says what it says; "and time" in the owner's sentence
over-reads it.

**Nothing weaker, nothing extra:** no termination smuggled in, no C/hardware
claim inside `Ziel` (that is `schlusssatz_104`'s job, §4). **Q1: YES**, modulo
the named exceptions above, each visible in its predicate.

## 2. Premise groups, and what the Rust checker computes today

`GabbroZiel` binds `C D P S Q fs ls cs ws`, then premises in four groups:

- (a) checker Bool: `C.akzeptiert P S fs.1 ls.1 cs.1 ws = true`, with `korrekt`
  the one link from the Bool to `AkzeptiertSpec` (`Spec.lean:160-168`).
  `fs`/`ls`/`cs` are `Aufzaehlung`s — complete by type (per-declaration `cases`
  proofs), not premises. `ws` is program data (declared starts).
- (b) user logic: `NutzerPflicht P S Q` — per function at EVERY budget
  (`KoerperGutS` triple + caller duty + no-`logik` over `execEndH` against every
  `RahmenO`/`RegLokal`/`AxVertragO` oracle, every `HavocOk` move, every
  frame-respecting handler; `InvGutS`; `InvGutGrund`) plus `SperrInvLokal`,
  `AxEnsLokal`. All own logic.
- (c) named hardware: `HardwareAnnahmen O Q` = `GutO ∧ RegLokal ∧ AxVertragO`.
- (d) quantified run data: `passes`, `sp`, `init`, `M` + reachability, cut down
  by `StartZulaessig` (declared-or-idle starts, `requires` and lock invariants
  at the start memory).

Every PREMISE is in exactly one group. Two BINDERS are declaration data with
no producing tool, and that is a finding about use, not grouping: `S` (the
lock-invariant family — no surface syntax produces it, no checker rule
computes `fussSperreB`/`SperrInvOk`) and `Q` (the declared axiom ensures).
Both are universally quantified, so the theorem constrains every instance;
but certifying a program means hand-building `S`/`Q` in Lean.

**Rust checker today: it does NOT compute `Akzeptiert`.** `grep Akzeptiert`
over `crates/gabbro-check/src/` is empty; `lean_g.rs:2818` emits
`example : programmImFragmentG gP gFs = true := by decide` with the comment
"the flagship's `FussS`/`fussSperreB` … has no Rust rule"
(`lean_g.rs:2825`, same in `obligations_g.rs:119-120`). Neighbours exist but
none IS the composed predicate: `H013` (+`H222` beside it, `geteilt.rs`) for
unguarded shared writes, `N240` (`startexklusiv.rs`) for start shape,
`N275-N277` (`sperrinv.rs`) for thirds of `SperrInvOk`, `E245-E249`
(`wirkungen.rs`, now hints beside `fusswache2.rs`). Concrete sub-gap found by
grep: `startexklusiv.rs` never mentions `gruende` — the no-reasons half of
`wurzeln` (the very premise that closes the start-reason edge, §1) has not
even a neighbour rule. Of the ~7 decidable components of `Akzeptiert`
(`Akzeptiert.lean:309-311`), ZERO are produced by the checker as the theorem
consumes them. The Lean-side bridge (`Akzeptiert_ok`, `akzeptiert_iff`,
`rennfreiBis_of`) is proved; the Rust side is unwired.

## 3. Adversarial emptying (probed with `./lean-probe`, `.tmp/sonde189.lean`, 0 errors)

- **A `Pruefer` whose Bool is always false** (`prueferFalsch`, green): sound
  (`korrekt` vacuous) and useless. The `∀ C` quantifier therefore carries no
  force by itself; the force is `akzeptiert_pruefer` + acceptance by `decide`
  (`mP_akzeptiert`, `zPB_akzeptiert`, `zPC_akzeptiert`) + refutations
  (`ungeschuetzt_abgelehnt_gilt`, `zwei_schreiber_abgelehnt_gilt` in tree).
  Not a hole — but "the checker carries it" rests on those witnesses, and
  today the concrete checker is Lean-side `decide`, not Rust (§2).
- **Unsatisfiable lock-invariant family** (`sperrInvFalsch`, green):
  `startZulaessig_falsch_unsat` — no start is admissible; `havocOk_falsch_leer`
  — no move is in the class, so every `KoerperGutS` clause holds vacuously.
  JOINT vacuity for that `S` (the `SpecProben.lean:17-20` header names exactly
  this shape). Not a refutation (`S` universal); guarded by the witnesses,
  which pair acceptance with SATISFIABLE families (`mSI`, `zS`) and moving
  runs (`gabbro_ziel_zeuge`, `Proben.lean:190-209`). Use-side obligation worth
  naming: whoever instantiates `S` owes `∃ s, ∀ L, S.inv L s = true` (the form
  `NutzerWiderlegt` already demands).
- **Trivial `Q`** (`axVertragO_mono`, green): meeting is monotone in the
  permissiveness of `Q`, so the witnesses' `Q = axWahr` (met by EVERY oracle,
  `axVertragO_wahr`) is the STRONGEST user duty; `Q = false` shrinks the
  oracle class toward empty — joint vacuity with `HardwareAnnahmen`, same
  shape as `S`. Universal `Q` saves the theorem; `axWahr` instances carry it.
- **`P.mitRuhe` hiding behaviour**: transfers proved (`akzeptiertSpec_mitRuhe`,
  `nutzerPflicht_mitRuhe`, `hardware_mitRuhe`, `Ruhe.lean`; `MitRuheSemantik`:
  `P.mitRuhe` at `some f` IS `P` at `f`). The root writes NOTHING
  (`ruhig_mitRuhe`; `Ruhig` strengthened to no writes, `Akzeptiert.lean:51-53`),
  and the root on every thread is admissible for every satisfiable `S`
  (`startZulaessig_ruhe`) — the statement is never empty for lack of starts.
  `wsRuhe = map some` (`MitRuhe.lean:646`; the root is not a declared start)
  and `Erfuellbar`'s every-declared-start-runs clause (`SpecProben.lean:47-53`)
  keep witnesses from going root-only. No hole.
- **Trivial `NutzerPflicht` / empty oracle class / `StartZulaessig` admitting
  nothing**: `NutzerPflicht` quantifies every budget (probe-D refutations
  `probeD_widerlegt_gilt`, `probeD_wahr_widerlegt_gilt` in tree) and every
  function; emptying needs unsat `S` (above) or `Q = false` (above) — both
  jointly vacuous, both universally quantified. No hole.
- **Waves-1-2 defect** (`∀` over all contracts/statements/expressions):
  absent at the flagship — checked by reading `Spec.lean`: universals range
  over handlers/oracles/moves (inhabited by record handlers in the replay and
  `rufAusV` witnesses), functions, budgets, threads, runs; all instantiated
  jointly in `gabbro_ziel_zeuge` (moving run, changed memory) and `Erfuellbar`.
  The `e0` carrier exclusion is GONE (justified records, `Beweis.lean:34-49`).

**Q3: no emptying found.** Two joint-vacuities (`S`, `Q`) behave as designed
under universal quantification; each has its satisfiable/maximal witness.

## 4. Machine G and the emitted C

G (`RufMaschineG`, 70 rules, one thread per step, `HeldIn` side conditions
after the §15.1 inclusion relaxation, no bare lock steps; `rufG_haelt_statisch`,
`exklusivG`) runs SC interleavings of the language's statements: leaves fire
through `execStmt` outcomes, `locks`/`awaits`/axiom/register/float rules carry
their hardware side conditions, entries/returns are logged with actual values.
The user proves against `execEndH` (lock-aware sequential semantics with
`HavocOk` acquire-moves and release checks); adequacy links G to the
contract-ignoring `rufRumpf` via handler records, with the known limits
(`Tief` admission, `KandOk`-restricted indirect calls, no per-slot frames).
Gaps are booked, not hidden (SATZKARTE §§11-15; Spec header NOT CLAIMED:
termination, fairness/waiting bound, weak memory beyond DRF-SC, floats past
the kernel IEEE model on the C side, starvation freedom, entry/held-lock
invariants). G runs what the language means on the covered fragment; the
fragment boundary (`KandOk`, `RegLokal`, signature-or-invariant guards,
`rufTief`-admitted calls) is where it stops meaning it.

The G-to-C link is `schlusssatz_104` (`Schlusssatz104.lean:1460`): ONE
program, single-threaded, stage (a) — parse fidelity, model certificates,
model judgement at every budget, every C run related, the machine conclusion
— under A1 (C compiler follows `CSemantik`), A2 (emitted text IS `refCProg`,
hand transcription), A3 (layout pins), A4 (runtime starts thread 0, idles the
rest), A5 (kernel + review defs). Chain count by the strict counter
(`messung/KETTE-2026-09-13.md`): **0 of 101** — it counts a chain as closed
only where a `Schlusssatz*.lean` names the program AND the parsed, certified
and C-corresponding programs are proved one, which even 104 still owes.
Substance: one single-threaded program closed modulo A1/A2/A4 + the `gP`
identity gap; sieves (b)-(e) pass for 104/108/118 only. Concurrent stage (b)
is a planned statement, proof not started; the emitter has no thread notion,
lock primitives are extern prototypes in no theorem, G is SC while C is weak
memory (DRF-SC a named premise). **Q4: G is linked to its meaning; G is linked
to C for one program on one thread.**

## 5. What changed since the 2026-09-14 Muse verdict

Closed as theorems since: the `e0` carrier exclusion (justified records;
`GabbroZiel` has no `e0`), the start-reason edge (no-reasons premise +
`KeinStartGrundG`), reason-exit invariants (`InvGutGrund`/`InvAmGrundG` in
premise and conclusion), the `renn` write-write component (`rennB`,
`SchreibGetrennt`, probe `ak3_zwei_schreiber_ohne_lesen`), `Ruhig`-writes-nothing,
`Erfuellbar`'s declared-starts-run clause. The statement is strictly stronger
and the probe set strictly wider than what the last verdict reviewed.

## 6. Named gaps (the verdict list)

MODEL (in the statement's vocabulary, none load-bearing for ordinary
value-returning programs):
1. Invariants at returns only — never while held, never at entries.
2. Reason exits carry owed invariants, never `ensures`.
3. `ZeitAb` is own-step bounds under per-frame `rufTief` admission — no
   recursion/induction coverage, no wall-clock (weakest leg).
4. Progress is no-unnamed-stuck-state — no fairness, waiting bound (separate
   `Lebendigkeit.lean`, not in `Ziel`), termination.
5. Atomic globals and publish payloads excluded from DRF (A10 regime).
6. Adequacy limits: `Tief` admission, `KandOk` indirect calls, no per-slot
   frames, `ret`-under-`locks` untypable.

USE (instantiating the statement for a program):
7. `S` satisfiability (`∃ s, ∀ L, S.inv L s = true`) is owed but not a
   premise — joint vacuity otherwise (§3).
8. `S` and `Q` have no surface syntax and no producing tool.

IMPLEMENTATION (the actual distance):
9. No Rust rule computes any composed component of `Akzeptiert` (§2); the
   no-reasons half of `wurzeln` has no neighbour at all.
10. No tooling states `NutzerPflicht`/`InvGutS` for real code (`gabbro prove`
    aims at `Body.lean`, a different model).
11. C linkage: one program, one thread, modulo A1/A2/A4 + the `gP` identity
    gap; strict chain count 0/101; concurrent stage (b) unstarted.

---
CUTS (this verdict file): proves nothing; it classifies, counts and cites.
`#print axioms` record (probed, `.tmp/sonde189.lean`, 0 errors):
`prueferFalsch`, `startZulaessig_falsch_unsat` depend on
`[propext, Classical.choice, Quot.sound]`; `havocOk_falsch_leer` on `[propext]`;
`axVertragO_mono` on `[propext, Quot.sound]`. `gabbro_ziel` itself: green
`./lean-bau` (224 jobs); axioms per `Beweis.lean` prints (standard three, no
`sorryAx`, no new `axiom`).
