# VERDICT: IS THE REPAIRED GabbroZiel THE GOAL? (lane 190, fourth independent review, 2026-09-15b)

Owner's goal: "a Gabbro user proves only their OWN logic plus named hardware
assumptions; memory safety, data-race freedom, contracts where claimed in
concurrent runs, and time are carried by the language."

**Verdict: `GabbroZiel` is the goal with named gaps (list in §6).**

`theorem gabbro_ziel : GabbroZiel` (`grammatik/Grammatik/Zielsatz/Beweis.lean:154`,
statement `Zielsatz/Spec.lean:474-485`) says the four legs and nothing weaker
(§1); each leg adds a named, checkable fact over `NutzerPflicht` (§2); every
premise sits in exactly one group and every (c)/(d) entry is genuinely
hardware/runtime (§3); all three Opus findings P1-P3 verify as closed with
`./lean-probe` on a scratch file, and no new emptying attempt succeeds (§4).
The remaining distance is implementation and named model boundaries, not
statement defects (§§5-6).

Base: branch `muse/190` (master at `ad43ef5f`). No existing file changed; no
Lean file added outside scratch. Probes: `.tmp/sonde190.lean` (git-ignored
scratch): `./lean-probe` **0 errors**. `./lean-bau`: **Build completed
successfully (225 jobs)**. I did NOT read
`messung/URTEIL-OPUS-2026-09-15b*`. I read the third-round verdicts
(`URTEIL-MUSE-2026-09-15.md`, `URTEIL-OPUS-2026-09-15.md`), `SATZKARTE.md`
§22, and the `Spec.lean` header (the Einheit, NutzerPflicht with
StartPflicht, Laufzeit A4, the one assumption list).

## 1. Each leg vs its words (`Ziel`, `Spec.lean:453-471`)

`Ziel` has 12 conjuncts in four legs (memory safety is one conjunct;
contracts are six; progress two; time one).

**Memory safety — `speicherSicher : SpurInv M`.** `SpurInv`
(`RennfreiVoll.lean:249`): every recorded access carries its carrier's
guards (locks AND marks) in `Λ`, whose locks are really held
(`Ereignis.gut`, `Satz.lean:263`; traces `Konsistent`). Typing and
in-range are intrinsic (`World` slots total over `Int`; `.index` values
in-range by type) and G's rules fire only on success outcomes. Reading:
every RECORDED access held its guard. Unrecorded memory change is not
this conjunct's subject — the race leg's `ZugriffG` (recorded event OR
memory change, `RennfreiVoll.lean:333`) closes that direction for races.
Means what the words mean, modulo the trace-recorded framing, which is
visible in the predicate. Stack depth is outside it (unbounded stacks;
named NOT CLAIMED in the Spec header).

**Data-race freedom — `rennfrei : RennfreiBis P O passes M0 M`.**
(`Spec.lean:386-393`): on every run `M0 → M`, two accesses by different
threads to ONE carrier, one a write, force
`∃ L, Bewacht c L ∧ GeordnetG …` (release by one, acquire by the other).
Unguarded carriers are included (no such order exists without a guard,
so the pair must not exist). Exactly ONE exception, in the statement:
`¬ AtomarAusgenommen c` (atomic globals, A10 regime). The old publish-
payload exemption is GONE (P3 repair, §4). DRF with one named exception.

**Contracts where claimed — six conjuncts.** `vertrag : VertragAmOrtG`
(`ZielOrt.lean:67`): requires at every logged entry, ensures at every
logged value return, actual parameters/results, entry world as `old` —
no `∀ rho`/`∀ v` quantification-away. `sperrInv : SperrInvG S M`: every
lock no thread holds has its invariant IN SHARED MEMORY — a global
cross-thread fact. `invRueck : InvAmOrtG` and `invGrund : InvAmGrundG`
(owed invariants at value AND reason exits). `startEnde : StartEndeG`
(start functions' value completion with ensures + owed invariants).
`keinStartGrund : KeinStartGrundG` (no start frame at a reason return —
closed by the checker's no-reasons premise, `wurzeln` + `wurzel_of`).
`keinLogikHalt : KeinLogikHaltG` (loop invariants and transition
pre-states hold where G tests). Named boundaries, all visible:
invariants at returns only (never while held, never at entries); reason
exits carry owed invariants but NO ensures (callee `grund` outside the
slogan by design). "Contracts where claimed", claim boundary in the
statement.

**Progress — `keineVerklemmung` + `fortschritt`.** Deadlock freedom is
the conditional "all unfinished wait → all finished" (needs `StufenM` +
lock-free starts, `keine_verklemmungG`). `FortschrittG`
(`Spec.lean:441-442`) is "every thread finished, waiting, at a NAMED
hardware stop, or stepping", where `HaltBenannt` (`:434-437`) enumerates
spent `forever` budget and the failing side conditions of every hardware
rule (`KopfHardware` `:406-422`: mistyped axiom answers, register
answers against promise/outside type, invisible `awaits`, float out of
range). "No UNNAMED stuck state" — not liveness, termination, fairness,
or a waiting bound (all named NOT CLAIMED). This also keeps the safety
legs from being vacuous by G getting stuck.

**Time — `zeit : ZeitAb P O passes M`.** (`Spec.lean:447-450`): a frame
entered at `M` whose calls nest at most `n` deep takes at most
`kostenTief P passes (n+1) g` OWN steps on every run while active.
Conditional per frame on `rufTief` admission — recursive/indirect
programs get no bound, with no program-wide premise owed
(`Beweis.lean:105-106`); scheduler delay excluded by construction
(`segZaehle` counts own steps). Declared `costs` are not in
`Deklaration`. The weakest leg — own-step bounds, not timing/WCET
(named NOT CLAIMED). It says what it says; "and time" in the owner's
sentence over-reads it.

**Q1: YES**, modulo the named exceptions above, each visible in its
predicate.

## 2. What `Ziel` gives beyond `NutzerPflicht`, leg by leg

The user proves SEQUENTIAL per-function facts: each body, run alone by
`execEndH` against every callee answer meeting the callee's contract and
frame, every register/axiom answer in the (c) class, and every lock move
keeping the invariant, ends in its `ensures` and owed invariants, meets
each callee's `requires`, and never ends in `logik` (`KoerperGutS`,
`InvGutS`, `InvGutGrund`, at EVERY budget); plus `SperrInvLokal`,
`AxEnsLokal`, and the start obligation (`StartPflicht`: every lock
invariant at `E.sp0`, every declared start's `requires` there with its
declared arguments). `Ziel` speaks about the INTERLEAVED machine G:

- `speicherSicher` — NOT in (b) at all: from the checker and G
  (`spurInv_erreichbar`, needs only `GutO`).
- `rennfrei` — NOT in (b): from the checker and G (`rennfreiBis_of`).
- `vertrag`, `invRueck`, `invGrund`, `keinLogikHalt`, `startEnde`,
  `keinStartGrund` — these ARE (b)'s sequential clauses, restated at the
  places of G's log. What the theorem adds is that they survive
  interleaving and are G's behaviour, not only `execEndH`'s: other
  threads interfere only through `HavocOk` lock moves and through
  carriers the checker proved thread-local. For a single-threaded
  lock-free program these legs are (nearly) a restatement of (b),
  transported to G by the replay.
- `sperrInv` (`SperrInvG`) — NEW: (b) checks the invariant at each
  release of one body; the global fact (every free lock's invariant in
  shared memory at every reached machine) is the theorem's.
- `keineVerklemmung`, `fortschritt` — NOT in (b): no deadlock from lock
  ranks, and G never stops silently.
- `zeit` (`ZeitAb`) — NOT in (b), and WEAK: holds for EVERY program of
  G with no premise (`frame_schritte_beschraenkt`), so it says nothing
  about waiting, recursion, indirect calls or `forever` loops; not the
  declared `costs`.

**Q2 (first half):** the added value is real on every leg except the
degenerate single-threaded case, where the contract legs are honestly a
transport — which is itself the point (sequential reasoning reaching
the interleaved machine).

## 3. Premise groups; are the assumptions hardware/runtime?

`GabbroZiel` binds `C D E fs ls cs`, then:

- (a) checker Bool: `C.akzeptiert E fs.1 ls.1 cs.1 = true`, with
  `korrekt` the one link from the Bool to `AkzeptiertSpec`
  (`Spec.lean:281-286`). `fs`/`ls`/`cs` are `Aufzaehlung`s — complete
  by type (per-declaration `cases`), not obligations.
- (b) user logic: `NutzerPflicht E` = `LogikPflicht E.P E.S E.Q` +
  `StartPflicht E`. All own logic, over the program's own fields.
- (c) named hardware: `HardwareAnnahmen O E.Q` =
  `GutO O ∧ RegLokal O ∧ AxVertragO E.Q O`.
- (d) runtime A4: `Laufzeit E sp init` = `lader` + `start` + `einmal`.
- Run data: `passes`, `sp`, `init`, `M` + reachability. Nothing else
  restricts the quantified runs (`StartZulaessig` is derived, not a
  premise: `startZulaessig_aus`, `Beweis.lean:120-144`).

Every premise is in exactly one group. (`S`, `Q`, `starts`, `sp0` are
fields of `E`, not premises at all — P2 repair.)

Audit of each (c)/(d) entry — really hardware/runtime?

- `GutO O`: an axiom (a FOREIGN body: `extern`/`prim`/`asm`/`entry`/
  `entrust`) writes only its declared frame, keeps held locks, leaves
  accesses in the trace. Foreign code is not Gabbro code: nothing in
  the language can check it; the user's logic never sees its body.
  Genuinely hardware/foreign. YES.
- `RegLokal O`: a register read answers from its device's carriers
  (`D.rtraeger`); `awaits g` visibility from `g` only
  (`ZielOrtGeraetSem.lean:48-52`). About the device, not the program —
  BUT NAMED stronger than hardware: `register_ohne_traeger_konstant`
  (`Proben.lean:135`) proves a register WITHOUT declared carriers
  answers the same value in EVERY world, and a user proof may use that
  two reads agree — a real volatile register breaks that. A
  device-driven value must come through an axiom (free under `GutO`)
  or through carriers an axiom writes. Named in the ONE list, not
  repaired (the replay `regLies_gleich` needs the answer to be a
  function of shared carriers). Hardware with a named over-strength.
  YES, with the asterisk the header itself puts on it.
- `AxVertragO E.Q O`: every axiom answer meets the `ensures` the
  program declares for it. The contract of foreign code/a device, which
  the user writes and nothing checks: `Q := false` is a false NAMED
  assumption (visible in the declaration), and makes (c)
  unsatisfiable — the honest kind of vacuity. YES.
- `Laufzeit.lader` (`sp = speicherR E.sp0`): the loader establishes the
  declared initial memory (initialized data/zeroed storage of the
  emitted C). Toolchain/loader fact; that `sp0` meets invariants and
  start requires is the USER's `StartPflicht`. YES.
- `Laufzeit.start`/`.einmal`: the runtime starts exactly the declared
  starts, each on its own thread with declared arguments, the idle root
  (`MitRuhe.lean`: `return`, empty signature, writes nothing) on every
  other thread; covers every assignment running some declared starts.
  Thread creation is the emitted `main`/boot code's, not user logic.
  YES.
- Reading assumptions (not premises, named in the header): machine G is
  the meaning of the C (translation validation,
  PLAN-UEBERSETZUNGSVALIDIERUNG); the hardware is DRF-SC. Named, not
  smuggled. YES.

**Q2 (second half): YES.** One asterisk (`RegLokal` constancy), declared
in the statement's own assumption list.

## 4. Adversarial emptying (probed, `.tmp/sonde190.lean`, 0 errors)

- **P1 re-tried: `invariant false` on any lock.** `probeA_falsch_inv_nicht`
  refutes (b) for every `Q`, `starts`, `sp0` (by `StartPflicht.sperren`);
  `p1_akzeptiert` (`by decide`) shows the checker's Bool ACCEPTS that
  program, so the refusal is (b)'s, not (a)'s. Whole class at once:
  `unerfuellbar_widerlegt` — no program with an unsatisfiable family
  meets (b). Mechanism: `havocOk_bewohnt` — under (b) the `HavocOk`
  move class every body obligation quantifies over is inhabited (via
  `havocOk_misch_lokal`, needing only the locality half). And a start
  whose `requires` fails at `sp0` refutes (b): `start_req_widerlegt`
  (before, it only made that start inadmissible while emptying its
  body's obligation). P1 CLOSED.
- **P2 re-tried: the starts knob, `S`/`Q` free, empty run class.**
  `starts`, `S`, `Q`, `sp0` are fields of `E` (`Einheit`, Spec.lean:
  229-234); the checker runs on `E.ws`, the hardware assumption names
  `E.Q`. `laufzeit_nur_erklaert`: a user function runs on a thread only
  if declared. `E.starts = []` is a DIFFERENT program about the root
  alone (`laufzeit_ohne_starts`, `akP3_ohne_starts`). `akD_kein_zweiter_schreiber`:
  no accepted program over `akD` runs both writers. Distinctness is
  checked (`einzeln`/`einzelnB`; `laufzeit_voll`, `laufzeit_initRuhe`).
  The run class is never empty: `laufzeit_ruhe` (root everywhere from
  `sp0` meets (d)) — but `Erfuellbar`'s declared-starts-run clause keeps
  witnesses from going root-only. P2 CLOSED.
- **P3 re-tried: payload write-write.** `zwei_schreiber_abgelehnt_gilt`
  refuses two declared starts writing one unguarded non-atomic carrier
  with no read and no payload exemption; `rennfreiBis_of` proves the leg
  for every non-atomic carrier (`rennfrei_g_voll` guarded,
  `rennfrei_ungeschuetzt` unguarded). `Spec.lean:386-393` (`RennfreiBis`)
  and `AkzeptiertSpec.renn` contain no `PaarungAusgenommen` (verified by
  grep). Remainder: the legacy predicate `DatenRasse`
  (`RennfreiVoll.lean:655-659`, lock-guarded carriers only) still
  carries the exemption — it is NOT the goal's race leg. Named price
  (Spec header P3): the publish/await hand-off of an UNGUARDED payload
  is refused, not covered. P3 CLOSED at the goal.
- **Tried, no defect:** a `Pruefer` whose Bool is always false (sound
  and useless; `∀ C` quantification — force is `akzeptiert_pruefer` +
  `decide` acceptances + refutations); `Q := false` (honest named
  vacuity, hardware stops); `P.mitRuhe` hiding behaviour (transfers
  proved in `Ruhe.lean`/`MitRuheSemantik.lean`; root writes NOTHING,
  `ruhig_mitRuhe`); probe-D shapes at every budget
  (`probeD_widerlegt_gilt`, `probeD_wahr_widerlegt_gilt`);
  table-invariant breaker (`tabelle_widerlegt_gilt`).
- **Waves-1-2 defect** (`∀` over all contracts/statements/expressions
  that no ordinary program satisfies): absent at the flagship — read
  off `Spec.lean`: universals range over handlers/oracles/moves
  (inhabited: record handlers in the replay, `rufAusV` witnesses,
  `havocOk_bewohnt`), functions, budgets, threads, runs; all
  instantiated jointly in `gabbro_ziel_zeuge` (two active threads, one
  step changes memory: `zweiFaeden_bewegt_gilt`) and `Erfuellbar`.

**Q3: no emptying found.** The one aging risk is the `∀ C` quantifier
(the Bool is decoration without `akzeptiert_pruefer`), which is why the
concrete checker's `decide` witnesses matter — they exist
(`p1_akzeptiert`, `mP_akzeptiert`, `zPB_akzeptiert`,
`zweiFaeden_erfuellbar_gilt`).

## 5. Re-check of the previous gap list (§6 of URTEIL-MUSE-2026-09-15.md) against master TODAY

The task states several implementation items there are stale
(lock-invariant syntax since lane 156, footprint rule N290-N294 since
lane 175, `gabbro obligations --g` since lane 176). Re-measured by grep
against this tree; each item marked CLOSED / PARTLY / OPEN:

MODEL (none load-bearing for ordinary value-returning programs):

1. Invariants at returns only — OPEN, by design (Spec header NOT
   CLAIMED; no new theorem claims entry/held-lock invariants).
2. Reason exits carry owed invariants, never `ensures` — OPEN, by
   design.
3. `ZeitAb` own-step bounds under per-frame `rufTief` — OPEN, by
   design (weakest leg; liveness entries of SATZKARTE §21
   `LaufzeitAnnahme`/`HardwareImAbschnitt` still not in `Ziel` or the
   ONE list, §21.6).
4. Progress is no-unnamed-stuck-state — OPEN, by design (waiting bound
   lives in `Lebendigkeit.lean`, not in `Ziel`).
5. Atomic globals excluded from DRF — OPEN, by design (A10 regime).
   The payload half is CLOSED (P3, §4).
6. Adequacy limits (`Tief`, `KandOk`, no per-slot frames,
   `ret`-under-`locks` untypable) — OPEN (no new adequacy theorem in
   tree).

USE:

7. `S` satisfiability owed but not a premise — CLOSED. It IS a premise
   now: `StartPflicht.sperren` (`Spec.lean:322-324`), proved by
   `unerfuellbar_widerlegt` + `havocOk_bewohnt` + `probeA_falsch_inv_nicht`.
8. `S` and `Q` have no surface syntax and no producing tool — PARTLY
   STALE, now half-closed. Lock-invariant syntax EXISTS:
   `lock L protects { … } invariant …` with checker rules N275-N277
   (`sperrinv.rs`, "the invariant reads a carrier the lock does not
   protect" etc.), exported as `gS.inv` (`lean_g.rs:2855-2858`), and
   `fusswache2.rs` reuses lane-156 lock data (`sperrdaten`). What
   stays true: no tool produces the Lean FAMILY `S` as the theorem
   consumes it (link is hand `decide` witnesses), and `Q`/axiom
   ensures still have no export path (axioms are not exportable;
   `Akzeptiert.lean:74-76` books `AxEnsLokal` as user-side).

IMPLEMENTATION:

9. "No Rust rule computes any composed component of `Akzeptiert`;
   no-reasons half of `wurzeln` has no neighbour" — STALE in its
   absolute form, TRUE in its composed form. What exists today:
   N290-N294 (`fusswache2.rs`, wired in `lib.rs` as "lane 175, the
   flagship's footprint premise") implement `FussS` + floors with
   five refusing error rules; N240 (`startexklusiv.rs`) implements the
   signature-lock half of `wurzeln`; `sperrOrte` holds by construction
   (`protects` = `orte`) plus printed `decide` examples; H013/H222
   implement `renn` (stricter per entry, no payload exemption).
   What stays true: no SINGLE Rust Bool composes them as
   `Akzeptiert`/`akzeptiert_pruefer` consumes them; the no-reasons
   half of `wurzeln` STILL has no rule — `startexklusiv.rs` never
   mentions `gruende` (verified by grep); `fuss` judges per start
   index, Lean per function (`reachB` graphs); `einzeln` and the
   payload-inclusive `renn` as one Bool unchecked
   (SATZKARTE §22.6: whether `concurrent { f, f }` is refused "was not
   checked" — still the case in tree).
10. "No tooling states `NutzerPflicht`/`InvGutS`; `gabbro prove` aims
    at `Body.lean`" — STALE in its absolute form, PARTLY true.
    `gabbro obligations --g` EXISTS (`main.rs:859`) and,
    per the `obligations_g.rs` header, states per-function
    `KoerperGutS` + `InvGutS` duties at every budget plus the start
    duty, through the IMPORTED definitions (no body copies). What
    stays true: it states the `ziel_ort_sperre_ende` vocabulary (older
    flagship naming), not today's `NutzerPflicht E` over
    `Einheit`/`mitRuhe` (no `InvGutGrund`, no `StartPflicht` shape,
    no `E.sp0`/`E.starts` fields); and the `Body.lean` remark about
    `gabbro prove` is untouched by this tree.
11. C linkage: one program, one thread, `gP` identity gap, chain
    0/101, concurrent stage (b) unstarted — OPEN (no new
    `Schlusssatz*.lean` in tree; exporter still fills neither
    `starts` nor `sp0` nor source `requires` — Spec header NOT
    CLAIMED names it).

## 6. Named gaps (the verdict list; * = design boundary, † = implementation distance)

MODEL*: 1. invariants at returns only; 2. reason exits never carry
`ensures`; 3. `zeit` is syntax-computed own-step bounds (weakest leg);
4. progress is no-unnamed-stuck-state (no fairness/waiting bound in
`Ziel`); 5. atomic globals excluded from DRF (A10); 6. adequacy limits
(`Tief`, `KandOk`, per-slot frames, `ret`-under-`locks`); 7. `RegLokal`
register constancy without `depends` (named over-strength, device
values via axioms); 8. one thread per busy start (no SMP-symmetric
code); 9. stack depth unclaimed.
USE†: 10. `S`/`Q` as Lean families hand-built per program (surface
syntax for lock invariants exists; no producing tool for the families
as consumed).
IMPLEMENTATION†: 11. no single Rust `Akzeptiert` Bool (components
N290-N294, N240-half, H013 exist; no-reasons half missing; semantics
differ per-index vs per-function); 12. `obligations --g` states the
older obligation vocabulary, not `NutzerPflicht E`; 13. C linkage one
program/one thread, exporter gaps (`starts`, `sp0`, source
`requires`), concurrent stage unstarted.

---
CUTS (this verdict file): proves nothing; it classifies, counts and
cites. Axioms (probed, `.tmp/sonde190.lean`, 0 errors): `gabbro_ziel`
per `Beweis.lean` prints `[propext, Classical.choice, Quot.sound]`
(verified via the probe's `#print axioms` output tail); probe
theorems `probeA_falsch_inv_nicht`, `havocOk_bewohnt`,
`start_req_widerlegt`, `laufzeit_*`, `zwei_schreiber_abgelehnt_gilt`
standard three or fewer; no `sorryAx`, no new `axiom`. `./lean-bau`:
Build completed successfully (225 jobs).
