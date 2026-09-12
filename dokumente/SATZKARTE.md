# SATZKARTE-A: theorem map for `ziel_nutzer_last_aus_pc_Q`

Draft A (lane 16). Independent draft; no Lean changes.
Target: `Gabbro.Grammatik.ziel_nutzer_last_aus_pc_Q`, `grammatik/Grammatik/Ziel.lean:2324`.
All claims verified by reading the Lean sources cited as `file:line`.
Line numbers refer to the current working tree on branch `muse/16`.

Q-binder instantiation: `Pre := Extraktion.QRequires P`, `Post := Extraktion.QEnsures P`,
where `QRequires` (`grammatik/Grammatik/Extraktion.lean:1437`) is `requires` as a world
predicate (holds for every parameter environment) and `QEnsures`
(`grammatik/Grammatik/Extraktion.lean:1442`) is `ensures` as a world predicate
(for every return value and every parameter environment). The per-thread assertion is
`SpecQ Pre Post Nb J f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`
(`grammatik/Grammatik/InterferenzAllgemein.lean:1069`).

## 1. Conclusion: one sentence per conjunct

The conclusion (`Ziel.lean:2394-2416`) is a 12-way conjunction:

- **C1 (`Gesittet M.lauf`, :2394):** the generated machine run is disciplined
  (consistent, good observations, scheduler exclusion, single-thread marks, unshared separation).
- **C2 (consistency and goodness, :2395-2396):** every per-thread projected trace prefix is
  consistent, and every event observed in it is good.
- **C3 (stable contracts, :2397-2399):** at the last chain world, every member thread's
  contract conjunction (`QRequires ∧ QEnsures` for the function it runs) holds.
- **C4 (probe answers, :2400-2401):** some clock tick lands between the deadline and the use,
  and the deadline run answers the named hardware assumption `fortschritt` of that deadline.
- **C5 (lowering cap, :2402):** the supplied lowering witness expands each Gabbro primitive to
  at most 18 C forms.
- **C6 (outcome classification, :2403-2405):** the single-body outcome `o` is control flow
  (`ok`, `zurueck`, `grund`, `leave`, `next`), user logic (`logik`), or named hardware
  (`hardware`) — nothing else. This leg is unconditional (see below).
- **C7 (one mark, one thread, :2406):** the code projection of the run is single-threaded per
  mark: one mark code is never named by two threads.
- **C8 (unshared means one thread, :2407-2412):** any carrier declared unshared that is
  touched by two run steps belongs to one thread.
- **C9 (world count, :2413):** the recorded world history has exactly one world per step plus
  the start world.
- **C10 (good history, :2414):** every event in every recorded world is good.
- **C11 (live last world, :2415):** the last recorded world is some thread's world over live
  memory.
- **C12 (serial order, :2416):** two conflicting accesses to table `t₀` by distinct threads are
  happens-before ordered in one direction or the other.

Leg-to-lemma wiring (read off the proof term, `Ziel.lean:2417-2428`):
C1 by `pc_gesittet` (`grammatik/Grammatik/Maschine.lean:1743`);
C2 by `pc_konsistent` (`Maschine.lean:1426`) and `pc_gut_obs` (`Maschine.lean:1433`);
C3 by `stabil_aus_lauf` (`Maschine.lean:3879`), whose `hFree` argument is derived inside from
`hForm` via `interferenceFree_of_invariantForm` (`grammatik/Grammatik/InterferenzAllgemein.lean:1213`)
over the discipline-derived context from `invariantenKontext_aus_disziplin`
(`InterferenzAllgemein.lean:1530`), with memory via `speicherVertrag_aus_Q`
(`Extraktion.lean:3924`) and frame via `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`);
C4 by `sampling_closes_frist` (`grammatik/Grammatik/Fristlauf.lean:395`);
C5 by the `begrenzt` field of the supplied `Absenkung` (structure field, not a theorem);
C6 by `zwei_fehler` (`grammatik/Grammatik/Satz.lean:50`, proved by case split, unconditional);
C7 by `pc_discharge_einfaedig` (`Maschine.lean:1619`) over `pcReach_markInv` (`Maschine.lean:1582`);
C8 by `pc_discharge_unshared` (`Maschine.lean:1704`) over `pcReach_carrierInv` (`Maschine.lean:1591`);
C9 by `genWelten_laenge` (`Maschine.lean:1158`) via `pcReach_gen` (`Maschine.lean:1396`);
C10 by `genWelten_gut` (`Maschine.lean:1165`) via `pcReach_gen`;
C11 by `genWelten_letzte` (`Maschine.lean:1172`) via `pcReach_gen`;
C12 by `pc_reduktion` (`Maschine.lean:1765`).

## 2. Premises: one row per premise

Classes: OWN-LOGIC = the user's own logic; NAMED-HW = named hardware assumption;
GABBRO-DUTY = discharged by checker/emitter once Gabbro is verified; OPEN = nothing discharges it.
DATA = object binder, not a proof obligation (no class applies).
"Discharge" means the exact Lean theorem that proves this premise (not merely consumes it);
"none" means no such theorem exists in the tree.

Non-premise object binders (meaning only, no class):
`P` (the program), `O` (the oracle answering `axiomCall`/registers,
`grammatik/Grammatik/Semantik.lean:355`), `passes` (execution bound), `fcode` (thread-to-function
map), `tabs`/`globs` (carrier lists the extraction flattens over), `sp` (start memory),
`M`/`pc` (reached machine and program counters), `code` (mark-to-nat projection),
`Nb` (which thread pairs are co-declared), `J` (the joint chain), `I` (the carrier invariants),
`Wc`/`Gc` (per-carrier footprint witnesses), `tr` (thread trace), `t₀` (the one table the
reduction leg talks about), `g₁`/`g₂`/`j₁`/`j₂`/`w₁`/`w₂`/`Λ₁`/`Λ₂`/`h₁`/`h₂` (the two accesses),
`S`/`c` (sampling period and tick clock, `Fristlauf.lean:279`), `p` (check/use pair,
`Fristlauf.lean:102`), `fr` (deadline: assumption plus probe name, `Fristlauf.lean:110`),
`d` (deadline moment), `o` (the single-body outcome the C6 leg classifies).

| Name | One-sentence meaning | Class | Discharging theorem or "none" |
|---|---|---|---|
| `hO : GutO O` (:2325) | The oracle respects every axiom frame and never changes held locks or the trace (`Satz.lean:794`). | OPEN | none (per-oracle assumption; GutO oracles only, cf. the `Extraktion` §18 remainder on event-emitting oracles) |
| `h : PCReach … (progAus P fcode tabs globs) (GenStart sp) M pc` (:2328) | The machine `M` is really reachable by firing program-counter steps of the computed thread program (`Maschine.lean:1377`; `progAus` at `Extraktion.lean:2572`). | OPEN | none in general (witness-built per run; one-step lifters `pcSchritt_blatt_progAus_ohne_axiomCall` `:929` / `…_axiomCall` `:1129` extend it, they do not create it) |
| `hMSep : PCMarkSep code …` (:2330) | No mark code named by one thread's program text is named by another's (`Maschine.lean:1309`). | GABBRO-DUTY | none (per-program text check; consumed by `pc_discharge_einfaedig`, `Maschine.lean:1619`) |
| `hCSep : PCUnsharedSep …` (:2331) | Any carrier reached from two threads' program texts is declared shared (`Maschine.lean:1318`). | GABBRO-DUTY | none (per-program text check; consumed by `pc_discharge_unshared`, `Maschine.lean:1704`) |
| `hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c)` (:2336) | Every carrier invariant reads only its witnessed footprint (frame agreement implies agreement, `Interferenz.lean:80`). | OWN-LOGIC | none (per-invariant obligation over the user-supplied `I`) |
| `hFrameTD` (:2337) | Each table footprint is a singleton frame: whatever `Wc c` marks must be `c` itself. | OWN-LOGIC | none (per-invariant shape proof) |
| `hFrameGD` (:2338) | Same as `hFrameTD` for the global footprint. | OWN-LOGIC | none (per-invariant shape proof) |
| `hGuardEx : ∀ c, ∃ L, Bewacht c L` (:2339) | Every carrier, table or global, has a guard lock in its watch list (`InterferenzAllgemein.lean:1350`). | OPEN | none — FLAG (see §3) |
| `hEntry : ∀ c σ₀, J.welten[0]? = some σ₀ → I.inv c σ₀` (:2340-2341) | Every carrier invariant holds at the chain head. | OWN-LOGIC | none (caller/sequential side per program) |
| `hReturn` (:2342-2346) | Every writing chain step re-establishes every carrier invariant at its end world while holding the guard. | OWN-LOGIC | none (per-step restoration proof) — FLAG (see §3) |
| `hWatch` (:2347-2351) | Every writing chain step holds the guard lock (declared-holds, `D.haelt` shape). | OPEN | none inside this theorem; table instances discharge via `wache_aus_schuld` (`InterferenzAllgemein.lean:1481`) from `J.hSchuld` plus coverage — FLAG (see §3) |
| `hDeck : GeteiltGedeckt Nb J` (:2352) | Any carrier written by two threads is shared and both writers share a lock of its guard (`InterferenzAllgemein.lean:299`). | OPEN | none (per-chain coverage) — FLAG (see §3) |
| `hReqTAll` (:2353-2354) | Every table read by `requires` lies in the function's write signature. | GABBRO-DUTY | none (per-program footprint check; folded into `hAb` by `haengtAb_vertrag_gesamt`, `Extraktion.lean:1568`) |
| `hReqGAll` (:2355-2356) | Same as `hReqTAll` for globals read by `requires`. | GABBRO-DUTY | none (as above) |
| `hEnsTAll` (:2357-2358) | Same as `hReqTAll` for tables read by `ensures`. | GABBRO-DUTY | none (as above) |
| `hEnsGAll` (:2359-2360) | Same as `hReqTAll` for globals read by `ensures`. | GABBRO-DUTY | none (as above) |
| `hForm : InvariantForm … (SpecQ …)` (:2361-2362) | Per thread, the contract conjunction coincides at every world with some carrier invariant (the CSL fragment, `InterferenzAllgemein.lean:1204`). | OWN-LOGIC | none (exhibit one carrier per thread) — FLAG (see §3) |
| `htr : PCSpur … M pc tr` (:2364) | The reachability derivation fires exactly the thread sequence `tr` (`Maschine.lean:3594`). | GABBRO-DUTY | `pcSpur_von_reach` (`Maschine.lean:3607`, induction on `h`) |
| `hJw : J.welten = M.welten` (:2365) | The joint chain's worlds are exactly the machine's recorded worlds. | OPEN | none for two threads (`kette_aus_lauf_bezeugt_closed`, `Ziel.lean:2235`, closes only witnessed single-thread runs) — FLAG (see §3) |
| `hJsf : J.schrittFaden = tr` (:2366) | The chain's step threads are exactly the machine's fired-thread trace. | OPEN | none for two threads (same single-thread closer as `hJw`) — FLAG (see §3) |
| `hSeedAll` (:2367-2371) | Per member thread, `QRequires` and `QEnsures` both hold at the start world. | OWN-LOGIC | none (caller side) — FLAG (see §3: `Post` at entry) |
| `hBlattAll` (:2372-2384) | Uniform per-firing preservation: every leaf fired at every reachable intermediate machine preserves that thread's `Pre`/`Post` both ways. | OWN-LOGIC | partial: `hBlattAll_speicherfest_aus_feuerung` (`Maschine.lean:4093`) closes only the nine memory-preserving leaves; the seven memory-changing/oracle leaves stay owed — FLAG (see §3) |
| `hne : g₁ ≠ g₂` (:2385) | The two witnessed accesses are by distinct threads. | DATA | witness selection per use |
| `hw₁` (:2387) | Step `j₁` of the run is thread `g₁` accessing table `t₀`. | DATA | run witness per use |
| `hw₂` (:2388) | Step `j₂` of the run is thread `g₂` accessing table `t₀`. | DATA | run witness per use |
| `hstart : c.tick 0 ≤ S` (:2389) | The first clock tick is within one period (the sampling induction starts). | OPEN | none (per-clock fact; consumed by `TickClock.covers`, `Fristlauf.lean:299`) |
| `hpd : p.pruef < d` (:2391) | The deadline is strictly after the check. | DATA | per-deadline instantiation |
| `hdl : d < p.lauf` (:2391) | The deadline is strictly before the use. | DATA | per-deadline instantiation |
| `hspace : deadlineSpacing S p d` (:2392) | The use waits out the sampling window: `d + S ≤ p.lauf` (`Fristlauf.lean:388`). | NAMED-HW | none in Lean (per-use premise; a watchdog at the use or deadline granularity above `S` discharges it per run, `Fristlauf.lean:384-389`) |
| `hLowering : Absenkung` (:2393) | A lowering witness: per-primitive C-form count with cap 18 (`Ziel.lean:83`). | GABBRO-DUTY | the measured witness `absenkung` (`Ziel.lean:97`, value 17) via `ziel_l5_absenkung_zeuge` (`Ziel.lean:474`); its bound by `absenkung_haelt_schranke` (`Ziel.lean:110`) / `ziel_l5_schranke` (`Ziel.lean:478`) |

Discharge ledger for the sequential-logic leg (C3), for the checker: `hMemAll` (the
`stabil_aus_lauf` memory premise) is premise-free at Q-instantiation by
`speicherVertrag_aus_Q` (`Extraktion.lean:3924`, Q-contracts read only live memory);
the frame premise `hAb` is folded inside the `_Q` proof (`Ziel.lean:2417-2421`) from the four
footprint premises by `haengtAb_vertrag_gesamt` (`Extraktion.lean:1568`); the interference
check is derived inside from `hForm` by `interferenceFree_of_invariantForm`
(`InterferenzAllgemein.lean:1213`); the context is derived inside from
`hEntry`/`hReturn`/`hWatch` (+ frame/guards) by `invariantenKontext_aus_disziplin`
(`InterferenzAllgemein.lean:1530`).

## 3. Inapplicability flags

Every flagged premise is load-bearing (each feeds the proof term at `Ziel.lean:2425-2428`),
so the flag is about fit, not redundancy: an ordinary program that cannot meet the premise
cannot use this theorem.

1. **`hSeedAll` demands `Post` at entry (strongest flag).** `hSeedAll` (`Ziel.lean:2367-2371`)
   requires `QEnsures P (J.code g)` at the start world, because the underlying
   `SpecTriple.ensuresHead` (`InterferenzAllgemein.lean:1083`) requires the ensures-side at the
   chain head. An ordinary ensures-clause (postcondition established by running) is false at
   entry. Only ensures-clauses that already hold initially (e.g. invariant-shaped ones) fit.
2. **`hForm` restricts contracts to invariant form.** `InvariantForm`
   (`InterferenzAllgemein.lean:1204`) requires each thread's `Pre ∧ Post` to coincide, at every
   world, with some carrier invariant. Ordinary functional contracts (e.g. relating result to
   input) are not a carrier invariant; such programs keep owing the general per-run
   interference proof, which this variant exists to avoid.
3. **`hReturn`/`hWatch` quantify over all carriers and all steps.** `hReturn` requires every
   writing step to restore every carrier's invariant; `hWatch` requires every writing step to
   hold the guard. Ordinary programs with carriers outside any locking discipline, or with
   lock-free writes, meet neither. Table instances of the watch discharge via
   `wache_aus_schuld` (`InterferenzAllgemein.lean:1481`), but globals stay checker-side and the
   premise itself is still owed here.
4. **`hGuardEx` requires a guard for every carrier.** `hGuardEx` (`Ziel.lean:2339`) asks a watch
   lock for each `c : D.Tab ⊕ D.Glob`, including unshared and global carriers that ordinary
   declarations leave unguarded.
5. **`hJw`/`hJsf` assert chain-machine identity.** Equality of chain worlds with recorded
   machine worlds (`Ziel.lean:2365-2366`) is the open chain-to-machine wiring; the only closer,
   `kette_aus_lauf_bezeugt_closed` (`Ziel.lean:2235`), is single-thread, while this goal's C12
   leg needs two distinct threads. Moreover chain steps are whole critical sections
   (`InterferenzAllgemein.lean:1277-1293`) while machine worlds advance per event, so the
   equality also presumes a grain match ordinary runs do not have by construction.
6. **`hBlattAll` is uniform over all reachable machines.** It quantifies over every
   intermediate `M₀`/`pc₀` with `PCReach` (`Ziel.lean:2372-2373`), not just the executed path;
   only the nine memory-preserving leaves discharge via `hBlattAll_speicherfest_aus_feuerung`
   (`Maschine.lean:4093`). Every program whose contract touches a written slot/global owes the
   seven remaining leaf shapes per leaf.
7. **`hDeck` bans lock-free sharing.** `GeteiltGedeckt` (`InterferenzAllgemein.lean:299`) forces
   any carrier written by two threads to be shared with a common guard lock; ordinary
   programs with atomic or lock-free shared writes (or racy ones) are outside the covered class.
8. **C4/C12 legs narrow the runs covered.** The probe leg concludes expiry answered
   (`:2400-2401`), so with `hpd`/`hdl` (`:2391`) only deadlines strictly inside the open
   check-use interval fit — endpoints (`d = pruef`, `d = lauf`) are `ok` by `fristlauf`
   (`Fristlauf.lean:131-135`) and absent deadlines (`none`) are `ok` too; those runs cannot
   feed this conclusion. The reduction leg needs two exhibited same-table accesses by distinct
   threads (`hw₁`, `hw₂`, `hne`); single-threaded runs and runs without shared table accesses
   supply no such witnesses.
9. **`hO` excludes event-emitting oracles.** `GutO` (`Satz.lean:794`) forces
   `(O.wirkt …).1.spur = σ.spur`; oracles modelling DMA or other event-producing hardware do
   not satisfy it and stay open (the `Extraktion` §18 remainder).
10. **`hspace` is a per-use hardware timing proof.** `deadlineSpacing` (`Fristlauf.lean:388`) is
    never modelled, only named; each deadline of each of the 29 deadline kinds owes a watchdog
    or granularity argument outside Lean.

## 4. Cuts (what is not proved here)

This is a map, not a theorem: nothing is proved in this document. Within the mapped theorem:
C6 (`zwei_fehler`) holds unconditionally by case split, so it carries no assurance beyond
"the datatype has no fourth error"; C5 re-states the supplied witness's own field
(`hLowering.begrenzt`); the run premise `h`, the wiring `hJw`/`hJsf`, the per-leaf `hBlattAll`
(write fragment), the per-carrier discipline (`hEntry`/`hReturn`/global `hWatch`), the
per-thread form exhibit (`hForm`), the head validity (`hSeedAll`), the oracle bound (`hO`),
the separation facts (`hMSep`/`hCSep`), the footprint containments, and the per-use spacing
(`hspace`) are all owed per program, per chain, or per run. The non-invariant fragment
(assertions over shared carriers not in invariant form) is not covered by this variant at all.

## 5. Flags from the independent draft B (lane 17) that draft A does not carry

Draft B was written independently of this map; its premise table agrees with §2. These
flags are new or sharper, and each was re-read against the Lean before being folded in:

- **B8 -- `hMSep` excludes two threads running the same function.** `PCMarkSep`
  (`Maschine.lean:1309`) demands that no mark code named by one thread's program text is
  named by another's. `progAus` (`Extraktion.lean:2572`) extracts each thread's text from
  the body of the function it runs, so two threads running the same function carry the same
  atoms, and every mark named in that body appears in both texts. The most ordinary
  multithreaded shape -- the same routine on two threads -- therefore cannot reach the W4
  discharge (`pc_discharge_einfaedig`). Marks are static names (`D.Marke`), not per-thread
  instances; a per-thread mark needs an instance notion the extraction does not have.
- **B5 -- `hBlattAll` excludes break-and-restore.** The per-firing `↔` forbids a thread's own
  step from breaking its contract even temporarily (a counter mid-update, two linked fields
  updated in sequence). Only contracts that no own write can touch discharge.
- **B11 -- the lowering leg is numeric only.** `hLowering.proPrimitiv ≤ 18` says nothing about
  the 30 undecided C forms in real output (`Ziel.lean:68-73`); count preservation for the
  seven modeled ops lives downstream (`Budget.lean:681-690`).
- **B12 -- the order leg names one table and two accesses.** Conjunct 12 orders exactly
  `hw₁`/`hw₂` on `t₀`; everything else an ordinary program races on is not ordered by this
  theorem (shared globals, more than two sections, restoring writers stay open).
