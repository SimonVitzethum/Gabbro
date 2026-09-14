# Verdict on `GabbroZiel` (independent Opus reviewer, third round, 2026-09-15)

*Base: `master` at `f19a30d7` (the worktree was fast-forwarded from `a8b59d85` before reading).
Lean 4.33.1. The server directory is `~/gabbro-muse/opus-urteil3/` on ki-pc-fisch-101. There,
`lake build Grammatik.Zielsatz.Proben Grammatik.Zielsatz.AkzeptiertZeuge` exits 0 with 85 jobs,
and `gabbro_ziel` prints `[propext, Classical.choice, Quot.sound]`. The probe file is
`grammatik/.tmp/urteil_opus15.lean` and is NOT committed. `lake env lean` on it exits 0 with 0
errors, and every probe prints either `[propext]` or `[propext, Classical.choice, Quot.sound]`.
No cargo was run and nothing was pushed. Rust statements come from reading the source, not from
running a binary. I read the earlier verdicts `URTEIL-*-2026-09-14`, but no `URTEIL-*-2026-09-15*`
file.*

> **Goal (owner):** a Gabbro user proves only their OWN logic plus named hardware
> assumptions. Memory safety, data-race freedom, contracts where claimed in concurrent runs,
> and time are carried by the language.

## VERDICT: **`GabbroZiel` is not the goal, yet.** The fix is small.

`Ziel` names the right legs, and each leg means close to what its words say. There are named
weakenings, listed in §5. The statement fails at review question 3, in the probe-A/D class this
round exists to catch.

**Probe A goes through `GabbroZiel` again once a lock invariant is `false`** (probe P1):
- The Rust checker accepts `invariant false`. The concrete Bool accepts the program.
- `NutzerPflicht` holds for a program whose every function has `ensures false`. The obligation
  is empty because `HavocOk S` has no member.
- The conclusion is empty because no start is admissible.

Nothing in the three premise groups rules this out. The two start conditions that do the
excluding (`StartZulaessig.req` and `.sperren`) belong to no group. The shipped refutation of
probe A needs a satisfiable lock family (`NutzerWiderlegt`, SpecProben.lean:57), and that is a
side condition of the probe, not of the statement. Two more parameters, `ws` and `Q`, are not
bound to the program either (§2).

---

## 1. Question 1: the legs of `Ziel` (Spec.lean:296-314)

| Leg | Lean predicate | Does it mean the words? |
|---|---|---|
| memory safety | `speicherSicher : SpurInv M` (RennfreiVoll.lean:249) | Only in part. `SpurInv` is the ACCESS DISCIPLINE: every recorded access carries its carrier's guards, and those locks are held. Bounds and type safety are INTRINSIC: an `.index n` value lies in range by its type, and a pointer is a table name with a typed index (`assignDurch`, Syntax.lean:452). No heap, no dangling reference and no out-of-range index can be expressed in `Programm D`. So the leg is honest *for the model*, but its force rests on the `.gab`→`Programm D` step (§4). **Not covered:** stack depth. G's stacks are unbounded and recursion is admitted, so a recursive function that never returns meets any `ensures` (partial correctness), while the emitted C overflows its stack. Neither the header nor PLAN §6 names this. |
| data-race freedom | `rennfrei : RennfreiBis` (Spec.lean:229) | Yes, over EVERY carrier except `atomic` globals and publish payloads. Reads are recorded (`World.lese`, Semantik.lean:87), and "access" also counts a memory change (`ZugriffG`, RennfreiVoll.lean:333). The ordering is release by one thread and acquire by the other (`GeordnetG`, :563). **Weakening:** a publish payload is simply dropped, with no replacement conjunct. The A10 pairing is not stated. `AkzeptiertSpec.renn` (Spec.lean:152) exempts payloads too, so by reading the definitions (not probed), two declared starts that WRITE one payload (no reads) pass both. That is a real C11 race on a non-atomic object, which the Rust rule H013 refuses (it has no payload exemption) but the Lean Bool does not. Named in the header ("excluded from `rennfrei`"). The granularity is the whole table or global, which is conservative. |
| contracts where claimed | `vertrag` (`VertragAmOrtG`, ZielOrt.lean:67), `sperrInv` (`SperrInvG`, SperreMaschine.lean:424), `invRueck`/`invGrund`, `startEnde`, `keinStartGrund`, `keinLogikHalt` (ZielOrtGanz.lean:658) | Yes, at the places a user expects. `requires` holds at every logged entry (so the caller's duty is carried) and `ensures` at every logged value return, both at the concurrent worlds. Every free lock has its invariant in memory. Owed table invariants hold at value and reason returns, the start function completes, and no thread stops at a loop-invariant or state-transition check. **Not claimed:** invariants at entry or while locks are held, and `ensures` at reason exits (none is declared). |
| progress | `keineVerklemmung`, `fortschritt` (`FortschrittG`, Spec.lean:284) | Yes, and it matters for the other legs. Every thread is finished, waits for a lock another thread holds, stands at a NAMED hardware stop, or can step. So G cannot make a safety leg vacuous by silently getting stuck. |
| time | `zeit : ZeitAb` (Spec.lean:289) | **Weaker than the word, and weaker than PLAN §2.** It is a bound on the thread's OWN G-steps per frame: `kostenTief` (KostenG.lean:955) is syntax-computed, and it holds only for frames with a finite call tree (`rufTief`, :964). Recursion and indirect calls get no bound. A `forever` loop's bound is its body times `passes`, and since `passes` is universally quantified, that is no bound at all. Lock waits and axiom durations are not counted. PLAN §2 promised "own steps ≤ declared `costs`", but the declared `costs` are not in `Deklaration`. The header names this. The leg is true of G alone (`frame_schritte_beschraenkt` has no premise), so it is "carried", but it is a step count, not time. |

## 2. Question 2: premise groups, and the checker today

| Premise | Group | Remark |
|---|---|---|
| `C.akzeptiert … = true`, `∀ C : Pruefer` | (a) checker | **The Bool is decoration.** `p4_ziel_iff` proves `GabbroZiel ↔` the same statement with premise (a) replaced by the Prop `AkzeptiertSpec P S fs.1 ws`. `Pruefer` accepts any classical predicate (`specPruefer`), and the always-false checker is a `Pruefer` too (`nullPruefer`). The statement therefore does not name the Rust checker, and says nothing about it. It is decidable: `Akzeptiert` is a computable Bool with `akzeptiert_iff` for complete lists. |
| `NutzerPflicht` (Spec.lean:190) | (b) user | `KoerperGutS`, `InvGutS` and `InvGutGrund` hold at EVERY budget, so probe D stays closed. `SperrInvLokal` and `AxEnsLokal` are really well-formedness of written specs, which is checker work: Rust N275 decides the read half of the first, and nothing decides the second because axioms are not exportable. |
| `HardwareAnnahmen` (Spec.lean:197) | (c) hardware | These are `GutO`, `RegLokal` and `AxVertragO Q`. **`RegLokal` is stronger than hardware:** a register without `depends` (`rtraeger = []`, the default at Syntax.lean:185) answers THE SAME in every world (`p3_register_konstant`). A user proof may use that two reads of a status register are equal, which a real volatile device breaks. It is named, but not per register and not by the user. |
| `S`, `Q`, `ws` | data, **free** | None of them is tied to `P` (`Programm` has no starts, no lock family and no axiom ensures). `Q` IS the content of the named hardware assumption. `ws` IS the thread-creation assumption. **`ws` changes the Bool:** the two-writer program `akP3` is refused with its real starts and ACCEPTED with `ws = []` (`p5_leer_akzeptiert`). With `ws = []` the statement then covers only threads whose functions write nothing and read nothing shared (`Ruhig`). This is honest, but it depends on a list no tool derives: the exporter drops `concurrent` (lean_g.rs:81-82). |
| `StartZulaessig` (Spec.lean:214) | run data, restricted | `wurzel` and `einmal` are the runtime assumption A4: each declared start runs on ONE thread and the root runs elsewhere. This excludes the same busy function on two cores (`mTafel_doppelt_falsch`, AkzeptiertZeuge.lean:159), which is the ordinary SMP shape. **`req` (start `requires` at the start memory) and `sperren` (every lock invariant at the start memory) are in NO group.** No tool checks them: Rust has no rule on initial values against lock invariants or start `requires`. The user does not prove them and they are not a named assumption. By PLAN §2 ("a premise that fits none of the three is a finding"), they are a finding. |
| `fs`, `ls`, `cs` as `Aufzaehlung` | by type | Harmless. They only exclude infinite declarations. |
| `passes`, `sp`, `init`, `M` | ∀ run data | Correct, because `passes` is quantified in the obligation too. |

**Does the Rust checker compute `AkzeptiertSpec` today? No, not as one Bool.** Nothing in
`crates/` or `instrumente/` computes `Akzeptiert` or runs `decide` on it; the only instances are
`mP`, the export of 104 with `ws = []`, and hand fixtures. Per component:

| Component | Rust today |
|---|---|
| `frag` | Only through the exporter's structure. `lean_g.rs:2818` prints `example : programmImFragmentG … := by decide`, and forms outside the fragment are refused with LG001–LG007. |
| `abg` | No rule ("closed by construction", fusswache2.rs:43-46). |
| `fuss` | `fusswache2.rs` N290–N293 are errors. They judge thread identity per START INDEX, not per function; they accept reads inside `locks L` over carriers `L` protects, which Lean does not. The old E245–E249 are hints. |
| `stufen` | Only analogous rules: H006/H012/N294 are rank rules. The floors are computed by the exporter. |
| `sperrOrte` | By construction (`protects` = `orte`), plus the printed `decide` examples. |
| `wurzeln` | **Only partly.** N240 bans COMMON signature locks between distinct starts. No rule bans ANY signature lock on a start, and no rule bans reasons on a start. |
| `renn` | H013, H222 and W001–W003 are errors, per `entry`. H013 is stricter per entry and has no payload exemption. |

**The two directions disagree.** Rust accepts `beispiele/108`'s `concurrent { read_a, read_c }`
(disjoint signature locks, N240). The goal's Bool refuses those starts for every lock family
(`p2_108_abgelehnt`).

## 3. Question 3: adversarial probes (`grammatik/.tmp/urteil_opus15.lean`, 0 errors)

- **P1: an unsatisfiable lock invariant empties (b) and (d). DEFECT.** Take `sF : SperrInv zD
  := ⟨fun _ => [], fun _ _ => false⟩`.
  - `p1_akzeptiert`: `Akzeptiert paP sF zFs [()] [.inl ()] [zHaupt] = true`, where `paP` is
    probe A, with `ensures false` everywhere.
  - `p1_nutzer`: `NutzerPflicht paP sF (axWahr zD)`.
  - `p1_hardware`: the hardware group is satisfiable.
  - `p1_kein_start`: NO `StartZulaessig` exists, not even the root on every thread.

  The mechanism is that `KoerperGutS`, `InvGutS` and `InvGutGrund` all start with `∀ U, HavocOk S U
  → …` (SperreFuss.lean:374, SperreSem.lean:71). So ONE unsatisfiable invariant, on any lock,
  taken or not, empties EVERY function's obligation.

  At the surface, `lock D protects {…} rank 0 invariant false;` passes N275–N277 (`Falsch` is pure,
  sperrinv.rs:122-125), and `lean-g` exports it as `gS.inv` (lean_g.rs:2855-2858). The earlier
  verdict's "`HavocOk S` is inhabited whenever `hSstart` + `SperrInvOk`" was true while `hSstart`
  was a PREMISE. `GabbroZiel` moved it into the start restriction, on the conclusion side, and so
  re-opened the hole.
- **P2: no program with a closed C chain is covered on a busy thread.** The export of 104 is
  accepted only with `ws = []` (`gP_akzeptiert`), because both functions hold `M` by signature
  (`p2_keine_wurzel`). Every admissible start then runs the idle root on EVERY thread
  (`p2_nur_ruhe`), so the statement says nothing about 104's bodies. 108 (`p2_108_abgelehnt`) and
  118 (both `requires Held(K)`) are the same.
- **P3: `RegLokal` makes a register without `depends` a constant** (`p3_register_konstant`). The
  hardware class is not empty, but it is narrower than hardware, and user logic may exploit it.
- **P4: the Pruefer quantifier.** A `Pruefer` whose Bool is always false exists. It is harmless
  only because the statement quantifies over EVERY `C`, and it shows that premise (a) is the Prop,
  not "what Rust computes".
- **P5: `ws` is a free knob.** It is shown on `akP3` above. It empties no obligation, but it
  weakens the checker verdict and shrinks the covered runs, and nothing in the statement says
  which `ws` is the program's.
- **Tried, no defect:**
  - `Q := false`. Only oracles whose answers never fit exist, so every run stops at a named
    hardware stop. This is the honest kind of vacuity: a false named assumption.
  - `P.mitRuhe`. The root writes nothing, its contracts are `true`, and no function pointer
    reaches it (MitRuhe.lean header). It hides nothing, but it makes `StartZulaessig` satisfiable
    for EVERY program, so satisfiability of the start is no evidence of content. The shipped
    positives rightly demand that every declared start runs (`Erfuellbar`).
  - The handler class `RespektiertRahmen`. It is inhabited by handlers that answer `hardware`,
    and a callee with `ensures false` constrains only the `ok` branch, which is standard modular
    Hoare logic.
  - `Aufzaehlung`. Complete by its type.
  - A start with `requires false`. That start is not admitted and its body's obligation is empty,
    which is the standard reading. It is the same unowned `req` premise as in P1, though.

## 4. Question 4: G against the language, and G against the C

- **G against the sequential semantics.** The adequacy that exists is:
  - forward `rufG_adaequat*`: existential, against `rufRumpf` (contracts ignored), with
    depth-admitted direct calls;
  - converse `rufG_adaequat_ruf_umkehr`: only the loop-free, axiom-free fragment;
  - `else` inside loops: shown by the replay equalities and a witness, not by a general theorem
    (SATZKARTE §15.3/15.6).

  No general theorem covers indirect calls. `gabbro_ziel` does not route through adequacy. It
  links the sequential obligation (`execEndH`) to G by the replay (`Begruendet`,
  SperreBeweis.lean §0b). So "G runs what the language means" rests on (i) a human reading the 70
  rules of `RufSchrittG`, (ii) partial adequacy, and (iii) `FortschrittG`, which rules out
  UNNAMED stuck states. It does not rule out G taking a DIFFERENT step than the C.
- **G against the C.** The chain count is 1: `schlusssatz_104`, sequential, with its own machine
  `gPB` and its own start premise `LaufzeitStart` (Schlusssatz104.lean:1460). It does not
  compose with `GabbroZiel`: under `GabbroZiel`, 104 runs only idle threads (P2). Stage (b) does
  not exist: the lock primitives, thread creation and DRF-SC are not premises of any theorem.
- **The exporter is the only `.gab` → `Programm D` path**, and it:
  - exports `requires := fun _ => .wahr` for every function (lean_g.rs:2803), so the caller duty
    of the SOURCE contracts is not what `VertragAmOrtG` carries;
  - drops `concurrent`, so it gives no `ws`;
  - refuses `entry`/`boot`, globals, devices, axioms, `forever`/`retry` and indirect calls.

  So the program class the goal speaks about is reachable today only by hand-written terms. That
  is an implementation distance, not a statement defect, but it bounds every claim that
  `GabbroZiel` is "about the program the user wrote".

## 5. What makes it the goal: repairs, and the gaps that may stay named

**Repairs to the statement (the verdict turns on the first; the rest are needed for "nothing weaker"):**
1. **Give `sperren` and `req` an owner.** Make "the program's declared initial memory satisfies
   every lock invariant and every start `requires`" a USER obligation in `NutzerPflicht`, over a
   declared initial memory that is part of the program, and quantify starts from that memory.
   The minimum is to add `∃ sp, ∀ L, S.inv L sp = true` to `NutzerPflicht`, which kills P1 via
   `havocOk_misch`, and to name "the loader's initial memory satisfies them" in the ONE
   assumption list. Test: `p1_nutzer` must no longer be derivable, and probe A must be refuted
   with NO side condition on `S`.
2. **Bind `ws` (and `Q`, `S`) to `P`.** Either add a start list, lock family and axiom ensures
   as fields of the program the exporter produces, or state `GabbroZiel` over the exporter's
   output. Then name "the runtime starts exactly `ws`, each once, and the root elsewhere" (A4) in
   the assumption list.
3. **Give payloads a conjunct.** Either drop `¬ PaarungAusgenommen` from the write-write case of
   `RennfreiBis` and `renn` (as H013 already does), or add the A10 pairing claim.

**Gaps that can stay named (with 1–3 done, the verdict would read "the goal with named gaps"):**
- time as a syntactic own-step bound, not the declared `costs`, no waiting bound, no termination;
- stack depth (not named today, add it to PLAN §6);
- `RegLokal` register constancy without `depends`;
- one thread per busy start (no SMP-symmetric code);
- invariants only at returns;
- weak memory beyond DRF-SC;
- G↔C for concurrency (stage (b)) and the single sequential chain;
- `else`-in-loop and indirect-call adequacy;
- the Rust checker computes neither `wurzeln` nor `abg`, and judges `fuss` differently.

---
CUTS: this file proves nothing by itself. The probe theorems live in the uncommitted
`grammatik/.tmp/urteil_opus15.lean` (checked on ki-pc-fisch-101, EXIT 0, 0 errors). Rust
behaviour comes from reading `crates/` at `f19a30d7`: no current checker binary was run, and
the local one dates from 2026-09-11. The claim that `invariant false` passes N275–N277 and
exports is from source reading and was not executed. No existing file was changed.
