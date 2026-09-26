/-
  File:    Grammatik/Zielsatz/Spec.lean -- THE GOAL AS ONE STATEMENT (PLAN-ZIELSATZ.md step 2).
  Content: definitions and `def GabbroZiel : Prop`. No proof. Review target.

  Goal (owner): a user proves only their OWN logic plus named hardware assumptions; memory
  safety, data-race freedom, contracts where claimed in concurrent runs, and time are carried
  by the language.

  SHAPE (since 2026-09-15). Everything is about ONE value `E : Einheit D`, the program the
  user wrote: code with contracts `E.P`, lock invariants `E.S`, axiom ensures `E.Q`, declared
  starts with arguments `E.starts` (functions `E.ws`), declared initial memory `E.sp0`.
  Premises in four groups:
  (a) `C.akzeptiert E fs ls cs = true` -- ONE Bool of the checker (`Pruefer`: the Bool and its
      soundness against `AkzeptiertSpec`; the concrete checker is `akzeptiert_pruefer`,
      Zielsatz/Akzeptiert.lean, computing `Akzeptiert E.P E.S fs ls cs E.ws`);
  (b) `NutzerPflicht E` -- the user's logic: the bodies at EVERY `forever` budget
      (`LogikPflicht`) AND the start (`StartPflicht`: every lock invariant at `E.sp0`, every
      declared start's `requires` there with its declared arguments);
  (c) `HardwareAnnahmen O E.Q` -- the hardware and foreign code;
  (d) `Laufzeit E sp init` -- the loader and the runtime's thread creation (A4).
  Then for every budget, every set of initially live threads and every reached machine of the
  THREAD machine (FadenMaschine.lean: machine G plus threads spawned at run time by `start` and
  `child`, since 2026-09-26): `ZielF` -- `Ziel` on its G state plus the spawn and join legs.
  `fs`/`ls`/`cs` (functions, locks, carriers) are `Aufzaehlung`s (complete by their type:
  finite declarations only).

  WHAT CHANGED ON 2026-09-26 (OPUS AGENT A, OFFEN O21/O22), AND WHY -- a REVIEWED DIFF of this
  file (the review itself: messung/OPUS-A-LAUFZEITFAEDEN.md):
  * THE GAP. The language creates threads at run time -- the hosted `start { f, g };` (the
    starter waits for its roots: a join; Rust `N458`-`N462`) and the `child { … }` region of a
    stack gate (its own thread on the handed stack, entered holding nothing; Rust `N446`-`N452`,
    `N456`, `N457`) -- and this statement fixed the thread population at the start: (d) let a
    thread run only the idle root or a declared start, and `Ziel` spoke about G runs only. A
    child reached the goal only through `klon_ziel` (CloneHandoff.lean, outside the
    statement), a `start` not at all (NOT CLAIMED until this diff).
  * THE DIFF. (i) `Einheit` gains `gestartet` (default `[]`): the run-time roots with their
    arguments. (ii) `Einheit.ws` lists every run-time root TWICE: a root may run on any number
    of threads, so the checker judges it as a pool routine -- `AkzeptiertSpec` is textually
    unchanged, and its `wurzeln` (no signature lock, no reasons) and `einzeln` (pool-safe)
    components now decide the model half of `N458`/`N462` (for a lifted `child` region: of
    `N456`/`N457`), `Getrennt`/`SchreibGetrennt` pair a root with every start and with itself
    (`akzeptiertSpec_gestartet`, Zielsatz/FaedenVor.lean). (iii) (b) `StartPflicht.req` and
    (d) `Laufzeit.start` range over `E.starts ++ E.gestartet`: the runtime may place a thread
    slot at a run-time root, and its `requires` is the user's duty at `E.sp0`, as for a
    declared start. (iv) THE CONCLUSION moves from machine G to the THREAD MACHINE
    (`FadenMaschine`, `FadenSchritt`, `FadenErreichbar`, `FadenStart`; FadenMaschine.lean):
    a G machine plus the live set. A slot that is not live is DORMANT and untouched until a
    live thread spawns it -- by `start` (only while the starter holds no lock, the model side
    of `N461`; the starter then takes no step until every root is finished, and the `join`
    step ends the wait) or by `kind` (the parent goes on). No G rule changed or was added. The
    conclusion is `ZielF` on every reachable thread machine, from any set `lebt0` of initially
    live threads: `Ziel` on its G state (every spawned thread IS a G thread there), and the
    legs `schlafendUnberuehrt`, `schlafendFrei` (a spawned thread enters holding nothing),
    `joinFrei` (a waiting starter holds nothing), `keineVerklemmung` and `keinZyklus` WITH
    join waits (`KeinWarteZyklusF`: no cycle through locks and joins), and `fortschritt`
    (`FortschrittF`: every stop named, the join wait `JoinWartet` among them).
  * WHY NOTHING IS WEAKENED (theorems, Zielsatz/FaedenVor.lean and Beweis.lean):
    `fadenErreichbar_von_G` -- every G run is a thread-machine run with every thread live and
    nothing spawned, so `Ziel` on every G run (`gabbro_ziel_g`, the statement of before, which
    every caller of `gabbro_ziel` now uses) is a corollary; `ws_ohne_gestartet`,
    `startPflicht_vor_iff`, `laufzeit_vor_iff` -- on a unit with `gestartet = []` (every unit
    of before) the checker's `ws`, (b) and (d) are word for word the old ones;
    `pruefer_aus_vor`, `pruefer_aus_vor_gleich` -- every checker of the old interface is a
    checker of the new one with the same verdict on every unit of before; and
    `gabbro_ziel_vor : GabbroZielVor` -- the OLD STATEMENT, VERBATIM over the units of
    before, is proved from the new one. The new statement adds units with run-time roots and
    runs with spawns and joins, and the legs above; it drops nothing.
  * WHAT CARRIES THE PROOF: the bridge `fadenErreichbar_G` (a spawn and a join do not move the
    G state), so `ziel_aus` applies unchanged; the thread-machine invariant `FadenInv` (a
    dormant slot is its start thread, a joining starter holds no lock and is live, an awaited
    root is live and ranks above its starter, ranks are bounded by the spawn clock); the join
    legs from lock ranks plus the ghost spawn rank (Zielsatz/Faeden.lean).
  * NEW NAMED ASSUMPTIONS (in THE ONE LIST below, (d)): a run-time root's slot is placed in the
    start machine, so its ARGUMENTS are the unit's (a `start` root takes none, `N458`; the
    exporter carries no root with parameters) and its frame's ghost ENTRY WORLD (`s0`, the
    logged entry) is the start world -- its body reads the memory of the moment it steps, as a
    late-scheduled declared start does; and the spawn SITES are the checked ones: the lowering
    spawns a `start` root only where the starter holds nothing (`N461`) and waits for all its
    roots, and enters a `child` by jump at the region with an empty held set (`N456`, the
    jump assumption of OFFEN O21) -- translation validation's to check, as every "G is the
    meaning of the C".
  * WITNESSES (Zielsatz/FaedenZeuge.lean): `sj_lauf` (a `start` spawns two threads, both write
    and finish, the join fires only then, the starter calls and writes), `kw2_lauf` (a `child`
    runs concurrently with its parent: parent call, child write, parent write),
    `spawn_start_ziel`/`spawn_kind_ziel` (every leg of `ZielF` on spawn runs of ACCEPTED units,
    through `gabbro_ziel`), refusals `start_nicht_poolsicher_abgelehnt` (a non-pool-safe root,
    at the pool component), `kind_unter_sperre_abgelehnt` (a region lifted from inside `locks`
    needs the lock at entry, refused at the root component), `start_unter_sperre_kein_schritt`
    (no start under a held lock), and `klon_als_faden` (fix lane F9's clone machine is a
    special case of the thread machine).

  WHAT CHANGED ON 2026-09-22 (FIX LANE F11, reviews G02 F1/G12 F1, OFFEN O19), AND WHY -- a
  REVIEWED DIFF of this file; NO premise moved, `Ziel` gained ONE leg:
  * THE GAP. An `entry … vector … via idt` dispatch root travels into the model as an ordinary
    declared start (see (d) below), and G interleaves threads freely. So the configuration the
    Rust `H102` refuses -- a handler takes, on the core it interrupted, a lock that core's
    thread holds without `masks irqs` (`beispiele/gift/460`) -- is no deadlock in G: there the
    holder simply steps on. `D.maskiert` (the exported `masks irqs`, lane 255) was read by
    nothing here, so `beispiele/59`'s exported deadlock freedom was NOT interrupt-deadlock
    freedom. Simon's decision (2026-09-21): real coverage, not a NOT-CLAIMED line.
  * THE DIFF. New `KernPlan kern H ms fs n` (a core assignment, a handler set, and the two
    hardware facts about one core: a handler takes its FIRST step only where no other thread
    of its core holds a masked lock -- that is what `cli`/`sti` DO -- and from there it runs
    to completion before that thread continues -- that is what preemption IS). New leg
    `keinKernHalt : KernHaltG P O passes M0 M` of `Ziel`: on such a run a handler NEVER stands
    at a lock a thread of its own core holds.
  * WHY NOTHING IS WEAKENED, AND HOW MUCH IT ADDS. `Ziel` gains a conjunct and loses none,
    and no premise of `GabbroZiel` changed, so it covers exactly the same programs and runs,
    and every earlier theorem about them still holds. It is NOT strictly stronger, though,
    and the word was wrong here until the Spec-diff review of 2026-09-23: the leg needs
    nothing from (a)-(d) and holds for EVERY program of G with no premise (`kernHaltG_gilt`,
    Zielsatz/Masken.lean -- `ziel_aus` discharges `keinKernHalt` with it and nothing else),
    so the new `Ziel` is LOGICALLY EQUIVALENT to the `Ziel` before F11. It is the same kind
    of leg as `zeit`: what it adds is a READING of a core schedule that G itself does not
    know, and the whole program side sits in the leg's OWN hypotheses (`KernPlan`, and the
    masking discipline `H102`) -- which is also why it closes no gap by itself, and why O19
    stays open. What carries the proof is the frame invariant `MerkInvG` (FadenMerkmal),
    whose `Merkmal.sperre` field says which locks a body may take.
  * WHERE THE PROGRAM SIDE SITS, and why NOT in (a): the leg's own hypotheses name the
    handler threads (`H`), their cores (`kern`), their call graphs (`Z`) and features (`A`),
    and demand that every lock a HANDLER's features admit is declared `masks irqs` -- that is
    `H102`, decided by `maskenDisziplinB` (Zielsatz/Masken.lean) as the Rust checker decides
    it over the handler's call-graph hull (`kontexte.rs`). It is not a component of
    `AkzeptiertSpec`, because `Einheit` does not say WHICH declared start is a handler: the
    exporter drops `via idt` (the dispatch fact) and G has no cores. Closing that needs a
    field in `Einheit` and a core in the machine -- OFFEN O19, narrowed to exactly this.
  * WITNESSES (Zielsatz/MaskenZeuge.lean, on `Korpus59.lean`): `masken_zeuge` -- threads 0
    (`takt_verteiler`, the handler) and 1 (`ruf_verteiler`) on ONE core; thread 1 takes `RING`
    and the handler then steps and stands at `locks TAKT` (masked) while the interrupted
    thread is inside its section; the leg gives that `TAKT` is not held by that thread.
    `masken_disziplin_460` -- the `gift/460` shape (a handler root whose lock does not mask)
    is refused by the discipline Bool, `masken_disziplin_59` accepts example 59.

  WHAT CHANGED ON 2026-09-22 (FIX LANE F10, review G06 F1, OFFEN O18), AND WHY -- a REVIEWED
  DIFF of this file; the text of `GabbroZiel` and of `Ziel` is unchanged:
  * The Rust checker admits a symmetric worker pool, `concurrent { w, w }`, when `w` is
    pool-safe (lane 245, narrowed `N304`), while `AkzeptiertSpec.einzeln` demanded `ws.Nodup`
    and (d) let no declared start run on two threads -- so no theorem covered those programs.
    Simon's decision (2026-09-21): move the statement, and prove the legs.
  * THE DIFF. New `Mehrfach ws w` (`[w, w]` is a sublist of `ws`: declared at least twice).
    (a) `AkzeptiertSpec.einzeln : ws.Nodup` becomes `EinzelnPool P fs ws` (every routine
    declared twice is `PoolSicherW`: no signature lock, no reasons, every carrier its graph may
    write guarded or atomic); `Getrennt` pairs a start with a DIFFERENT OCCURRENCE (`w₁ ≠ w₂ ∨
    Mehrfach ws w₁`), so a pool routine's footprint carrier that its own graph may write needs a
    signature lock or a lock invariant, as for two different starts. (d) `Laufzeit.einmal` lets
    a routine run on several threads iff it is declared at least twice (before: never).
  * WHY NOTHING IS WEAKENED. (i) Every program the old checker accepted is accepted, with the
    same verdict: on a repetition-free `ws` `Mehrfach` never holds, so the new `Getrennt` is the
    old one and `EinzelnPool` holds vacuously (`akzeptiert_nodup_gleich`,
    `akzeptiertSpecVor_neu`, Zielsatz/PoolSym.lean). (ii) Both premise changes are
    RELAXATIONS: `AkzeptiertSpec` is the target of `Pruefer.korrekt`, so every old checker is
    still a `Pruefer` (`pruefer_vor_neu`), and every run (d) admitted before is admitted now.
    `GabbroZiel` therefore claims `Ziel` for strictly more programs and runs, and `Ziel` is the
    same structure. (iii) The proof needs nothing new below `Akzeptiert_ok`: every leg is
    proved over per-THREAD facts (`lokK`, `SchreibGetrenntK`, `StartExklusiv`), and the two
    places where distinctness entered -- `getrenntK_of`, `schreibGetrenntK_of` -- now take a
    same-routine pair from `Mehrfach`: the footprint pair from the occurrence form of
    `Getrennt`, the write pair from pool safety (a pool graph writes no unguarded, non-atomic
    carrier). Witnesses: `pool_ziel_zeuge` (a pool of two lock-guarded workers accepted by
    `akzeptiert_pruefer`, both instances stepped, `Ziel` by `gabbro_ziel`) and `pool_abgelehnt`
    (an unguarded writer twice is refused by the Bool), Zielsatz/PoolZeuge.lean.
  * WHAT STAYS NAMED: per-core writes (`accumulates … per cpu`, OFFEN O17) are exempt in the
    Rust pool rule and unmodelled; the exporter refuses such units, so they never reach (a).

  WHAT CHANGED ON 2026-09-15 (FOURTH ROUND), AND WHY (round-6 confirmation reviews,
  URTEIL-OPUS-2026-09-15d.md and URTEIL-MUSE-2026-09-15d.md, finding W1 -- a REVIEWED DIFF:
  `AkzeptiertSpec` gains the field `antworten`, `KopfHalt .nieZurueck` is narrowed to an
  axiom `-> never`; the text of `GabbroZiel` is unchanged):
  * W1 -- the third round named every EMPTY declared answer type as the stop `nieZurueck`,
    with the reason "the continuation is unreachable in the C as in G". That is true only
    for an axiom `-> never` (the C prototype is `_Noreturn`). An axiom whose result is
    `.grund 0`, an empty range, a sum without a value or a pointer type no function has is
    declared by an ORDINARY prototype: the C call returns some word and the continuation
    runs, covered by nothing;
    a register read never "does not return". Both reviewers reproduced it: probe A behind
    `let p = hol();` with `hol() -> fn(sig 5)` (no function has signature 5) met (b) and was
    certified. REPAIR, in the checker: the new component `antworten` (Bool `antwortenB`,
    Zielsatz/Akzeptiert.lean, decided exactly by `antwortenB_iff`) refuses every answer site
    of every body -- `bindAxiom`, `axiomCall`, `regLies`, `regLiesElse` (`Block.ants`,
    AntwortOrte.lean) -- whose declared answer type has no value, except an axiom whose
    result is `never` (`StelleOk`). Emptiness is decided from the declaration (range
    bounds, reason count, sum cases, the float range by three candidate witnesses, complete
    since the kernel IEEE order is transitive on finite values) and, for `fnptr n`, over the
    enumerated function list (`antwortB_iff`, EinpassenVoll.lean). G continues only with
    sub-blocks of the bodies (`antInvG_erreichbar`, AntwortOrte.lean), so on every reachable
    machine a thread can stand at an empty answer type only at an axiom `-> never`
    (`fort_dann`, Fortschritt.lean), and `KopfHalt .nieZurueck` now SAYS so: it holds only at
    an axiom call whose declared result is `never`. The reason of the ONE list is true
    again, and the escape is gone from it. Refuted: the round-6 probe, now refused by the
    checker (`w1_abgelehnt`, Zielsatz/ProbenW1.lean).
  * Precision (verdict): "for a satisfiable `E.Q`, oracles with fitting answers exist" reads
    "satisfiable at a DECODABLE value" (for a float: a well-formed one, `WertOk`).

  WHAT CHANGED ON 2026-09-15 (THIRD ROUND), AND WHY (round-5 confirmation review, finding
  G1 -- a REVIEWED DIFF of this file: `KopfHalt`, `HaltArt`, `FortschrittG` and the ONE list
  below. The text of `GabbroZiel` and every premise are unchanged; the leg `fortschritt` of
  `Ziel` names one more stop kind, and its `hardware` kind is narrowed to answerable types):
  * G1 -- `einpassen`, which holds a raw machine answer against the declared type, answered
    `none` for EVERY raw word of a `tagged` sum (an `ok | reason` syscall result), a float
    and a function pointer. So every call of an axiom with such a result stopped at
    `hardware (annahme a)`, every read of such a register at `hardware (register r)`, for
    EVERY oracle: a stop the MODEL decided, filed as hardware -- the class of F1. (b) does not
    constrain hardware outcomes, so probe A behind one such call met (b), passed the checker
    and was certified; `AxVertragO` was vacuous for those axioms. REPAIR, in the model
    (Semantik.lean): every type has a real decoding -- a sum packs the emitter's C value
    `struct { marke; union last; }` as `roh = marke + |cases| * last` (`summePasst`); a float
    is its IEEE-754 binary64 bit pattern, range-checked like a computed float
    (`gleitWortPasst`); a function pointer is a code address that the LOADED IMAGE names
    (`Orakel.zeiger`, a new oracle field -- which address a function has is the linker's and
    loader's, so it is the machine's answer; the signature number is checked against the
    declared `fnptr n`). PROVED (EinpassenVoll.lean): every value of every type (floats:
    well-formed) is the decoding of some raw word under some image (`einpassen_voll`), and
    the answer class is empty EXACTLY when the declared type has no value (`antwortLeer_iff`)
    -- the model decides no stop the declared type does not. Refuted: the G1 probes
    (Zielsatz/ProbenG1.lean) -- an axiom with an `ok | err` result and a float register, each
    in front of `ensures false`, both accepted by the checker: an oracle meeting (c) answers
    them (`g1_holen_antwortet`, `g1_temp_antwortet`), and no program with that code meets (b)
    (`g1PA_widerlegt`, whenever the declared ensures holds at SOME answer; `g1PR_widerlegt`).
  * THE EMPTY TYPES, and `never` (NEW kind `HaltArt.nieZurueck`): a declared answer type
    without a value (`never`, `.grund 0`, an empty range, a sum without a value, a pointer
    type no function has; `AntwortLeer`) admits no answer at all -- so its call does not
    return. That is not the machine answering "outside" a type that has no inside, so it is
    no longer a `hardware` stop: `KopfHalt .hardware` at an axiom or register head now
    requires the type to be answerable (`¬ AntwortLeer`), and `KopfHalt .nieZurueck` names
    the empty case; `FortschrittG` lists it. (NARROWED in the fourth round, W1: the reason
    below holds only for `-> never`; every other empty type is now refused by the checker,
    and `nieZurueck` is an axiom `-> never` alone.) WHY this and not "only in tail position": for
    `-> never` the non-return IS the declaration (the emitter writes `_Noreturn` on the
    prototype), the code after the call is unreachable in the C exactly as in G, and (b)
    still covers every statement BEFORE the call -- a `logik` outcome or a failed callee
    `requires` there is an outcome of the body, which `KoerperGutS` excludes. What stays
    vacuous is only the unreachable continuation and the function's own `ensures` (a body
    that never returns meets every `ensures`, partial correctness, as for recursion).
  * The replay of the user's sequential proof into G (`GleichRS`, `ZeigerGleich`) and the
    idle-root transfer (`OrakelRu`, MitRuheSemantik.lean: an oracle of `E.P.mitRuhe` may
    place the root at an address, which no translated type accepts) carry the image; no
    premise changed.

  WHAT CHANGED ON 2026-09-15 (SECOND ROUND), AND WHY (fourth Opus verdict,
  URTEIL-OPUS-2026-09-15b.md):
  * F1 -- a float result outside its declared range ended the body in `Hardware.ieee` for
    EVERY oracle: the kernel IEEE model (`gleitRechne`, Annex F) decides it from the
    program's own values, no machine is involved. `KoerperGutS` constrains only returns and
    `logik` outcomes, so probe A behind an out-of-range literal (`f1P`, SpecProben) met (b),
    passed the checker with its start declared and running, and was certified -- by a stop
    labelled "hardware". REPAIR, in the model: the three float forms without `else`
    (`gleit`, a float literal, `gleitVon`) answer `Logik.bereich` there (Semantik.lean,
    SperreSem.lean; `Hardware.ieee` is no longer produced). Why this and not a new clause
    "`≠ hardware ieee`" in (b): the range is the program's logic exactly as a `state`
    pre-state is (`Logik.vorzustand`), so the existing clause "no `logik` outcome" of
    `KoerperGutS` covers it with no new obligation shape; and the replay already carries
    `logik` outcomes to the machine, so the CONCLUSION gains it too: no reachable machine
    has a thread at a failing range check (`BereichG`, Fortschritt.lean, from the
    obligation) -- `FortschrittG` lists no float stop any more. Machine G's rules are
    unchanged (they fire only on an in-range result, as before). That the FPU computes the
    kernel model is `gleitkomma_ieee`, on the C side, where it always was. Refuted:
    `probeF1_widerlegt_gilt` (Proben.lean); the checker accepts `f1P` (`f1_akzeptiert`), so
    the refusal is (b)'s.
  * F2 -- `keineVerklemmung` ruled out only GLOBAL deadlock. New leg `keinZyklus`
    (`KeinWarteZyklus`): no threads `t₀ … tₙ₊₁ = t₀` each standing at a lock the next one
    holds, whatever the other threads do; proved from the rank invariant
    (`kein_warteZyklusG`, Zielsatz/Beweis.lean).
  * F3 -- the named stops are now of three KINDS (`HaltArt`) and listed, with their
    reasons, in THE ONE ASSUMPTION LIST below: `hardware` (axiom and register answers),
    `flagge` (an `awaits` whose flag is not visible: a WAIT, no longer called hardware),
    `budget` (a spent `forever` budget: a model artefact, not called hardware).
  * Header corrections: `speicherSicher` needs no checker (only `GutO`); "`Q := false`
    empties (c)" holds only for axioms without a result (see (c) `AxVertragO`).

  WHAT CHANGED ON 2026-09-15, FIRST ROUND, AND WHY (third Opus verdict,
  URTEIL-OPUS-2026-09-15.md):
  * P1 -- an unsatisfiable lock invariant (`invariant false`) emptied (b): every body
    obligation quantifies `∀ U, HavocOk S U → …`, and `HavocOk` had no member. It also
    emptied the conclusion: the old premise `StartZulaessig` demanded every invariant at the
    start memory, so no start was admissible. Its fields `req` and `sperren` belonged to no
    premise group. Now they are the user's `StartPflicht`, over the memory and arguments the
    PROGRAM declares. An unsatisfiable family refutes (b) (`unerfuellbar_widerlegt`,
    `probeA_falsch_inv_nicht`), `HavocOk` is inhabited under (b) (`havocOk_bewohnt`), and
    every (b)-refutation of the probes holds with no side condition on the family.
  * P2 -- `ws`, `S`, `Q` were free parameters: `akP3` (two writers) was refused with its real
    starts and accepted with `ws = []`. They are now fields of `E`; the checker runs on
    `E.ws`, the hardware assumption names `E.Q`, and (d) lets a thread run only a declared
    start (`laufzeit_nur_erklaert`). No accepted program over `akD` runs both writers
    (`akD_kein_zweiter_schreiber`); the same code declaring no start is a different program,
    about the root alone (`akP3_ohne_starts`). The checker also demands distinct starts
    (`AkzeptiertSpec.einzeln`), so the runtime's exact start is covered (`laufzeit_voll`).
  * P3 -- publish payloads were dropped from the race leg with nothing in their place; two
    starts WRITING one unguarded payload passed. The exemption is gone from `RennfreiBis`
    and from the checker's `renn`: only `atomic` globals are exempt. Why no pairing conjunct
    is needed: a payload read by one start and written by another is already refused by the
    footprint check (`fuss`: an unguarded footprint carrier must be thread-local), and a
    guarded payload is lock-ordered like any carrier. What remains exempt is exactly what
    A10 orders: accesses to `atomic` globals. The price, NAMED: the publish/await hand-off
    of an UNGUARDED payload across threads is refused, not covered.
  * `StartZulaessig` is no longer a premise; the proof derives it (`startZulaessig_aus`,
    Zielsatz/Beweis.lean). The old `NutzerPflicht P S Q` is now `LogikPflicht`.

  THE ONE ASSUMPTION LIST -- everything the theorem assumes that is neither the checker's
  Bool nor the user's proof. Each entry with why it is hardware/runtime and not a software
  obligation under that name:
  * (c) `GutO O` -- an axiom (a FOREIGN body: `extern fn`, `prim fn`, `asm`, `entry`,
    `entrust`) writes only its declared frame, keeps the held locks, and leaves its accesses
    in the trace. Foreign code is not Gabbro code: nothing in the language can check it, and
    the user's logic never sees its body.
  * (c) `RegLokal O` -- a register read answers from the state of its device, i.e. from the
    carriers declared for it (`depends`, `D.rtraeger`); `awaits g` sees a publication
    depending only on `g`. It is about the device, not the program. NAMED RESTRICTION
    (third verdict, `register_ohne_traeger_konstant`, Zielsatz/Proben.lean): a register
    WITHOUT declared carriers answers the same value in EVERY world, and a user proof may use
    that two reads agree -- a real volatile register breaks that. So `RegLokal` is STRONGER
    than hardware: a register whose value the device changes on its own must be read through
    an axiom (whose answer is free under `GutO`) or given carriers an axiom writes. Not
    repaired here: G's oracle answers a read from the world alone, and the replay linking the
    user's sequential proof to G (`regLies_gleich`) needs the answer to be a function of the
    carriers the two worlds share.
  * (c) `AxVertragO E.Q O` -- every axiom answer THAT FITS ITS DECLARED RESULT TYPE meets
    the `ensures` the program declares for it. That is the contract of foreign code or a
    device, which the user writes and nothing checks: a false `E.Q` is a false NAMED
    assumption (visible in the declaration). CORRECTED 2026-09-15 (verdict): `Q := false`
    makes (c) unsatisfiable only for an axiom WITHOUT a result; for an axiom with a result,
    (c) stays inhabited by oracles whose answers never fit the type, and every call of that
    axiom then stops at a `hardware` stop (`Hardware.annahme`). Both are the honest kind of
    vacuity -- a visible false assumption, reported as such -- but they are two kinds.
    SINCE G1 (2026-09-15) "fits" is a real decoding for EVERY type (`einpassen_voll`): for an
    `E.Q` satisfiable at a DECODABLE value (for a float: a well-formed one, `WertOk`; a `Q`
    true only at malformed bit triples is again a false declaration), oracles with fitting
    answers exist, and (b) must cover them. SINCE W1 the checker admits no answer site at an
    empty type except an axiom `-> never`, so every other site's class has such values.
  * (d) `Laufzeit.lader` -- the loader establishes the program's declared initial memory
    `E.sp0` (initialized data and zeroed storage of the emitted C). A toolchain/loader fact;
    that `E.sp0` meets the lock invariants and start `requires` is the USER's `StartPflicht`.
  * (d) `Laufzeit.start`/`.einmal` -- the runtime starts exactly the declared starts, each on
    its own thread with its declared arguments, and the idle root `none` (MitRuhe.lean: body
    `return`, empty signature, no lock, no reason, writes nothing) on every other thread;
    the statement covers every assignment running some of the declared starts this way, and
    (since fix lane F10) any number of threads running a routine the program declares at
    least twice (a worker pool; the runtime's own start runs one thread per occurrence).
    Thread creation is the runtime's (the emitted `main`/boot code), not user logic. The
    machine runs `E.P.mitRuhe`, whose `some f` IS `f` of `E.P`: every checker fact transfers
    (`akzeptiertSpec_mitRuhe`, `akzeptiert_mitRuhe`) and every function behaves as in `E.P`
    (MitRuheSemantik.lean).
  * (d) since 2026-09-26, THREADS CREATED AT RUN TIME -- `Laufzeit.start` also places thread
    slots at the run-time roots `E.gestartet`; a slot the run does not start live is DORMANT in
    the thread machine until a `start` or `child` step spawns it. Assumed, and not a software
    obligation under that name: (1) the slot's ARGUMENTS are the unit's (for a `start` root
    `.nil`, `N458`) and its frame's ghost entry world (`s0` and the logged entry, read by
    `old`-parts of the root's `ensures` and by `VertragAmOrtG`'s `requires` leg) is the START
    world, not the spawn world -- the body itself reads shared memory at each step, so what it
    DOES is the spawned thread's behaviour; (2) the spawn SITES are the checked ones: the
    lowering creates the threads of a `start` only where the starter holds no lock (`N461`
    checks the source, the `start` rule carries it as a side condition), makes the starter wait
    until EVERY root has finished (the `join` rule), and enters a `child` region by jump with
    an empty held set (`N456`; OFFEN O21's jump assumption); and (3) every spawn SUCCEEDS: the
    `start`/`kind` steps have no failure branch, and a unit that spawns in a loop needs
    unboundedly many slots (`Faden` is unbounded) -- thread creation failing for want of memory,
    stacks or thread ids is not modelled (review 2026-09-26). All three are statements about the
    runtime and the lowering (lane 260's raw `clone`), whose check is translation validation's.
    Over-approximated, never under-: a spawn may fire at ANY point of a live thread where the
    rule's condition holds, and any slot may be live from the start (`lebt0` is quantified).
  * THE PERMITTED STOPS (`HaltArt`, in the conclusion `FortschrittG`): not premises, but
    the places where the theorem reports instead of claiming more. Each with why it is not
    the user's logic:
    - `hardware`, axiom answer outside its type (`dannBindAxiom`, an axiom leaf;
      `Hardware.annahme`) -- the answer of FOREIGN code, which (c) describes only by its
      frame (`GutO`) and its declared `ensures` (`AxVertragO`); a type-correct answer is
      constrained, an ill-typed one is the foreign code breaking its declaration. Only for
      an ANSWERABLE type (`¬ AntwortLeer`, since G1): the type has values, each of them some
      raw word under some image (`einpassen_voll`), so the machine could have answered.
    - `hardware`, register answer outside its type (`dannRegLies*`; `Hardware.register`) --
      the device answered a bit pattern its declared type excludes (answerable types only,
      as above).
    - `nieZurueck` (since G1; narrowed by W1), a call of an axiom whose declared result is
      `never` -- the call does not return. That is the declaration's promise about the
      foreign code (the C prototype is `_Noreturn`; a foreign body that returns breaks it, a
      hardware/foreign fact like every entry of (c)). The continuation is unreachable in the
      C as in G; everything before the call is covered by (b). Every OTHER empty answer type
      (`.grund 0`, an empty range, a sum without a value, a pointer type no function of the
      program has), at an axiom or at a register, is REFUSED by the checker
      (`AkzeptiertSpec.antworten`, W1): its C call would return into a continuation nothing
      covers, so it is not named here but excluded, and no reachable thread stands at one.
    - `hardware`, register answer against its declared promise (`regLies` of a `requires`
      without `else`; `Hardware.geraet`) -- the device broke the promise its declaration
      makes (`D.rzusage`). A promise the user declares `false` makes every read a stop: the
      same honest vacuity as `Q := false`, visible in the declaration.
    - `flagge`, an `awaits g` whose flag is not visible (`dannAwaits`) -- a WAIT, not a
      failure: G tests visibility once where the C spins. It covers three cases G does not
      separate: not yet published (a wait whose end is liveness, not claimed), published
      but not visible (A10 fails: the hardware part), and NEVER published (the program's
      own pairing, verdict F3). Why the last is not made a checker or user obligation: (d)
      covers runs with ANY SUBSET of the declared starts, so on a covered run the publisher
      need not run at all, and no static pairing check can exclude the permanent wait; and
      G has no "later" in which a publication could arrive -- whether it does is a liveness
      fact, like the end of a lock wait, and the statement claims no liveness. So it is
      reported, as a wait, and named here.
    - `budget`, a spent `forever` budget (`.ewig _ 0`) -- a MODEL ARTEFACT, not hardware:
      G unrolls `forever` at most `passes` times, and `GabbroZiel` quantifies every
      `passes`, so every finite prefix of the C's endless loop is a run of a larger budget.
      A thread at this stop is one the C keeps running.
    - GONE (verdict F1): `ieee`, a float result outside its range. It is `Logik.bereich`,
      excluded by (b), and `FortschrittG` has no such stop.
    NAMED NEXT TO PROGRESS: a thread at ANY of these stops while it holds a lock `L` leaves
    every thread that needs `L` waiting forever -- `WartetG` then holds for them at every
    later machine, and every leg of `Ziel` still holds. Progress is "every stop is named",
    not "every wait ends"; the waiting bound (Lebendigkeit.lean) assumes no such stop inside
    a critical section (`HardwareImAbschnitt`), and is not in `Ziel`.
  * Not premises, but assumptions of the reading: machine G is the meaning of the C
    (translation validation, PLAN-UEBERSETZUNGSVALIDIERUNG); the hardware is DRF-SC.

  WHAT `Ziel` ADDS OVER `NutzerPflicht` (leg by leg). The user proves SEQUENTIAL per-function
  facts: each body, run alone by `execEndH` against every callee answer meeting the callee's
  contract and frame, every register/axiom answer in the (c) class, and every lock move
  keeping the invariant, ends in its `ensures` and owed invariants, meets each callee's
  `requires`, and never ends in `logik`; plus the start obligation. `Ziel` speaks about the
  INTERLEAVED machine G:
  * `speicherSicher` (`SpurInv`) -- NOT in (b) at all: every access in every run carries its
    carrier's guards and those locks are really held. CORRECTED 2026-09-15 (verdict): it
    needs NO checker and no user proof -- `spurInv_erreichbar` uses only `GutO`, so it holds
    for EVERY well-typed program of G: carried by the intrinsic typing of `Programm D`
    (bounds are `.index n` types, pointers are declared tables, no heap). That is literally
    "by the language", but for Lean terms: its force for a `.gab` file rests on the
    `.gab -> Programm D` step (the exporter). Stack depth is not covered.
  * `rennfrei` (`RennfreiBis`) -- NOT in (b): cross-thread access pairs with a write are
    lock-ordered, or do not exist. From the checker and G.
  * `vertrag`, `invRueck`, `invGrund`, `keinLogikHalt`, `startEnde`, `keinStartGrund` --
    these ARE (b)'s sequential clauses, restated at the places of G's log. What the theorem
    adds is that they survive interleaving and are G's behaviour, not only `execEndH`'s: the
    other threads interfere only through lock moves of the `HavocOk` class and through
    carriers the checker proved thread-local. For a single-threaded program without locks
    these legs are (nearly) a restatement of (b), transported to G by the replay.
  * `sperrInv` (`SperrInvG`) -- NEW: every lock no thread holds has its invariant IN SHARED
    MEMORY at every reached machine. (b) only checks the invariant at each release of one
    body; the global cross-thread fact is the theorem's.
  * `keineVerklemmung`, `keinZyklus`, `fortschritt` -- NOT in (b): no global deadlock, and
    (since 2026-09-15, F2) no wait CYCLE among any threads, both from lock ranks; and G
    never stops silently: every thread is finished, waits for a lock, waits for a
    publication, has spent its `forever` budget, stands at a hardware stop, or can step.
    Since F1 the user's own code has no stop of its own in that list: a failing loop
    invariant, `state` pre-state or float range is excluded (`keinLogikHalt`, `BereichG`).
    So the safety legs cannot be made vacuous by a stop the USER's code decides; they can
    by a stop of the list above (hardware, a wait, the budget) -- each named.
  * `keinKernHalt` (`KernHaltG`) -- NOT in (b), and not in (a) either: on a run that a core
    schedule admits (`KernPlan`: masking works, and a handler runs to completion on the core
    it preempted) a handler never stands at a lock a thread of its core holds. The program
    side -- every lock a handler's call graph takes is declared `masks irqs` -- is a HYPOTHESIS
    of the leg, because the unit does not mark its handlers (fix lane F11, OFFEN O19). It is
    the model counterpart of the Rust `H102`, and it holds for every program of G.
  * `zeit` (`ZeitAb`) -- NOT in (b), and WEAK: a bound on a frame's OWN G-steps by the
    syntax-computed `kostenTief`, for frames with a finite call tree only (`rufTief`). It
    holds for EVERY program of G with no premise (`frame_schritte_beschraenkt`), so it says
    nothing about waiting, recursion, indirect calls or a `forever` loop; not the declared
    `costs`.

  REVIEW PACKAGE -- every model definition used, file:line, what it says / if it were wrong.
  Machine G and the sequential semantics (review question 4):
  * `RufMaschineG` RufMaschineG:151 -- shared memory, per thread a frame stack, trace, call log
    / a field G lacks is a behaviour no conjunct can speak of.
  * `RufSchrittG` RufMaschineG:246 -- the 70 rules, one thread per step, rules fire only on
    success outcomes / a rule G has and C lacks (or vice versa) makes every leg about another program.
  * `RufStartG` :2093, `RufErreichbarG` :2110 -- every thread in its start frame holding its
    signature locks; reachable = finitely many steps / a start C does not make is irrelevant.
  * `execStmt` Semantik:669, `keinRuf` Maschine:383, `Stmt.istBlatt` Maschine:392 -- one
    statement sequentially; leaves are what G runs in one step / wrong leaves = wrong steps.
  * `Logik`/`Hardware` Semantik:277/296 -- the failure outcomes; `Logik.bereich` (a float
    result outside its range, since 2026-09-15) / a user-decided failure filed as
    `Hardware` would pass (b) unconstrained (verdict F1).
  * `einpassen` Semantik:425 (`summePasst`, `gleitWortPasst`, `zeigerPasst` above it),
    `AntwortLeer` :447, `Orakel.zeiger` :451 -- a raw answer held against the declared type,
    and the loaded image / a type the decoding refused for every word would be a stop the
    model decides and files as hardware (finding G1); `einpassen_voll`, `antwortLeer_iff`
    (EinpassenVoll.lean) say it refuses exactly the values the type lacks.
  * `execEndH` SperreSem:363, `HavocOk` :71, `SperrInv` :45 -- the sequential body semantics the
    user proves against: `locks L` runs from any move keeping `S.inv L`, a release checks it /
    if it differs from `execStmt` outside `locks`, the user proves the wrong body.
  * `World` Semantik:79 (slots total over `Int`; in-range is the TYPE of `.index` values),
    `Speicher` Maschine:359, `Orakel` Semantik:451, `Faden` Wettlauf:46 (= Nat, all started).
  * `Deklaration.mitRuhe`, `Programm.mitRuhe`, `Orakel.mitRuhe`, `SperrInv.mitRuhe`, `fsRuhe`,
    `wsRuhe`, `speicherR` :268, `envR` :280 MitRuhe.lean -- the idle root added, signature
    numbers and function-pointer types shifted by one, every body translated constructor by
    constructor, memory and arguments carried over / a translation that changed a body would
    make every leg speak about another program.
  The thread machine (since 2026-09-26):
  * `FadenMaschine`/`FadenSchritt`/`FadenErreichbar`/`FadenStart` FadenMaschine.lean -- a G
    machine plus live set, join lists and ghost rank/clock; steps `lauf` (a G step of a live,
    non-joining thread), `start` (spawn a list of dormant slots and wait, only holding no lock),
    `kind` (spawn one slot, go on), `join` (end the wait once every root is finished) / a spawn
    that moved the G state, or a join that fired early, would make the legs speak about
    another run; `fadenErreichbar_G` and `fadenErreichbar_von_G` are the two bridges.
  Premise definitions:
  * `Einheit`, `Einheit.ws` (here) -- the program as one declaration / a field the exporter
    does not fill from the source would make the statement about another program.
  * `Block.ants`, `StelleOk` AntwortOrte.lean -- the answer sites of a body (axiom calls,
    register reads) and when one is admissible (an axiom `-> never`, or a non-empty answer
    type) / a site the collector missed could stand at an empty type unrefused (W1).
  * `GutO` Satz:965 -- axioms stay in their declared write frames, keep held locks and trace.
  * `RegLokal` ZielOrtGeraetSem:48 -- register/visibility answers depend only on declared carriers.
  * `AxVertragO`/`AxEnsLokal`/`AxEns` AxiomVertrag:50/56/44 -- axiom answers meet the declared
    `ensures`; the declared ensures reads only the axiom's write carriers.
  * `KoerperGutS` SperreFuss:374 -- per function, sequential: triple, caller duty, no `logik`
    outcome (since 2026-09-15 that includes `logik bereich`, a float out of range), against every frame-respecting handler (`RespektiertRahmen` ZielOrtRahmenSem:48,
    `OhneVorbedingung` ZielOrt:87, `OhneLogik` ZielOrtGanz:51), oracle (`RahmenO`
    ZielOrtVollBeweis:48) and move / an empty handler/oracle/move class empties it (probe A/D;
    the move class is inhabited under (b) since 2026-09-15, `havocOk_bewohnt`).
  * `InvGutS`/`InvAmRueck`/`InvHaelt` ZielOrtInv:54/46/41 -- owed invariants at a value return.
  * `ReqAmEintritt`/`EnsAmRueck` VertragOrtB:114/120, `StartGut` ZielOrt:113.
  * `programmImFragmentG` ZielOrtGeraetSem:502, `fussOrteG` :450, `FussS` SperreFuss:140,
    `AbgK` ZielOrtMehrfaden:107, `reachB` :146, `StufenM` Verklemmung:552, `Bewacht`
    InterferenzAllgemein:1350, `TraegerSchreibt` :123 -- the checker's program facts.
  Conclusion definitions:
  * `SpurInv` RennfreiVoll:249 (`Ereignis.gut` Satz:263, `Konsistent` :279) -- every recorded
    access carries its carrier's guards (locks AND marks) in `Λ`, whose locks are really held.
  * `LaufG`/`ZugriffG`/`SchreibG`/`GeordnetG` RennfreiVoll:485/333/337/563 -- runs by index;
    an access = recorded event or memory change; ordered = release by one, acquire by the other.
    `AtomarAusgenommen` InterferenzAllgemein:609.
  * `VertragAmOrtG` ZielOrt:67 -- requires at every logged entry, ensures at every logged return.
  * `SperrInvG` SperreMaschine:424 -- every lock no thread holds has its invariant in memory.
  * `InvAmOrtG` ZielOrtInv:66; `StartEndeG` ZielOrtStart:70 (`RetKopf` :59); `KeinStartGrundG`
    :191; `KeinLogikHaltG`/`PrueftG` ZielOrtGanz:658/622 -- no thread stuck at a loop invariant
    or transition test. `FertigG`/`WartetG`/`AnSperre` Verklemmung:746/751/652.
    `BereichG` Fortschritt.lean -- the float range checks pass at every head (proof side,
    not in `Ziel`: `FortschrittG` lists no float stop, so it follows from `fortschritt`).
  * `Eintritt`/`SegLauf`/`aktivVor`/`segZaehle`/`kostenTief`/`rufTief` KostenG:788/740/776/750/955/964.
  NEW here: `Einheit`, `LogikPflicht`, `StartPflicht`, `Laufzeit` (2026-09-15); `HaltArt`,
  `KopfHalt`, `RestHalt`, `WartetAuf`, `KeinWarteZyklus` (2026-09-15, verdicts F2/F3);
  `InvGutGrund`, `InvAmGrundG` (invariants at REASON exits), `HaltBenannt` (the named
  stops, by kind), `RennfreiBis`
  (DRF for every non-atomic carrier), `Getrennt`, `SchreibGetrennt` (write separation of
  unguarded carriers, the counterpart of `H013`; with it `rennfreiBis_of`, Akzeptiert.lean,
  proves `RennfreiBis`), `Ruhig` (an idle start writes NOTHING), `AkzeptiertSpec`,
  `StartZulaessig` (derived, not a premise), `Ziel`, `GabbroZiel`; `Mehrfach` (a routine
  declared at least twice, fix lane F10) with `PoolSicher`/`PoolSicherW`/`EinzelnPool` (lane
  245, a premise since F10); `KernPlan` and the leg `KernHaltG` (one core with interrupt
  handlers, fix lane F11, proved in Zielsatz/Masken.lean); `Einheit.gestartet`, `JoinWartet`,
  `WartetF`, `KeinWarteZyklusF`, `FortschrittF`, `ZielF` and the thread machine (threads
  created at run time, 2026-09-26; legs proved in Zielsatz/Faeden.lean).

  REVIEW QUESTIONS. 1. Does `Ziel` say the four legs, nothing weaker (see WHAT `Ziel` ADDS)?
  2. Is every premise in exactly one group? The start conditions are (b) (`StartPflicht`)
  and (d) (`Laufzeit`) since 2026-09-15; nothing else restricts the quantified runs.
  3. Can a user-controlled choice empty an obligation? Probes A/D: closed by `NutzerPflicht`
  at every budget. Probe F1 (an out-of-range float, the one stop the user's code decided
  for every oracle): closed, `logik bereich` (`probeF1_widerlegt_gilt`). An unsatisfiable lock family or start `requires`: closed, it refutes (b)
  (`unerfuellbar_widerlegt`, `start_req_widerlegt`). An empty answer type other than `never`
  (W1): closed, the checker refuses it (`w1_abgelehnt`). The run class is never empty: the root
  on every thread from `E.sp0` meets (d) (`laufzeit_ruhe`). What stays in the user's hand,
  honestly: `E.starts = []` (the program runs nothing; the statement is then about the root,
  `laufzeit_ohne_starts`), and `E.Q` unsatisfiable (a false named hardware assumption, (c)
  empty). 4. Does G run what the language means (translation validation takes over for the C)?

  NOT CLAIMED (PLAN §6): termination and a waiting bound under fairness (`zeit` bounds only
  frames with a finite call tree, `rufTief`); stack depth (G's stacks are unbounded and
  recursion is admitted, so a non-returning recursive function meets any `ensures` while the
  emitted C overflows); the C and the hardware; weak memory beyond DRF-SC (G is sequentially
  consistent; `atomic` globals are ordered by A10, not by locks, and are excluded from
  `rennfrei`); the publish/await hand-off of an unguarded payload (refused by the checker,
  see P3); floats only as the kernel IEEE model of GLEITKOMMA §7 (no float assumption on G's
  side -- true since F1: an out-of-range result is the user's `logik bereich`, not a
  hardware stop; `gleitkomma_ieee` is on the C side); starvation freedom; invariants at entry or while
  locks are held (claimed at returns only); WHICH threads are interrupt handlers and which
  core they share -- the `entry … via idt` dispatch fact is not in `Einheit` and G has no
  cores, so `keinKernHalt` takes them (and the masking discipline `H102` checks) as its own
  hypotheses instead of reading them from (a)/(d), and the emitted C realises no masking at
  all (no `cli`/`sti`; `beispiele/59` says so in its header) -- OFFEN O19; a busy routine declared ONCE on several threads
  (outside (d); a routine declared twice may run on any number of threads since fix lane F10,
  and the checker admits that only pool-safe, `EinzelnPool`); linking of separately compiled units
  (PLAN-ZIELSATZ §10: the statement is about ONE `Einheit`, and a function another unit
  supplies is not in `D.Fn`); for threads SPAWNED at run time (claimed since 2026-09-26, see
  (d) above): a root whose ARGUMENTS differ per spawn (a `child` region reading its handed
  values -- the model fixes one argument list per slot), a root `requires` that holds only at
  the SPAWN world (it is (b)'s duty at `E.sp0`), `old`-reads of a root's `ensures` at the spawn
  world, the END of a join wait (a root that never finishes keeps its starter waiting, a named
  `JoinWartet` stop, like a lock wait), the child's handed STACK (G is address-free), a spawn
  that FAILS (thread creation out of resources: the model's spawn always succeeds), and the
  C side of the spawn (lane 260's lowering: translation validation) -- OFFEN O21/O22. The
  exporter carries `start` (roots into `gestartet`); a `child` needs a stack gate, a foreign
  body the exporter does not build (`Ax := Empty`), so no `child` program is exported. Declared
  `costs` are not in
  `Deklaration`: `zeit` is the syntax-computed bound. The `.gab` -> `Einheit` step is the
  exporter's (lean_g.rs). Since lane 198 it fills `starts`, `sp0`, `S` and the source
  `requires` of the unit `gE` for the fragment it exports (pinned by the test
  `einheit_width_travels_together`); everything outside that fragment is refused by name
  (`LG001`-`LG007`), and a program there reaches `GabbroZiel` only by a hand-written term.
  The exporter itself is not verified: that `gE` is the source program is the job of the
  translation-validation chain, not of this statement.

  FINDINGS (definitions in proof files, imported anyway): there is no definition-only layer.
  All imports are mixed files; the goal predicates live in flagship proof files
  (ZielOrt, ZielOrtGanz, ZielOrtInv, ZielOrtStart, ZielOrtMehrfaden, SperreFuss,
  SperreMaschine, Verklemmung, RennfreiVoll, KostenG); the closure includes WITNESS files
  (AxiomVertrag imports ZielOrtVollZeuge, RennfreiG imports ZielOrtZeuge). To move: every
  definition listed above out of its proof file.
-/
import Grammatik.Verklemmung
import Grammatik.RennfreiVoll
import Grammatik.KostenG
import Grammatik.MitRuhe
import Grammatik.AntwortOrte
import Grammatik.FadenMaschine

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A complete enumeration: every element is in the list. -/
def Aufzaehlung (α : Type) : Type := {l : List α // ∀ a, a ∈ l}

/-! ## The program the user wrote -/

/-- **The program as ONE declaration** (2026-09-15, verdict P2): the code with its contracts
    (`P`: bodies, `requires`, `ensures`, table invariants) AND what the source declares about
    its run, which before were free parameters of the statement:
    * `S` -- the lock invariants (`lock L protects { … } invariant I`);
    * `Q` -- the axioms' declared `ensures` (the content of the hardware assumption);
    * `starts` -- the declared thread starts with their arguments (`concurrent { … }`,
      `entry`/`boot` dispatch roots);
    * `sp0` -- the declared initial memory (every table and global initializer);
    * `gestartet` (NEW 2026-09-26, Opus agent A, OFFEN O21/O22) -- the roots of threads the
      program creates AT RUN TIME: every root of a hosted `start { f, g };` and every
      `child { … }` region (lifted to a function), with its arguments (`N458`: a root takes
      none, so the exporter writes `.nil`). A root here runs on any number of threads (a `start`
      in a loop, in two starters, in a pool routine), so the checker judges it as a POOL
      routine: it enters `ws` TWICE (`Einheit.ws`). Default `[]`: a unit that creates no thread
      at run time is the unit of before.
    The exporter's output is exactly one such value; a different `starts` (say `[]`) is a
    DIFFERENT program, whose run the statement then describes (`laufzeit_nur_erklaert`). -/
structure Einheit (D : Deklaration) where
  P : Programm D
  S : SperrInv D
  Q : AxEns D
  starts : List (Σ w : D.Fn, Env D (D.params w))
  sp0 : Speicher D
  gestartet : List (Σ w : D.Fn, Env D (D.params w)) := []

/-- The thread roots the checker judges: the declared starts, and every run-time root TWICE
    (since 2026-09-26): a root the program may spawn is a pool routine (`Mehrfach`), so `einzeln`
    demands it pool-safe (the model side of `N462`/`N457`), `Getrennt` pairs it with itself and
    `Laufzeit.einmal` lets it run on any number of threads. For `gestartet = []` this is the list
    of before (`ws_ohne_gestartet`). -/
def Einheit.ws (E : Einheit D) : List D.Fn := (E.starts ++ E.gestartet ++ E.gestartet).map (·.1)

/-- **`w` is declared at least twice** (fix lane F10, 2026-09-22): two start OCCURRENCES of one
    routine, `concurrent { w, w }` -- a symmetric worker pool. The one notion of "twice" in
    this file: the checker's `einzeln` (pool safety), its thread-locality `Getrennt` (two
    occurrences are two threads) and the runtime's `Laufzeit.einmal` all read it. -/
def Mehrfach {α : Type} (ws : List α) (w : α) : Prop := List.Sublist [w, w] ws

/-! ## (a) What the checker decides -/

section Pruefer

variable [DecidableEq D.Fn]

/-- Carrier `c` is thread-local among the declared starts `ws`: no start reaches `c` in a
    footprint while a DIFFERENT start OCCURRENCE can write it (`GetrenntK` over the starts).
    Since fix lane F10 (2026-09-22) a routine declared twice (`Mehrfach`) is two threads, so
    it is paired with ITSELF too: its footprint carriers must not be written by its own graph
    unless a signature lock or a lock invariant covers them (`FussS`). On a repetition-free
    `ws` this is the old condition word for word (`Mehrfach` never holds there). -/
def Getrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, reachB P fs w₁ f = true →
    c ∈ fussOrteG P f → reachB P fs w₂ g = true → TraegerSchreibt g c = false

noncomputable def lokW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (Getrennt P fs ws c) (Classical.propDecidable _)

/-- Carrier `c` is WRITE-separated among the declared starts `ws`: if one start's call graph
    may write `c`, no DIFFERENT start's graph may write it or have it in a footprint. -/
def SchreibGetrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, reachB P fs w₁ g = true → TraegerSchreibt g c = true →
    ∀ h, reachB P fs w₂ h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **Pool-safe**: routine `w` may run on any number of threads. It starts
    like any admitted start (no signature-held lock, no reasons), and every
    carrier some function of the thread graph `K` may write is guarded by a
    lock or atomic. Reads need nothing for the RACE leg: with no unguarded
    writer, two threads reading one carrier do not race; the footprint leg
    (a carrier read in a footprint that the other instance may write) is
    `Getrennt`'s, which pairs a routine declared twice with itself. (Lane
    245: the model side of the narrowed `N304`.) -/
def PoolSicher (D : Deklaration) (K : D.Fn → Bool) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧
    ∀ f, K f = true → ∀ c, TraegerSchreibt f c = true →
      (∃ L, Bewacht c L) ∨ AtomarAusgenommen c

/-- **Pool-safe at its computed graph**: `PoolSicher` with the thread
    graph `reachB P fs w`. -/
def PoolSicherW (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  PoolSicher D (reachB P fs w) w

/-- **Duplicates allowed iff pool-safe**: every routine declared at least
    twice is pool-safe at its computed graph. `ws.Nodup` implies it
    vacuously (`einzelnPool_of_nodup`, PoolSym.lean); the symmetric pair
    `[w, w]` satisfies it exactly for pool-safe `w` (`einzelnPool_paar`).
    The checker's `N304` decides it for same-routine pairs. Since fix lane
    F10 (2026-09-22) this is the field `einzeln` of `AkzeptiertSpec`. -/
def EinzelnPool (P : Programm D) (fs : List D.Fn) (ws : List D.Fn) : Prop :=
  ∀ w, Mehrfach ws w → PoolSicherW P fs w

/-- **What `Akzeptiert` must establish** (the Props of its components): fragment; closed call
    graphs; every footprint carrier signature-guarded, lock-protected or thread-local; lock
    floors; protected carriers guarded by their lock; declared starts hold no lock by
    signature and have no reasons, and a start declared twice is pool-safe (`EinzelnPool`,
    since fix lane F10 -- before: pairwise distinct, `ws.Nodup`); every carrier without a guard
    lock that is not `atomic` is write-separated among the declared starts (the counterpart
    of the checker's `H013`; publish payloads INCLUDED since 2026-09-15, verdict P3); no body
    calls an axiom or reads a register at a declared answer type without a value, except an
    axiom whose result is `never` (`antworten`, since 2026-09-15, W1). -/
structure AkzeptiertSpec (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (lokW P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : EinzelnPool P fs ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x

end Pruefer

/-- **The checker interface.** `akzeptiert E fs ls cs` is the Bool the Rust checker computes
    on the program `E` (member lists of functions, locks, carriers); `korrekt` is its
    soundness, the one link between the Bool and what the statement uses. -/
structure Pruefer where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpec E.P E.S fs.1 E.ws

/-! ## (b) What the user proves -/

/-- Owed invariants at a REASON exit (the twin of `InvGutS`; SYNTAX.md: "owes `I` at every
    `return`"). -/
def InvGutGrund (P : Programm D) (passes : Nat) (Q : AxEns D) (S : SperrInv D) (f : D.Fn) :
    Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' → ∀ U : Umwelt D, HavocOk S U →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneVorbedingung R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ (σ' : World D) (r : Fin (D.gruende f)),
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = EndAusgang.grund σ' r →
            InvAmRueck P f σ'

/-- A lock invariant reads only its protected carriers (second half of `SperrInvOk`). -/
def SperrInvLokal (S : SperrInv D) : Prop :=
  ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s'

/-- **The logic of the bodies**: per function and at EVERY `forever` budget the body triple
    with caller duty and no `logik` outcome, owed invariants at value AND reason exits; the
    lock invariants and declared axiom ensures the user wrote read only their carriers.
    (Until 2026-09-14 this was all of `NutzerPflicht`.) -/
def LogikPflicht (P : Programm D) (S : SperrInv D) (Q : AxEns D) : Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutS P passes Q S f ∧ InvGutS P passes Q S f ∧ InvGutGrund P passes Q S f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q

/-- **The start obligation** (NEW 2026-09-15, verdict P1): at the program's DECLARED initial
    memory every lock invariant holds, and every declared start's `requires` holds with its
    declared arguments. Before, these two were conditions on the quantified start
    (`StartZulaessig.sperren`/`.req`) that belonged to no premise group: an unsatisfiable
    family (`invariant false`) emptied both the body obligations (`HavocOk` had no member) and
    the conclusion (no start was admissible). Now such a family refutes (b)
    (`probeA_falsch_inv_nicht`, Zielsatz/Proben.lean). -/
structure StartPflicht (E : Einheit D) : Prop where
  sperren : ∀ L, E.S.inv L E.sp0 = true
  req : ∀ a ∈ E.starts ++ E.gestartet, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2

/-- **The user's own logic**: the bodies' logic and the start obligation, both over the
    program `E` -- nothing the prover picks. -/
structure NutzerPflicht (E : Einheit D) : Prop where
  logik : LogikPflicht E.P E.S E.Q
  start : StartPflicht E

/-! ## (c) What the hardware is assumed to do -/

def HardwareAnnahmen (O : Orakel D) (Q : AxEns D) : Prop :=
  GutO O ∧ RegLokal O ∧ AxVertragO Q O

/-! ## (d) What the runtime is assumed to do (A4) -/

/-- **Assumption A4, the loader and the runtime's thread creation.** The machine runs
    `E.P.mitRuhe` (the program with the runtime's idle root `none`, MitRuhe.lean) from
    * `lader` -- the loader establishes the program's DECLARED initial memory `E.sp0`;
    * `start` -- every thread runs the idle root or ONE declared start with its DECLARED
      arguments;
    * `einmal` -- a declared start runs on two threads only if the program declares it at
      least twice (`Mehrfach`, a worker pool; fix lane F10, 2026-09-22 -- before: never).
    The runtime starts EXACTLY the declared starts, each on its own thread, the root on every
    other thread (`initRuhe E.starts`); that start meets this predicate whenever the checker
    accepts (`laufzeit_initRuhe`, Zielsatz/Proben.lean), and so does every assignment running
    only some of the declared starts. -/
structure Laufzeit (E : Einheit D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) : Prop where
  lader : sp = speicherR E.sp0
  start : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts ++ E.gestartet, init t = ⟨some a.1, envR a.2⟩
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 →
    (init t).1 = none ∨ ∃ w, (init t).1 = some w ∧ Mehrfach E.ws w

/-! ## The start the proof works with (derived from (b) and (d), not a premise) -/

section Start

variable [DecidableEq D.Fn]

/-- An idle start: no signature lock, no reasons, every function it reaches has an empty
    footprint and writes nothing. Any number of threads may run it. -/
def Ruhig (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, reachB P fs w f = true →
    fussOrteG P f = [] ∧ ∀ c, TraegerSchreibt f c = false

/-- **Admissible starts** (the proof's notion; NOT a premise of `GabbroZiel` since
    2026-09-15): every thread runs a declared start or an idle one; a start on two threads is
    idle or declared twice (`Mehrfach`, since fix lane F10); the start functions' `requires`
    and every lock invariant hold at the start memory.
    `startZulaessig_aus` (Zielsatz/Beweis.lean) derives it from (b) and (d). -/
structure StartZulaessig (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  wurzel : ∀ t, (init t).1 ∈ ws ∨ Ruhig P fs (init t).1
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → Ruhig P fs (init t).1 ∨ Mehrfach ws (init t).1
  req : StartGut P sp init
  sperren : ∀ L, S.inv L sp = true

end Start

/-! ## The legs of the goal -/

/-- **Data-race freedom on every run from `M0` to `M`**: two accesses by different threads to
    ONE carrier, one a write, the carrier not `atomic`, are ordered through a guard lock
    (release by the first, acquire by the second). Unguarded carriers included: there such a
    pair must not exist. Publish payloads included (2026-09-15, verdict P3). -/
def RennfreiBis (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufG P O passes M0 ms fs n → ms n = M →
    ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → fs i ≠ fs j →
      ZugriffG (ms i) (ms (i + 1)) (fs i) c → ZugriffG (ms j) (ms (j + 1)) (fs j) c →
      (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) →
      ¬ AtomarAusgenommen c →
      ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j

/-- At every logged REASON return, every invariant the function owes holds. -/
def InvAmGrundG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (ev : RufEreignisF D), ev ∈ (M.faeden t).log →
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      ev = RufEreignisF.grund g rho r s0 s1 → InvAmRueck P g s1

/-- **The kinds of named stop** (2026-09-15, verdicts F1 and F3, finding G1). Each is a place
    where G has no rule for a thread and the statement reports it instead of claiming more:
    * `hardware` -- a hardware assumption of (c) fails at the head: an axiom (foreign code)
      answered outside its (answerable) type, a register (a device) outside its type or
      against the promise its declaration makes;
    * `nieZurueck` -- the head calls an axiom whose declared result is `never`: the call does
      not return;
    * `flagge` -- a WAIT for a publication: the head is `awaits g` and `g` is not visible;
    * `budget` -- the `forever` budget is spent: G's finite stand-in for a loop the C runs
      without end.
    An out-of-range float is NOT a stop any more: it is `Logik.bereich`, excluded by the
    user's obligation, and no reachable machine stands at one (verdict F1). -/
inductive HaltArt where
  | hardware
  | flagge
  | budget
  /-- The head is a call of an axiom whose DECLARED result is `never` -- the call does not
      return. That is the declaration's promise (the emitter writes `_Noreturn` on the
      prototype), and the code after the call is unreachable in the C as in G; the
      obligation (b) still covers everything before the call. NEW 2026-09-15 (round-5
      finding G1): before, this stop was filed as `hardware`, as if the machine had answered
      outside a type that has no inside. NARROWED 2026-09-15 (round-6 finding W1): every
      other empty answer type (`.grund 0`, an empty range, a sum without a value, a pointer
      type no function has, at an axiom or a register) is refused by the checker
      (`AkzeptiertSpec.antworten`), because there the C call returns. -/
  | nieZurueck

/-- The first layer of the head block is a named stop of kind `k` at the world `σ`: the
    failing side conditions of `dannBlatt` (a leaf's hardware outcome), `dannBindAxiom`,
    `dannRegLies*` (`hardware` for an answerable type, since G1), an axiom `-> never`
    (`nieZurueck`, since W1 the only empty type the checker admits) and `dannAwaits`
    (`flagge`). -/
def KopfHalt (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (σ : World D) (ρ : Env D Γ) : HaltArt → Block D V l Γ Λ Λ' → Prop
  | .hardware, .cons s _ => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .hardware, .bindAxiom a args .. =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none ∧
      ¬ AntwortLeer D (D.aerg a)
  | .hardware, .regLies r .. =>
      (∀ v, einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v → D.rzusage r v = false) ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .hardware, .regLiesElse r .. =>
      einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r σ) = none ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .nieZurueck, .bindAxiom a .. => D.aerg a = some .never
  | .flagge, .awaits g .. => O.sichtbar g σ = false
  | _, _ => False

/-- A residue at a named stop of kind `k`: a spent `forever` budget (`budget`), a leaf's
    hardware outcome at the end block's head (`hardware`), or its head block's first layer. -/
def RestHalt (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (σ : World D) (ρ : Env D Γ) : HaltArt → GRest D V l Γ Λ → Prop
  | .budget, .ewig _ 0 _ _ _ => True
  | .hardware, .ende (.cons s _) =>
      s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | k, .dann b _ => KopfHalt O passes σ ρ k b
  | _, _ => False

/-- Thread `t` stands at a named stop of kind `k`. -/
def HaltBenannt (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (k : HaltArt) (t : Faden) :
    Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ ∧ RestHalt O passes (M.weltVon t) ρ k r

/-- **Every stop is named**: each thread is finished, waits for a lock another thread holds,
    waits for a publication, has spent its `forever` budget, stands at a hardware stop, stands
    at a call that does not return (an axiom `-> never`: G1, narrowed by W1), or can step. Nothing else: no thread ever stands at a failing `logik` check (`keinLogikHalt`) or
    at a float result outside its range. -/
def FortschrittG (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t, FertigG M t ∨ WartetG M t ∨ HaltBenannt O passes M .flagge t ∨
    HaltBenannt O passes M .budget t ∨ HaltBenannt O passes M .hardware t ∨
    HaltBenannt O passes M .nieZurueck t ∨ ∃ M', RufSchrittG P O passes M t M'

/-- Thread `t` stands at `locks L` while thread `u` holds `L`. -/
def WartetAuf (M : RufMaschineG D) (t u : Faden) (L : D.Lock) : Prop :=
  AnSperre M t L ∧ L ∈ offen (M.faeden u).spur

/-- **No wait cycle** (verdict F2): there are no threads `t₀, …, tₙ₊₁` with `tₙ₊₁ = t₀` where
    each `tᵢ` stands at a lock that `tᵢ₊₁` holds -- whatever the OTHER threads do. (The global
    `keineVerklemmung` only rules out that EVERY unfinished thread waits.) -/
def KeinWarteZyklus (M : RufMaschineG D) : Prop :=
  ∀ (n : Nat) (ts : Nat → Faden) (Ls : Nat → D.Lock),
    (∀ i, i ≤ n → WartetAuf M (ts i) (ts (i + 1)) (Ls i)) → ts (n + 1) ≠ ts 0

/-- **The schedule of ONE core with interrupt handlers** (fix lane F11, 2026-09-22, OFFEN
    O19): the two hardware facts about `cli`/`sti` and about preemption, as conditions on a
    G run. `kern t` is the core thread `t` runs on, `H g` says `g` is an interrupt handler (an
    `entry … dispatch` root, which travels into the model as an ordinary start).
    * ENTRY ONLY WHEN UNMASKED: a handler takes its FIRST step only where no OTHER thread of
      its core holds a lock declared `masks irqs` (`D.maskiert`). That is what masking IS:
      while such a lock is held, interrupts are off on that core, so the handler is not
      entered there.
    * RUN TO COMPLETION: from that first step until the handler is finished, no other thread
      of its core steps. That is what preemption IS on one core: the handler displaces the
      thread it interrupted, and that thread continues only afterwards.
    The run-side twin of `MaskenOrdnung` (Unterbrechung.lean), which says the same over the
    event log `Lauf`; here over the machine-G run, so that `AnSperre` can be read. -/
def KernPlan (kern : Faden → Nat) (H : Faden → Prop) (ms : Nat → RufMaschineG D)
    (fs : Nat → Faden) (n : Nat) : Prop :=
  (∀ i, i < n → H (fs i) → (∀ k, k < i → fs k ≠ fs i) →
      ∀ (f : Faden) (L : D.Lock), f ≠ fs i → kern f = kern (fs i) →
        L ∈ offen ((ms i).faeden f).spur → D.maskiert L = false) ∧
  (∀ (g : Faden) (i j k : Nat), H g → fs i = g → (∀ r, r < i → fs r ≠ g) →
      i ≤ k → k < j → j ≤ n → ¬ FertigG (ms j) g → kern (fs k) = kern g → fs k = g)

/-- **No same-core interrupt deadlock** (fix lane F11, 2026-09-22, OFFEN O19). On a run
    from `M0` that a core schedule admits (`KernPlan`), a handler NEVER stands at a lock
    that a thread of its own core holds -- the deadlock `H102` refuses in Rust
    (`beispiele/gift/460`: a handler takes a lock the interrupted thread holds without
    `masks irqs`).

    The program side is a hypothesis of the leg, not of `GabbroZiel`: `Z t` is the call graph
    of thread `t` and `A t` its feature set (FadenMerkmal.lean), and for a HANDLER thread
    every lock its features admit is declared `masks irqs`. That IS `H102`
    (`maskenDisziplinB`, Zielsatz/Masken.lean, decides it over the member list); the
    `Einheit` does not say which roots are handlers, so the checker's Bool cannot carry it
    (OFFEN O19). `M0` is a start machine: no thread stands at a lock there
    (`anSperre_start_falsch`).

    Nothing in the leg constrains the program otherwise: it holds for EVERY program of G
    (`kernHaltG_gilt`), like `speicherSicher`. What it adds to `Ziel` is the reading of a
    schedule G itself does not know -- G interleaves freely, so in G the handler and the
    thread it interrupted are independent threads and the deadlock is none. -/
def KernHaltG (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (H : Faden → Prop) (Z : Faden → D.Fn → Prop)
    (A : Faden → D.Fn → Merkmal D),
    (∀ t, H t → MerkAbg P (Z t) (A t)) →
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t)) →
    (∀ t, H t → ∀ (f : D.Fn) (L : D.Lock), Z t f → (A t f).sperre L = true →
      D.maskiert L = true) →
    (∀ (t : Faden) (L : D.Lock), ¬ AnSperre M0 t L) →
    ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufG P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ (g f : Faden) (L : D.Lock), H g → f ≠ g → kern f = kern g →
        AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **Time**: a frame entered at `M`, of a function whose calls nest at most `n` deep, takes
    at most `kostenTief P passes (n + 1) g` own steps on every run while it is active. -/
def ZeitAb (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (g : D.Fn) (n : Nat) (rho : Env D (D.params g)) (s0 : World D) (k : Nat),
    rufTief P (n + 1) g = true → Eintritt P f g rho s0 k M →
    ∀ (M2 : RufMaschineG D) (run : SegLauf P O passes M M2), aktivVor f k run →
      segZaehle run f ≤ kostenTief P passes (n + 1) g

/-- **THE GOAL at a reached machine `M` of a run from `M0`**: the four legs, nothing else. -/
structure Ziel (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : Prop where
  -- memory safety (typing and in-range: intrinsic in `Programm D`)
  speicherSicher : SpurInv M
  -- data-race freedom
  rennfrei : RennfreiBis P O passes M0 M
  -- contracts where claimed
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  startEnde : StartEndeG P M
  keinStartGrund : KeinStartGrundG M
  keinLogikHalt : KeinLogikHaltG O passes M
  -- progress
  keineVerklemmung : (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t
  keinZyklus : KeinWarteZyklus M
  keinKernHalt : KernHaltG P O passes M0 M
  fortschritt : FortschrittG P O passes M
  -- time
  zeit : ZeitAb P O passes M

/-! ## Threads created at run time (2026-09-26, OFFEN O21/O22) -/

/-- Starter `t` waits for a root that has not finished (a JOIN wait). -/
def JoinWartet (K : FadenMaschine D) (t : Faden) : Prop :=
  ∃ u ∈ K.wartet t, ¬ FertigG K.m u

/-- **Thread `t` waits for thread `u`** on a thread machine: `t` joins nothing and stands at a
    lock `u` holds (`WartetAuf`), or `t` joins the unfinished root `u`. -/
def WartetF (K : FadenMaschine D) (t u : Faden) : Prop :=
  (K.wartet t = [] ∧ ∃ L, WartetAuf K.m t u L) ∨ (u ∈ K.wartet t ∧ ¬ FertigG K.m u)

/-- **No wait cycle, join waits included**: no threads `t₀ … tₙ₊₁ = t₀` each waiting for the
    next, by a lock or by a join -- whatever the other threads do. -/
def KeinWarteZyklusF (K : FadenMaschine D) : Prop :=
  ∀ (n : Nat) (ts : Nat → Faden), (∀ i, i ≤ n → WartetF K (ts i) (ts (i + 1))) → ts (n + 1) ≠ ts 0

/-- **Every stop is named, on the thread machine**: each thread is dormant (not spawned yet), or
    it is a starter that waits for an unfinished root or can end its join, or it joins nothing and
    is finished, waits for a lock, stands at a named stop, or takes a G step the thread machine
    admits. -/
def FortschrittF (P : Programm D) (O : Orakel D) (passes : Nat) (K : FadenMaschine D) : Prop :=
  ∀ t, K.lebt t = false ∨
    (K.wartet t ≠ [] ∧ (JoinWartet K t ∨
      ∃ K', FadenSchritt P O passes K K' ∧ K'.m = K.m ∧ K'.wartet t = [])) ∨
    (K.wartet t = [] ∧ (FertigG K.m t ∨ WartetG K.m t ∨ HaltBenannt O passes K.m .flagge t ∨
      HaltBenannt O passes K.m .budget t ∨ HaltBenannt O passes K.m .hardware t ∨
      HaltBenannt O passes K.m .nieZurueck t ∨
      ∃ M', RufSchrittG P O passes K.m t M' ∧
        FadenSchritt P O passes K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩))

/-- **THE GOAL on a thread machine `K` reached from the start machine `M0`** (since 2026-09-26):
    every leg of `Ziel` on its G state -- which contains every spawned thread, as a G thread --
    and the legs the thread machine adds:
    * `schlafendUnberuehrt`, `schlafendFrei` -- a not-yet-spawned thread is its start thread,
      and holds no lock: a spawned thread ENTERS HOLDING NOTHING (the model side of `N456`);
    * `joinFrei` -- a starter that waits for its roots holds no lock (the side of `N461`);
    * `keineVerklemmung` -- if every live unfinished thread waits (for a lock, or for a root),
      every live thread is finished: no global deadlock, join waits included;
    * `keinZyklus` -- no wait cycle through locks AND joins;
    * `fortschritt` -- every stop is named (`FortschrittF`). -/
structure ZielF (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) (K : FadenMaschine D) : Prop where
  g : Ziel P S O passes M0 K.m
  schlafendUnberuehrt : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  schlafendFrei : ∀ t, K.lebt t = false → ∀ L, L ∉ offen (K.m.faeden t).spur
  joinFrei : ∀ t, K.wartet t ≠ [] → ∀ L, L ∉ offen (K.m.faeden t).spur
  keineVerklemmung : (∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) →
    ∀ t, K.lebt t = true → FertigG K.m t
  keinZyklus : KeinWarteZyklusF K
  fortschritt : FortschrittF P O passes K

/-- **GABBRO_ZIEL.** Since 2026-09-26 over the THREAD MACHINE: every thread-machine run from the
    runtime's start, with any set `lebt0` of initially live threads -- the others are slots that
    `start` or `child` spawn at run time. Every G run is such a run (`lebt0` all live, nothing
    spawned: `fadenErreichbar_von_G`), so the statement of before is a corollary
    (`gabbro_ziel_g`). -/
def GabbroZiel : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflicht E →                                           -- (b) the user, on E
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbar E.P.mitRuhe O.mitRuhe passes
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielF E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) K

end Gabbro.Grammatik.Zielsatz
