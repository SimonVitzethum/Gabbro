/-
  File:    Grammatik/Zielsatz/Kern/Spec.lean -- THE GOAL AS STATEMENTS. Definitions only, no proof. Review target:
           every extension of the goal is a reviewed diff of this file. The history of this header (the review
           rounds, the lanes and agents that moved the statement, every superseded form) is in git:
           `git log -p -- grammatik/Grammatik/Zielsatz/Kern/Spec.lean`.

  GOAL (Simon): a Gabbro user proves only their own logic plus named hardware assumptions; memory safety, race
  freedom, contracts where claimed -- in concurrent runs too -- and time are carried by the language.

  NATIVE FLOAT HARDWARE BOUNDARY (owner, 2026-11-05). All floating operations,
  comparisons, conversions, codecs and literal interpretation use opaque native
  primitives. `RootNativeFloat.Hardware` is the named fourth component of (c),
  including its finite/range, unsigned and saturating-conversion contracts.
  Its seventh component additionally assumes nearest-even rounding for finite
  binary32/binary64 addition, subtraction, multiplication and division, with
  signed overflow and division-by-zero results. This strengthens the named
  hardware premise; zero signs and NaN payloads remain unconstrained. The
  proof kernel does not execute an IEEE arithmetic, rounding or packing model.
  There is no global instance discharging this hardware assumption. Memory,
  ownership, concurrency, user contracts and cost conclusions remain unchanged.
  The shared logical CPU operations and these proofs are ISA-independent. ARM,
  x86, RISC-V and other targets supply their own checked instruction, register,
  memory-order, ABI and encoding correspondences; x86 flags and SSE control do
  not form part of the shared scalar contract.

  C03 DESCRIPTOR STAGE (2026-11-02). `ReasonSpec`/`ReasonVal` describe nominal u128 codes, including unknown
  open codes, and source collection retains their identity, code order and closed flag. The current G/GX goals
  still use finite-index reason channels and scalar raw answers: open transport and typed payloads are NOT
  claimed by this preparatory stage. The authorized channel migration must extend `KopfHalt`, `InvAmGrundG`,
  `InvGutGrund` and foreign-answer admission to every admitted open code and every checked structured field,
  retaining the same named assumptions and user duties; it remains required before C03 is complete.
  C03 TYPED SOURCE SCHEMAS. Tagged collection now retains complete parsed payload types and resolves every
  present payload at an explicit kernel-admission gate. The kernel is still numeric-only at that gate;
  reading a bool, record, array, string or reference schema does not enable its execution as a sum payload.
  This source-stage refactoring does not yet change the domain or meaning of the goal statements below.

  THE STATEMENTS (proofs in Zielsatz/Atomar/BeweisAtomar.lean; `#print axioms` of each is exactly `propext`,
  `Classical.choice`, `Quot.sound`):
  * `GabbroZiel` -- safety, on every reached machine: the legs of `ZielFX` (below). Proof `gabbro_ziel`.
  * `GabbroZielSC` -- the same over machine G without the atomic rely and without the ownership leg; proved directly
    (`gabbro_ziel_sc`), and on every unit without an arena a corollary (`gabbro_ziel_sc_aus`), kept as a name
    because corpus theorems and embeddings are stated over it.
  * `GabbroZielVerbund` -- a program LINKED from two separately compiled units, each accepted alone, under the link
    check `SchnittstelleSpec` and the SAME hardware assumptions; conclusion `ZielF` on the linked unit
    (`gabbro_ziel_verbund`).
  * `GabbroZielLeben` -- liveness: on every weakly fair run of the ticket lock a thread standing at `locks L` takes
    `L`, or some thread holds `L` from some step on for ever (`gabbro_ziel_leben`).
  * `GabbroZielTerminierung` -- termination: under the measure duty (`decreases`, user logic), on every infinite run
    of machine GX every thread takes only finitely many steps, and a thread whose start the algorithm `klasse` puts
    in class `endet` never stands at a spent `forever` budget (`gabbro_ziel_terminierung`, proof in
    Zielsatz/Atomar/BeweisTerminierung.lean). See TERMINATION below.
  * `GabbroZielWarten` -- a waiting bound: on every run of the ticket lock a thread standing at `locks L` takes `L`
    within `wartezeit` scheduler steps, under four named premises of the run (`gabbro_ziel_warten`, proof in
    Zielsatz/Atomar/BeweisWarten.lean). See WAITING below.
  * `GabbroZielProfil` (C14, 2026-11-02) -- the same conclusion over a SELECTED, profile-bound unit
    (`ProfilEinheit`: the unit with its build mode, the ORIGINAL parsed items and the image's section policy;
    Zielsatz/Projekte/Profil.lean). MEANING CHANGE, two points. (1) Assumption provenance: (c) is stated through
    the named components of `HardwareAnnahmen` (`GutO`, `RegLokal`, `AxVertragO`; `hardware_iff_komponenten`) and
    the profile supplies exactly these (`profilAnnahmen_iff`): it adds no software and no unlisted assumption, a
    linked library requires profile entries by name and adds none (`bindung_fuegt_nichts_hinzu_bindung`); the
    free prose of an `assume` stays outside Lean. (2) The statement is about the unit a build mode selects out of
    the original items (`when TESTBUILD`, shipping or test; each mode is its own instance), (a) gains the
    structural admission of the selection/profile-binding/placement certificate (`profilAkzeptiert`), which is
    COMPUTED from the original items, never carried. The statements above are unchanged. Proof
    `gabbro_ziel_profil` (= `gabbro_ziel` on `PE.E`). Not claimed: that `PE.E` is the translation of the selected
    tree (the source-to-unit pipeline's correspondence), the layout/startup/relocation proofs that discharge
    static placement, an entry/service binding or a guest boundary (C08/C12 services, still refused).
  What may be said: "the goal theorem is proved over the model, with witnesses and non-degeneracy". What may NOT be
  said: "Gabbro is verified" -- the checker inside the statement is the Lean Bool, not the Rust checker, and no
  bridge from the model to a binary is built (THE READING, below).

  THE SHAPE. Everything is about ONE value `E : Einheit D`, the program the user wrote: code with contracts `E.P`,
  lock invariants `E.S`, the axioms' declared `ensures` `E.Q`, declared starts with arguments `E.starts`, run-time
  roots `E.gestartet`, the declared initial memory `E.sp0`. Four premise groups:
  (a) `C.akzeptiert E fs ls cs = true` -- ONE Bool of a checker `C : PrueferX`, sound against `AkzeptiertSpecX`; the atomic checker also requires static-array reset admission
      (fragment, closed call graphs, footprints local/guarded/admitted shared atomics, lock floors, lock places,
      lock-free starts, pool safety, write separation, answer sites, masking discipline, the C02 library binding
      (generated programs are ordinary; source certificates in `Uebersetzung.lean`), and since 2026-10-24 the
      ownership judgment of every arena in `E.arenen` with plain allocator words; beside it `BesitzStart E`: every
      declared-check admission (`CheckAdmission`); arena empty in `E.sp0`, no start handed an allocation). The concrete checker is
      `akzeptiertX_pruefer` (Zielsatz/Atomar/AtomarZiel.lean), deciding `AkzeptiertX`. `fs`/`ls`/`cs` are complete
      enumerations (finite declarations only).
  (b) `NutzerPflichtA E` -- the user's logic: every body, SEQUENTIALLY, at every `forever` budget, against every
      callee answer meeting the callee's contract and frame, every oracle answer of class (c), every lock move
      keeping the invariant (`HavocOk`), and every value a read of an admitted shared atomic may return (the rely):
      its `ensures` and owed invariants at value and reason exits, every callee's `requires`, no `logik` outcome
      (`LogikPflichtA`); the interface refinement `PtrVerfeinert` for every admitted pointer target (C06:
      contravariant requires, covariant normal ensures, part of (b), never discharged by structural acceptance);
      and the start (`StartPflicht`: the lock invariants at `E.sp0`, every root's `requires`
      there). For units the Lean parser elaborates, (b) is derived from GabbroV's duty files
      (`bruecke_nutzer`, `bruecke_nutzerA`) under per-unit decided name and rank conditions.
  (c) `HardwareAnnahmen O E.Q` -- the hardware and foreign code (THE ONE LIST, below).
  (d) `Laufzeit E sp init` -- the loader and the runtime's thread creation (THE ONE LIST).
  CONCLUSION of `GabbroZiel`: for every budget `passes`, every set `lebt0` of initially live threads and every
  machine `K` of the THREAD machine over GX (FadenMaschine.lean, GXMaschine.lean: machine G, threads spawned at run
  time by `start`/`child`, and every read of an admitted shared atomic answered by the weak memory) reachable from
  the runtime's start: `ZielFX` at `K`. The program run is `E.P.mitRuhe`, `E.P` plus the runtime's idle root
  (MitRuhe.lean; every function behaves as in `E.P`, MitRuheSemantik.lean).

  THE LEGS. `ZielX` at the G state `K.m` (reached from `M0`), `ZielFX` on the thread machine. "From" names what
  carries a leg besides machine G: (a) the checker, (b) the user, (c) the oracle class, "--" nothing.
  * `speicherSicher` (`SpurInv`) -- every recorded access carries its carrier's guards, whose locks are held. (c).
  * `speicherAdressen` -- if foreign code writes inside the declared extents (`ImBereichO`, inside the leg), every
    cell the run changed lies in its extent and, under every correct byte layout (`AdressLayout`, `LayoutOk`), with
    all its bytes in its table's region; different cells share no byte (Speichermodell/Adressen/). Addresses
    distinguish backing-region identities from the finite declared nominal data spaces. Tables and globals
    realize their declared spaces; every open extent retains its own backing identity even when several
    extents inhabit one nominal space. Names imply neither physical separation nor a check/copy snapshot.
    Separation remains a separate `LayoutOk` obligation. This generalizes the former fixed space-0/nonzero
    interpretation without removing `ImBereichO` or the outside-write/extent guarantees. (c).
    Table capabilities now retain these nominal spaces and independent read/write flags. Every admitted
    dereference resolves the exact table in a registered space; stores still require the signature's write
    frame and the table's guards. Write-only access does not grant reads. Owner identities are retained in
    types but are not usable without the separately checked ownership flow. Live byte grants and restricted
    entry handles remain outside this table-only stage; no lifetime or code/data provenance claim is added.
  * `rennfrei` (`RennfreiBisGA`) -- two accesses of different threads to a non-atomic carrier, one a write, are
    lock-ordered, on every run with racing atomics. (a), (c).
  * `schwach` (`SchwachX`) -- every step of the weak machine W is a GX step, its presented memory G's outside the
    shared atomics: the weak memory adds no behaviour beyond the rely. (a), (c).
  * `vertrag`, `invRueck`, `invGrund`, `keinLogikHalt`, `startEnde`, `keinStartGrund` -- (b)'s sequential clauses at
    the places of the interleaved run: `requires` at every logged entry, `ensures` and owed invariants at every
    logged return, no thread stuck at a `logik` check, a start finishes in its contract, no start at a reason.
    (a), (b), (c).
  * `sperrInv` -- every free lock has its invariant in shared memory. `sperrWechsel`, `sperrSicht` -- every acquire
    starts from it, every release leaves it, and no thread but the holder touches a protected carrier. (a), (b).
  * `invRuhe`, `invSicht` -- a table/group/global invariant holds wherever no unfinished thread is inside one of
    its writers, and for a thread holding one of its guards outside every writer (hypothesis: it held at the
    start). Since C05 the declared carriers of an invariant are tables AND globals (`D.traeger : Inv → List
    (Tab ⊕ Glob)`): a writer of a global carrier (`gschreibt`) owes the invariant and the group's locks
    (`gbraucht` beside `braucht`) exactly like a writer of a table, and an observation under a global carrier's
    guard counts. No shared atomic is a carrier (refused, `N484`). (a), (b).
  * `keineVerklemmung`, `keinZyklus` -- no global deadlock, no wait cycle (lock ranks). (a).
  * `keinKernHalt` (`KernHaltEA`) -- for every core assignment and every run the core hardware admits (`KernPlan`,
    inside the leg), a thread whose root the program declares an interrupt handler never stands at a lock another
    thread of its core holds. (a): the masking discipline.
  * `fortschritt` -- every thread is finished, waits for a lock, stands at a NAMED stop, or can step (SAFETY: no
    unnamed stuck state). (a), (b), (c).
  * `zeit` -- a frame with a finite call tree takes at most `kostenTief` own steps while active. --.
  * `folge` -- the order of calls in every thread's call log, for every order specification the program passes
    (Folge.lean). --.
  * `pruefstand` (`CheckTreueG`, C16, 2026-11-02) -- check evidence and its consumption: every completed probe
    measurement carries its verdict and floor outcomes as a report, each live or consumed Duty has exactly one
    corresponding completed report, and a consuming gate discharges that same report once; the prose claim is a
    label and proves nothing. (a), (b).
  * on the thread machine: `schlafendUnberuehrt`, `schlafendFrei`, `joinFrei` (dormant and joining threads hold
    nothing), `keineVerklemmung`/`keinZyklus` with join waits, `fortschritt` with the join wait, `spawnSicht` (a
    spawn leaves the G state alone, the new thread holds nothing, every free lock and closed invariant holds).
  * `besitz` (2026-10-24) -- for every arena of the unit, lifted to `E.P.mitRuhe` (`ArenaIface.mitRuhe`): one
    ledger of its slots agrees with the shared memory, the free list is well formed, the ledger keeps its
    discipline against every thread's stack depth, and every thread's running activation and every suspended
    caller realise what their ownership interfaces say (`OwnInv`, Bausteine/Arena/Ownership/Machine/Inv.lean).
    (a), (c).
  * `budgetUnecht` -- a thread at a spent `forever` budget takes a step at budget `passes + 1` from the machine
    with every counter one higher: the budget stop is no stop of the program (BudgetMonoton.lean: every run at
    budget `p` is a run at every larger budget).

  THE ONE ASSUMPTION LIST -- everything the statements assume that is neither the checker's Bool nor the user's
  proof:
  * (c) `GutO O` -- an axiom (a FOREIGN body: `extern fn`, `prim fn`, `asm`, `entry`, `entrust`) writes only its
    declared carriers, keeps the held locks and leaves its accesses in the trace. Nothing in the language can check
    foreign code. (Carriers, not indices: that it writes inside the declared extents is `ImBereichO`, below.)
  * (c) `RegLokal O` -- a register read answers from the carriers declared for its device; `awaits g` depends only
    on `g`. NAMED RESTRICTION: a register WITHOUT declared carriers answers the same value in every world, so
    `RegLokal` is stronger than a volatile device; such a register is read through an axiom or given carriers.
  * (c) `AxVertragO E.Q O` -- every axiom answer that fits its declared result type meets the declared `ensures`.
    A false `E.Q` is a false NAMED assumption, visible in the declaration. `Q := false` empties (c) for an axiom
    without a result; for one with a result (c) stays inhabited by oracles whose answers never fit, and every call
    then stops at `hardware`. Every type has a real decoding (`einpassen_voll`), so for an `E.Q` satisfiable at a
    decodable value, oracles with fitting answers exist and (b) must cover them.
  * (d) `Laufzeit.lader` -- the loader establishes the declared initial memory `E.sp0` (initialized data and zeroed
    storage of the image). That `E.sp0` meets the lock invariants and the start `requires` is the user's (b).
  * (d) `Laufzeit.start`/`.einmal` -- the runtime runs exactly the declared starts with their declared arguments,
    one thread per occurrence, and the idle root on every other thread; a routine runs on several threads only if
    declared at least twice (a worker pool). Run-time roots (`E.gestartet`) have slots that stay dormant until a
    `start`/`child` step spawns them. Assumed about the runtime and the lowering: (1) a spawned root's arguments are
    the unit's and its ghost entry world is the start world; (2) spawns happen only where the checked conditions
    hold (no lock held at a `start`, `N461`; the starter waits for every root; a `child` is entered with nothing
    held, `N456`); (3) every spawn succeeds (`Faden` is unbounded; thread creation failing is not modelled).
  * INSIDE A LEG, not in (c): `KernPlan` (`keinKernHalt`: masking works and a handler runs to completion on the
    core it preempted) and `ImBereichO` (`speicherAdressen`: foreign code writes inside the declared extents).
  * `GabbroZielLeben`: `Fair` -- the scheduler is weakly fair (a thread ready at every step from some point on
    takes a step). The FIFO order of the lock is no assumption: it is the model (`FifoLauf`, the ticket lock of
    laufzeit/sperre.gab and Code/Conc/Lock.lean), and the earlier runtime assumption `FifoSperre` is a theorem
    about it (`fifoSperre_aus`).
  * `GabbroZielVerbund`: the two units' hardware assumptions are the same (`E₂.Q = E₁.Q`).

  THE PERMITTED STOPS (`HaltArt`, in `fortschritt`) -- where the statement reports instead of claiming more:
  * `hardware` -- an axiom answer outside its (answerable) declared type, a register answer outside its type or
    against its declared promise (`D.rzusage`), a leaf's hardware outcome: foreign code or a device breaking its
    declaration.
  * `nieZurueck` -- a call of an axiom whose declared result is `never`: the call does not return (the declaration's
    promise about the foreign code). Every other empty answer type is refused by the checker (`antworten`).
  * `flagge` -- an `awaits` whose flag is not visible: a WAIT (not yet published, not visible, or never published).
  * `budget` -- a spent `forever` budget: a model artefact, and not final (`budgetUnecht`).
  A thread at any of these stops while holding a lock leaves every thread that needs it waiting for ever; that is
  the second case of `GabbroZielLeben`.

  THE READING -- not premises, assumptions of reading the statements as statements about the BINARY:
  * C02 translators use exact source-bound map correspondence, in addition to output typing
    (`Logik/Vertraege/Uebersetzung.lean`). Compile-time row collections are immutable by-value
    arrays, not runtime table capabilities. The goal applies to the generated accepted ordinary
    program; a translation certificate alone does not establish payload initialization, library
    call expansion or image correspondence. Those source cases remain refused until their generic
    bridges are connected. This strengthens the former output-only translation promise and adds
    no hardware assumption or change to the existing G/GX safety, contract, call-log or time legs.
  * Machine G (over GX) is the meaning of the compiled code at G's step granularity. The compiler is the LLVM path
    (`gabbro build`: checker, LLVM IR from `llvm.rs`, `opt`, `llc`, `ld.lld`); the bridge is translation validation
    (source -> model -> final machine bytes, checked in Lean; dokumente/PLAN-TRANSLATION-VALIDATION.md), which is
    NOT built. Code/ holds the refinement pieces (`lowerS_ok`, `stmt_gx`, the ticket lock), not a whole-program
    simulation.
  * The memory model, five named assumptions:
    (1) the view machine W over-approximates the C11 memory model -- the model LLVM's atomic orderings follow -- for
        the orderings the lowering uses, at G's step granularity: nothing interleaves inside a step, all reads of a
        step are checked against the pre-step view, a release message carries the view before the step's own
        writes; `seq_cst` is modelled as release/acquire (Speichermodell/Sicht.lean, a published promise-free
        timestamp machine, not proved here against an axiomatic model);
    (2) the toolchain and the hardware implement the atomic orderings as specified, and an `exchange` is lowered to
        ONE read-modify-write (`SchrittW.rmw`: the write sits directly above the message read);
    (3) every lock take is an acquire and every give a release (the runtime's ticket lock: fetch-add on `next`,
        acquire spin on `now`, release advance);
    (4) carriers are the locations (a table or an atomic array is one location of W);
    (5) what G reads from the outside -- foreign answers (`Orakel.wirkt`), register reads, the visibility of
        `awaits` -- is read over G's memory: the last executed write, not an older message.

  QUESTIONS TO THE OUTSIDE ARE TRACE EVENTS (2026-10-25, a change of meaning reviewed with the owner). Every
  foreign call, register read and `awaits` visibility first records `Ereignis.fremd` in the thread's trace
  (`World.fragt`), and the oracle answers in that world. So two calls of the same foreign body in the same memory
  are two different questions, and an oracle may answer them differently, as a real system does (a `read` that
  returns the next bytes, a provider that hands out a fresh cell). Before, every oracle had to answer both alike,
  so the statement covered no run in which a repeated call answered differently. The event touches no cell and no
  lock. `RegLokal` (premise (c)) still lets a register or visibility answer depend on the device carriers only, not
  on that history: lifting it needs the local replay of `ziel_ort_*` to record register answers as it records
  foreign answers -- named, open.

  WHAT A GREEN BUILD COVERS. Certificates are generated on demand (crates/gabbro-check/tests/zertifikate.rs): for
  every accepted `.gab` under `beispiele/` the exporter (`gabbro obligations --g`) either writes a certificate --
  the exported unit `gE`, the checker premise decided IN LEAN (`gCheck … := by decide`) and `GabbroZiel`
  instantiated on it with (b) open (`gP_gabbro_f`) -- which the Lean guardian elaborates, or refuses the program by
  name (`LG001`-`LG007`); the register is `target/zertifikate/REGISTER.txt`. Checked-in instances:
  Korpus/Programme/GenOblig104.lean, GenOblig108.lean. For a certified program the Rust checker's verdict is not in
  the chain. STILL TRUSTED: that `gE` IS the source program (the exporter is unverified; every form it drops is
  listed in the certificate's header), and THE READING above. A green build says NOTHING about an uncertified
  program; such a program reaches the statements only through a hand-written term.

  TERMINATION (2026-10-22, `GabbroZielTerminierung`). Two more premises beside (a)-(d), both user logic: a measure
  `m` (per function a lexicographic tuple of natural-number expressions over its parameters, the `decreases`
  clause) whose duty `MassPflicht` holds for every function -- every call back into the caller's cycle (`zykS`)
  has a smaller measure than the caller's entry -- and measures of one length along a cycle. A function on no cycle
  owes nothing (`massPflicht_ohne_zyklus`). The measure, its duty and the class are stated on the user's program
  `E.P`; the runs are those of the program with the idle root (`E.P.mitRuhe`), to which the duty transfers
  (`massPflicht_mitRuhe`). Claimed: (1) on every infinite run of the thread machine over GX from the runtime's
  start (any initially live threads; threads started, spawned and joined at run time) every thread takes only
  finitely many steps -- a `forever` is finite here because machine G grants `passes` passes from outside; (2) a thread whose start
  function the decision algorithm `klasse` (Logik/Terminierung/Klasse.lean: `endet`, `umgebung`, `bedingt`,
  `abgelehnt`, computed from the syntax) puts in class `endet` never stands at a spent budget: its end does not
  lean on the passes. Classes `umgebung` and `bedingt` are finite per pass (`durchgang_schritte`); how their loops can
  end is fixed in the model, not here (Logik/Terminierung/Ausgang.lean): a `forever` loop completes only through a
  pass that leaves and returns only through one that returns (`forever_bedingt`), and a loop whose body holds no exit
  -- the loops of class `umgebung` -- ends only at a logic or hardware stop, at its `progress` assumption when the
  passes are spent (`forever_umgebung`).

  WAITING (2026-10-23, `GabbroZielWarten`). Over the runs of the ticket lock (`FifoLauf`) from the runtime's start,
  four named premises of the run, none derived: the scheduler's fairness window `F` (`FairF`: a thread that can
  step at each of `F` consecutive steps takes one); the hold time (`Haltezeit h k`: on every stretch on which a
  thread holds `L` it takes at most `h L` own steps, `k L` of them at a nested `locks`); no named stop inside a
  critical section (`HardwareImAbschnitt`); the contenders `Ts L` (`Anwaerter`). Claimed: a thread standing at
  `locks L` takes `L` within `wartezeit ls Ts h k F L` scheduler steps (Logik/Fortschritt/Warten.lean: recursive over
  the lock ranks, `(c - 1)·(h·F + k·Wn + F) + F`). The hold time is a premise: that the checker's `held <= N ops`
  bounds the steps of a section in machine G is not proved (Lebendigkeit.lean, the two missing bridges).

  PER-CORE ACCUMULATORS (2026-11-02, C15 concurrency/link/export slice; a reviewed change
  of meaning in the sense of §1, staged beside the goal). One `accumulates` declaration
  becomes N private global cells with one exclusive lock each, a core-query binding and
  generated update/reduction functions. The checker admits the descriptor, the neutral
  initialization at the start memory and the storage/contract shape (`AccumulatorAdmission`
  in (a) with the Bool `accumulatorB`, `AkkuStart` beside it); the core identity provenance,
  the range facts and the quiescence condition are source-derived user duties in (b). The
  operators, neutral elements and fold/permutation/RMW laws are proved on the typed encodings
  (`Bausteine/Kernzelle`); the sampled fold equals the contribution fold under a proved
  quiescent history (`ruhigFalte`). Since this slice: each cell is proved guarded by its
  exclusive lock, so the ordinary race leg covers accumulator cells with no per-core
  exemption (`SperrProtokoll.akkuRennfreiAbgedeckt`; group invariants and `KernHaltEA`
  still apply); the quiescent collapse to the completed fold and the neutral-start RMW
  chain are proved at the ghost level with the staged added conjunct `AkkuZielErweitert`
  beside `ZielX`/`ZielFX`; the admission and neutral initialization cross separately
  compiled units through the link check (`SchnittstelleSpec.akku`, `BindeSpec.akku` with
  `akkuStart`, decided by the link Bools); the elaborator expands admitted declarations
  (`max`/`min`/`add`/`or` over integer ranges with a positive constant `per cpu` count) to
  guarded storage while updates, reads and the core query stay refused (they need the C08
  core-query contract); a full-program admission is witnessed on a non-degenerate two-cell
  fixture (`akkuProgramm_zeuge`). What is NOT claimed yet: the run-level existence of such
  a history for every reachable machine (needs the GX replay of the update stores), so the
  goal has no accumulator leg yet; any race exemption or universal quiescence (existing
  race/time qualifications are retained).

  NOT CLAIMED:
  * source-accepted pointer interface contracts: `CallContract` states the interface and `PtrVerfeinert` (O43)
    with local transfer to the selected target's concrete contract is now part of (b) (`LogikPflicht(A)`),
    with whole-body interface caller duty and prefix replay through havoc/atomic rely. `Programm.ptrVertrag`
    alone still proves nothing; pointer contract clauses remain refused by the source exporter
    (`uZeigerVertrag`, `ptrVertragGebunden`) until the full pipeline (export lowering, checker admission,
    Stage-0/IR and GabbroV duties) is connected. Existing concrete target contracts are still claimed;
  * a waiting bound without the four premises of WAITING (in particular the hold time derived from the program), a
    time bound for `forever` or recursion, termination of `umgebung`/`bedingt` beyond the budget
    (whether a `leave` guard or a base path is ever taken is the program's question); `GabbroZielLeben` claims that a
    lock wait ends unless a holder never lets go, not when, and not for runs over GX or with threads spawned at run
    time;
  * stack depth (G's stacks are unbounded; the LLVM lowering runs recursion without native stack growth, and
    exhausted memory fail-stops -- outside the model);
  * the compiled code and the hardware (THE READING); that the compiler's byte layout is a `LayoutOk` one;
  * reads in their extents as a statement about runs (they are, by the index types); globals and registers have no
    index;
  * that W is exactly the C11 model; a contract, `requires`, `ensures` or invariant over a shared atomic (refused,
    `N484`); linked units sharing an atomic across the link; the publish/await hand-off of an
    unguarded PLAIN payload (refused);
  * the run-level cell/history correspondence of per-core cells and their quiescent reduction
    (OFFEN O17; staged in C15, 2026-11-02: the descriptor, neutral initialization and admission
    are checked in (a) (`AccumulatorAdmission`, `AkkuStart`), per-cell guardedness and the
    ghost-level quiescent reduction are proved (`SperrProtokoll`, `AkkuZielErweitert`), the
    admission crosses the link (`SchnittstelleSpec.akku`, `BindeSpec.akku/akkuStart`) and
    admitted declarations expand to guarded storage, but updates, reads and the core query
    are still refused at elaboration (they need C08) and the goal has no accumulator leg
    yet);
  * a proof of hardware floating arithmetic: the opaque native operations and their
    numerical properties are the named `RootNativeFloat.Hardware` assumption, with
    the existing finite/range user duties and no software IEEE arithmetic model;
  * that a prose `claim` is true, or that one successful sample proves it (C16, 2026-11-02): a `false` verdict
    or floor outcome is a completed measurement with a negative verdict, and an unrun counterprobe is
    unmeasured, never passed;
  * an invariant inside a running writer or false in the start memory or reading carriers (tables or globals) outside its declared
    `traeger`; a lock invariant inside its holder's section (claimed: no other thread observes it there);
  * interrupt handlers beyond `KernPlan`: re-entry, handler-on-handler preemption, a thrown entry without `via idt`,
    a lock the unit does not declare (OFFEN O19);
  * an order of effects that are not calls of Gabbro functions, an order across a compound statement, an indirect
    call or a lock block, the entry of a `ruf` function run as a thread start, an order "sometime before", the
    promises of `breaking I` about its name (OFFEN O1);
  * a routine declared ONCE running on several threads (outside (d));
  * for linked units: differing hardware assumptions, a callback through an import, an importer relying on a
    contract other than the exporter's, dynamic loading, linking of foreign code below the ABI, the link step
    itself, ownership of an arena (`GabbroZielVerbund` concludes `besitz` over `[]`);
  * ownership beyond the arenas the unit declares (`E.arenen`): an arena whose allocator words are atomic, an
    arena not empty in the start memory, a start handed an allocation (each refused by the checker's
    `BesitzStart`/`worte`), and what a foreign body does to an arena beyond `GutO`;
  * C09 nominal-owner mint provenance and call-scoped owner-mark transfers/loans on canonical G/GX.
    `Signatur.owner` now contributes exact owner inputs to `Signatur.anfang`, owner outputs to
    `Vertrag.ende`, and both inventories to `nachSig`; pointer conformance preserves the same flow.
    This changes the typed entry/exit resource inventory, not the oracle assumptions. Canonical calls
    admit escrow-ready owner flows (`RufPasst.ownerReady` is `OwnerFlow.EscrowReady`): the caller's
    bindings move into a frame escrow at the push and the return gives back exactly the outputs,
    with conservation proved per edge (`Kern/Syntax/Marken/Owner/Escrow`). `Kern/Syntax/Marken/Owner`
    supplies linear ghost bindings and bookkeeping over the existing
    grant/escrow ledger, with permanent spent authority. No `OwnerInvG/GX` or owner provenance/lifetime leg
    is yet claimed by `Ziel(X/FX)`. The authorized stronger goal still needs C08 software-call execution,
    root/start admission and reachable-step/frame replay. No new source case is admitted by this work;
  * for threads spawned at run time: arguments per spawn, a root `requires` holding only at the spawn world,
    `old`-reads at the spawn world, the end of a join wait, the child's stack, a failing spawn, the lowering of the
    spawn;
  * dynamic data structures without a declared ceiling (OFFEN O29; an arena with ceiling `M` is a table of `M`
    slots, and the exporter refuses `grow`, `LG005`); probabilistic statements (OFFEN O29);
  * any release of a static's backing pages (C18, open): the pending page-return authority, the
    exclusive scope, the granule-aligned coverage and the zero-on-next-read contract stay open until
    the proved page-return binding (C08 grant ledger) is connected, with no OS assumption (page
    return is user logic). The `reset A at i count n` range itself is connected: it elaborates to
    `UStmt.resetRange` metadata, lowers via the checked range-store expansion into typed array
    stores, and is admitted (`AkzeptiertSpec.reset`);
  * every program the certificate register lists as UNCERTIFIED, by name.

  KNOWN DEBT. There is no definition-only layer: the goal predicates live in mixed files (ZielOrt, SperreFuss,
  SperreMaschine, Verklemmung, RennfreiVoll, KostenG, …), and the import closure includes witness files. To do:
  every definition this file reads out of its proof file.

  C08 FOUNDATION (2026-11-02, no change of meaning). New definitions only: the canonical
  foreign signature (`Deklaration.asignatur`), the provenance (`AxOrigin`, `axHerkunft`,
  `axBeleg`; unresolved by default, never inferred), call contracts with boundary clauses
  (`CallContract`, `BoundaryClause`, `Programm.axVertrag`), boundary records with the
  live-grant inventory and provider judgment (`BoundaryRecord`, `GrantInventory`,
  `ProviderOk`, `ProviderRealisiert`, `klauselGilt`), the generalized contract with replay
  (`AxVor`, `AxNach`, `AxVertragONeu`, `VertragANeu`), the software obligations
  (`ForeignPflicht` over the actual binding, `ProviderTreueG`, `GrantsStart` with
  `Einheit.grants0`), the interface component (`schnittstellenB`, `SchnittstellenOk`,
  folded into `Akzeptiert`/`AkzeptiertX` and `AkzeptiertSpec`/`AkzeptiertSpecX`), and the
  `Logik.fremdAntwort` outcome for unexpected software answers. The statements above are
  unchanged: wiring the software obligations into (b), narrowing the foreign part of (c)
  to named hardware, and the provider history in G are staged next.

  C08 PREMISE SPLIT (2026-11-02, authorized change of what (c) means; `GabbroZiel` itself is
  untouched and stays proved). `Zielsatz/Atomar/GabbroZielFremd.lean` states the same goal as
  `GabbroZielFremd` with the foreign premise split by provenance: (c) of the above reads
  "the hardware and foreign code", but a foreign item declared SOFTWARE (`axHerkunft`) is user
  logic -- its implementation proves its declared ensures against the actual binding `O`
  (`AxVertragOSw`, now part of (b)), and only the named hardware stays in (c')
  (`HardwareAnnahmenHw`: frame, register locality, the ensures of every item NOT declared
  software; unresolved provenance reads as hardware, the meaning of every unit before C08).
  `hardwareAnnahmen_of_split` shows the pair is exactly the old (c) (`gabbro_ziel_fremd` is
  `gabbro_ziel` recombined): no guarantee is weakened and nothing is newly assumed. The
  call-site form (the software contract's pre proved at each call, `CallSitePflicht`) and the
  provider history in the machine replace the unconditional software premise in a later step.
-/
module

import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public import Grammatik.Zielsatz.Kern.Spec.Teil1
public import Grammatik.Zielsatz.Kern.Spec.Teil2
public import Grammatik.Zielsatz.Kern.Spec.Teil3
public import Grammatik.Zielsatz.Kern.Spec.Teil4
