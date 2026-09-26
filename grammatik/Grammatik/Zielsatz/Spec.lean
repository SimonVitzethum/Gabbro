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
  A SECOND statement, `GabbroZielVerbund` (end of this file, since 2026-09-26), covers a
  program LINKED from two separately compiled units under the same hardware assumptions; its
  conclusion is this statement's `ZielF`, on the linked unit (the linking block below).

  WHAT A GREEN BUILD COVERS (OPUS AGENT C, 2026-09-26; messung/OPUS-C-TRAGWEITE.md). A header
  paragraph only: NO definition of this file changed, no premise moved, `Ziel`/`ZielF` are as
  before. It says, per REAL program, what a green `lake build` of `grammatik/` establishes, so
  that "Lean green => the language carries everything except what this header names" holds
  by construction and not by reading:
  * THE ONE LIST is `Grammatik/Zertifikat/REGISTER.txt`: every `.gab` under `beispiele/` (top
    level and `gift/`) the checker accepts, each either CERTIFIED or UNCERTIFIED. The cargo test
    `crates/gabbro-check/tests/zertifikate.rs` recomputes it from the tree and fails on any
    byte of difference, so an accepted program outside both lines, a stale certificate or a
    stale row turns `cargo test` RED. Measured 2026-09-26: 199 accepted, 23 CERTIFIED, 176
    UNCERTIFIED (of the 129 top-level corpus programs: 18 certified).
  * CERTIFIED: the program's certificate (the byte-exact output of `gabbro obligations --g`,
    imported by `Grammatik/Zertifikate.lean`, so in the build) holds the exported unit `gE`,
    decides (a) for it IN LEAN (`gCheck : akzeptiert_pruefer.akzeptiert gE … = true := by
    decide`) and states this theorem on it (`gP_gabbro_f`: `ZielF` on every reachable thread
    machine; `gP_gabbro`: `Ziel` on every G run), with (b) `NutzerPflicht gE` as the open
    hypothesis -- the user's part -- and (c), (d) as named above. For such a program the Rust
    checker's verdict is NOT in the chain of reasoning: the Lean Bool decides, and an exported
    program the Lean Bool refused would turn the build RED.
  * UNCERTIFIED: the exporter refuses the program (the row names its FIRST refusal, code and
    message, `LG001`-`LG007`). A green build says NOTHING about such a program; this statement
    reaches it only through a hand-written term (`Korpus07`, `Korpus125`), which no guardian
    pins to the source.
  * A program outside `beispiele/` is covered exactly when its own `gabbro obligations --g`
    output elaborates (the same file, the same `decide`); nothing checks that this was done.
  * STILL TRUSTED FOR A CERTIFIED PROGRAM, and named here as NOT CLAIMED: (i) that `gE` IS the
    source program -- the exporter (`lean_g.rs`) is unverified, and every form it drops is
    listed in the certificate's own header under "NO FORM in G" (declared `costs`, `reads`,
    deadlines with `arch`/`falsifier`, lock hold budgets, `traverse` annotations, `by ops`,
    `mut`, `pub`/`opaque`, `const fn` declarations, the hardware around `entry`/`boot`): none
    of them is claimed, whatever the Rust checker enforces about them; (ii) that machine G is
    the meaning of the emitted C -- the register marks `chain-instance=…` where a Lean instance
    of the generic closing theorem exists (104, 108 today, `zaehle-kette.py --lean` measures
    2 of 129 CLOSED) and `chain=none` everywhere else, where it is an assumption of the reading
    (below); of the emitted C forms, 51 have a correspondence lemma, 4 map to a named
    assumption and 27 have no semantics (`pruefe-cformen.py`, `KNOWN_UNCOVERED`).
  * TABLE AND GROUP INVARIANTS (review of Opus agent D, 2026-09-26): the exporter writes
    `Inv := Empty` and refuses `maintains` (`LG001`), so for every CERTIFIED program the legs
    `invRuhe` and `invSicht` are vacuous; of the invariant legs only the lock legs
    `sperrWechsel`/`sperrSicht` (and `sperrInv`) carry content there.
  * The Rust diagnostic codes (411 in the checker, 0 of its sentences in state PROVED) are
    therefore not premises of anything here: the ones mirroring `AkzeptiertSpec` are re-decided
    in Lean for every certified program, and the others guard properties this statement does
    not claim (the NOT CLAIMED list, and the dropped forms above).

  -- BEGIN linking block (Opus agent E, 2026-09-26) --
  WHAT CHANGED ON 2026-09-26 (OPUS AGENT E: LINKING SEPARATELY COMPILED UNITS), AND WHY -- a
  REVIEWED DIFF of this file (the review: messung/OPUS-E-LINKEN.md). PURELY ADDITIVE: no
  definition above changed, `GabbroZiel` is word for word the statement of before, and every
  theorem about it stands. What is added is a SECOND statement, `GabbroZielVerbund`, at the end
  of this file, with the definitions it reads.
  * THE GAP. The statement was about ONE `Einheit`: a function another unit supplies is not in
    its `D.Fn` with a body, and "linking of separately compiled units" stood in NOT CLAIMED.
    The language has the bridge (`gabbro abi` writes a `.gabi`, the importer is checked
    `--with` it: the exporter's heads, contract and effects, become `extern fn` heads), but
    nothing said that two units, each accepted alone, make an accepted program together.
  * THE MODEL. Two units `E₁`, `E₂` over ONE link declaration `D` (the union of their
    declarations; `Verbindbar`: the same contracts, table invariants, lock invariants and
    initial memory), unit 1 owning the functions where `e` holds. Each unit carries LEAF
    placeholders for the functions it does not own (`Platzhalter`: the `extern fn` head, which
    calls nothing the checker could follow). The LINKED unit `verbinde e E₁ E₂` takes every
    body from its owner, both units' starts and run-time roots, and the shared rest.
  * THE STATEMENT (`GabbroZielVerbund`): (a) each unit accepted ALONE by the checker, one link
    declaration, and the LINK CHECK `SchnittstelleSpec`; (b) each unit's user proves the bodies
    IT owns and its start (`NutzerTeil`); (c) the hardware meets the assumptions AND THEY ARE
    THE SAME for both units (`E₂.Q = E₁.Q`, one oracle); (d) the runtime starts the linked
    unit. Conclusion: `GabbroZiel`'s own -- `ZielF` on every reachable thread machine of the
    linked program, so race freedom and lock discipline ACROSS the units, spawned threads,
    joins and the weak-memory leg `schwach` are all claimed for the linked program.
  * THE LINK CHECK (`SchnittstelleSpec`, decided exactly by `schnittstelleB`,
    Zielsatz/Verbund.lean). Placeholders are leaves; no callback through an import
    (`KeinRueckruf`: an imported function's graph stays in its owner); and the three
    WHOLE-PROGRAM components of `AkzeptiertSpec` -- thread-locality (`fuss`), write
    separation (`renn`), pool safety (`einzeln`) -- re-decided over the COMPOSED hulls
    (`HuelleV`: a root's graph inside its owner, then inside the owner of every function of
    the other unit it reaches). That is where the interface carries the footprints: a unit
    alone sees neither the other unit's threads nor a read hidden behind an imported head
    (the refusal witness `vm_abgelehnt` is exactly that). The per-body components (fragment,
    closed graphs, lock floors, lock-invariant places, roots, answer sites) are each owner's
    own verdict.
  * WHY IT HOLDS (`gabbro_ziel_verbund`, Zielsatz/Verbund.lean): the linked unit meets every
    premise of `GabbroZiel` -- `akzeptiertSpec_verbinde` (a body's footprint and features
    depend on its own text and the shared contracts only; the linked call graph of a root
    lies in its composed hull; the linked graph is closed), `nutzerPflicht_verbinde` (a body
    triple depends on its own body and the contracts only) -- and `gabbro_ziel` applies.
  * EMBEDDING: `verbinde_leer` -- a unit linked with a partner that owns and starts nothing is
    the unit itself; `verbinde_akzeptiert`, `nutzerTeil_verbinde` -- the linked unit is
    accepted by the concrete checker and carries the restricted user duty, so a chain of units
    links by iteration.
  * WITNESSES (Zielsatz/VerbundZeuge.lean): `vz_ziel`/`vz_lauf_zeuge` (a library exports the
    lock-guarded table writer `wrap` with `ensures konto[0] == 100`, an app calls it from two
    threads; each unit accepted alone, the link accepted, `ZielF` on the linked program, and a
    run where both app threads step and one holds the lock); `vm_abgelehnt` (footprints that
    do not compose: each unit accepted alone, the link refused, and the whole-program checker
    refuses the linked program too); `vz_vertrag_zu_schwach` (the exported contract is weaker
    than the importer's: no link declaration).
  -- END linking block --

  -- BEGIN invariant block (Opus agent D, 2026-09-26) --
  WHAT CHANGED ON 2026-09-26 (OPUS AGENT D: INVARIANTS BEYOND THE RETURNS, OFFEN O11), AND WHY
  -- a REVIEWED DIFF of this file (the review: messung/OPUS-D-INVARIANTEN.md). NO premise
  moved; `Ziel` gains four legs, `ZielF` one:
  * THE GAP. NOT CLAIMED read "invariants at entry or while locks are held (claimed at returns
    only)". `Ziel` said that a table/group invariant holds at every logged return of a function
    that owes it (`invRueck`, `invGrund`) and that a FREE lock has its invariant in memory
    (`sperrInv`); nothing said what a function sees at its entry, what the acquirer of a lock
    starts from, or what the other threads see while a lock is held.
  * THE DIFF (definitions above `Ziel`): `InvTraeger` (the invariant reads only its declared
    carriers), `InvZu` (no UNFINISHED thread has a frame of a function that owes it), and the
    legs
    - `invRuhe : InvRuheG P M0 M` -- every invariant that reads only its carriers and held in
      the start memory holds at `M` whenever it is closed there;
    - `invSicht : InvSichtG P M0 M` -- a thread outside every writer of an invariant that holds
      a guard lock of one of its carriers sees it intact, whatever the others do;
    - `sperrWechsel : SperrWechselG P O passes S M` -- every step from `M` that acquires `L`
      goes from a memory where `S.inv L` holds to one where it holds, and every release leaves
      one where it holds;
    - `sperrSicht : SperrSichtG P O passes S M` -- every step from `M` that accesses a carrier
      `L` protects holds `L`, and while a thread holds `L` no other thread's step moves it;
    and `ZielF.spawnSicht` -- a spawn leaves the G state alone, the spawned thread holds no
    lock, every free lock has its invariant and every closed invariant holds at that moment.
  * WHAT IS NOW CLAIMED, precisely, and what the words "at entry" and "while held" can mean:
    - AT ENTRY: an invariant is owed by every function whose effects write one of its
      carriers (`schuldet`), and inside such a body it may be broken. A function CALLED from
      inside a writer may see it broken at its entry, so "at every entry" is false in general.
      Claimed: at every entry -- indeed at every machine -- reached while no unfinished thread
      is inside a writer (`invRuhe`), and at every point of a thread holding one of its guards
      outside every writer (`invSicht`). A writer's callee sees what the writer's `requires`
      to it says, which is the user's logic. (Review 2026-09-26, URTEIL-SPECDIFF-OPUS-D:
      a callee's writes are its caller's (`RufPasst.hw`), so every frame BELOW a writer --
      up to the thread's start function -- is a writer too. A thread that ever writes a
      carrier of `i` keeps `i` open for its whole life; `invRuhe` bites once every such
      thread has finished, and at every point of a program in which no running thread writes
      `i`. And with the declaration's `invarianten_gehalten` (a writer holds every guard BY
      SIGNATURE) and lock-free starts, an invariant with a GUARDED carrier has, by argument
      and not by a theorem, no writer reachable from an accepted start at all: it is frozen
      at its start value, and `invSicht` then says no more than `invRuhe`. The Rust `U003`
      counts `locks` in the body instead -- the model is stricter, see the verdict.)
    - WHILE HELD: an invariant is a predicate over SHARED memory and the holder's writes are
      shared memory at once, so the holder may break a lock invariant inside its section and
      the memory then does not satisfy it. "Other threads never observe it broken" means,
      exactly: no step of a thread that does not hold `L` touches a protected carrier, and no
      step of another thread moves one while `L` is held (`sperrSicht`); every section starts
      from the invariant and every release restores it (`sperrWechsel`). A held lock's
      invariant is observed by its holder alone, at observation points -- that is the claim.
    - AT THE START: a lock invariant at `E.sp0` is (b) already (`StartPflicht.sperren`), so
      `sperrInv` holds at the start machine; a table invariant at `E.sp0` is the HYPOTHESIS of
      `invRuhe`/`invSicht` (see below). ACROSS SPAWNS: `spawnSicht`.
  * WHY NOTHING IS WEAKENED. The premises of `GabbroZiel` are textually unchanged (`Einheit`,
    `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`). `Ziel` and `ZielF` gain
    conjuncts and lose none; every earlier leg is proved by the same term (Zielsatz/Beweis.lean),
    so `gabbro_ziel_g`, `gabbro_ziel_vor` and every certificate still hold, and the old `Ziel`
    is a projection of the new. Unlike `keinKernHalt` and `zeit`, these legs are NOT
    premise-free: `invRuhe` uses (b) through `invRueck`, `invGrund` and `StartEndeG`;
    `sperrWechsel` uses `sperrInv` ((a) and (b)); `sperrSicht` and `invSicht` use (a)
    (`sperrOrte`, lock-free roots: start exclusivity) and the declaration's `U003`
    (`invarianten_gehalten`).
  * WHY TABLE INVARIANTS AT `E.sp0` STAY A HYPOTHESIS. (b) did not demand them before, and
    making them a (b) duty would drop from the statement every program whose declared table
    invariant is false at its initializer -- programs the old legs covered. As a hypothesis of
    the leg nothing is dropped; for a concrete unit it is decidable. (Measured on the corpus:
    `beispiele/09`'s invariant WAS false at its zeroed table, and at its own writer's return --
    repaired with `N496`, see below.)
  * WHAT CARRIES THE PROOF (Zielsatz/Invarianten.lean): a step changes a carrier only if its
    head function may write it (`schritt_traeger`), so outside every writer nothing moves the
    invariant; the step that ends the last writer frame is a POP -- every step appends at most
    one call-log event (`schritt_logArt`, over the 70 rules) and the log determines the key
    stack (`rufLogPasstG_eind`, `schritt_schluessel`), so the popped writer's return is logged
    and `invRueck`/`invGrund` give the invariant at the memory the step leaves -- or the thread
    FINISHES at the writer's return (`StartEndeG`, `fertig_retKopf`). The lock legs are
    exclusivity (`exklusivG`), the rely (`relyG`), the guard of every access (`zugriff_haelt`)
    and `sperrInv` at the machines before and after the move.
  * OFFEN O11 (an invariant no function `maintains` was booked by nothing) is CLOSED on both
    sides. Model: every function that writes a carrier owes the invariant at its returns
    (`schuldet`, `InvGutS`/`InvGutGrund` in `LogikPflicht`), and one no function writes is
    carried by the frame (`inv_ohne_schreiber`). Rust: `N496` refuses a function whose effects
    write, publish or consume a carrier of a `table`/`group` invariant without naming it in
    `maintains`.
  * WITNESSES (Zielsatz/InvariantenZeuge.lean, on the two-writer program `mP` of
    MehrfadenZeuge.lean): the lock invariant `konto[0] == konto[1]` is BROKEN at a reached
    machine inside thread 0's section (`konto = [30, 0]`), where no step of thread 1 can touch
    `konto`; after the release, thread 1's acquire starts from `konto[0] == konto[1]` BY THE
    LEG; the table invariant `privA[0] == privA[1]` is BROKEN inside `hauptA` and holds, BY THE
    LEG, at thread 1's entry of `setze` once thread 0 is finished; and the refusal side of O11
    is `beispiele/gift/1231`-`1234`.
  * WHAT STAYS NAMED (NOT CLAIMED below): an invariant reading carriers outside `D.traeger`;
    a table invariant false at the start; any invariant at a point where an unfinished thread
    is inside one of its writers (it may be broken there, by design); and every certified
    program has NO table invariant (the exporter writes `Inv := Empty`), so for them
    `invRuhe`/`invSicht` are vacuous and the contentful new legs are the lock legs.
  -- END invariant block --

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

  -- BEGIN weak-memory block (Opus agent B, 2026-09-26) --
  WHAT CHANGED ON 2026-09-26 (OPUS AGENT B: THE MEMORY MODEL BEYOND DRF-SC), AND WHY -- a
  REVIEWED DIFF of this file; NO premise moved, `Ziel` gained ONE leg:
  * THE GAP. G is sequentially consistent, and the header read "the hardware is DRF-SC" as an
    assumption of the reading; `atomic` globals were "ordered by A10" and excluded from
    `rennfrei`. The emitted C is a C11 program with relaxed, release/acquire and seq_cst
    atomics and `pthread_mutex` locks (or own/foreign lock primitives, see assumption (3) of
    the reading below); nothing proved that its weak behaviours are G's.
  * THE MODEL (Speichermodell/Sicht.lean, MaschineW.lean). Machine W is machine G over a WEAK
    memory: a history of messages per carrier (plain and atomic), a view per thread and per
    lock, message views for release writes. A thread's step READS, at every carrier it reads,
    ANY message at or above its view -- not necessarily the newest -- and writes at a fresh
    timestamp above its view. This is the promise-free timestamp machine of RC11 for the
    orders the emitter writes (relaxed; release store / acquire load / acq_rel RMW; `seq_cst`
    modelled as release/acquire -- an over-approximation, so claims over W hold for the C, at
    G's step granularity and under the five named assumptions of the reading below).
    The weakness is real: on the instruction machine built from the same primitives the
    stale outcome of relaxed message passing and both-zero store buffering are REACHABLE
    (`mp_rlx_erlaubt`, `sb_erlaubt`), the latter not on SC (`sb_sc_verboten`); release/acquire
    forbids the MP outcome (`mp_ra_verboten`); coherence holds (`corr_verboten`).
  * THE DIFF. New `SchwachSC P O passes M0 M` and the leg `schwach` of `Ziel`: at every
    reached machine `M`, for EVERY assignment of memory orders to the atomics, every step the
    weak machine takes from a weak state over `M` (reached from `RufStartW M0`) is a step of G
    from `M` to the successor's G-part. With it (`gabbro_ziel_schwach`, Zielsatz/Schwach.lean)
    every leg of `Ziel` holds at every machine W reaches: the goal is proved over the weak
    machine, not only over G. SCOPE since the merge with Opus agent A (thread machine): W is
    taken over G's runs from the start machine; `ZielF.g.schwach` holds at every reachable
    thread machine `K.m` (`gabbro_zielF_schwach`), but W does NOT model spawn and join
    (`pthread_create`/`pthread_join`) as synchronisation points. Under DRF by exclusion that
    costs nothing (a child reading what its parent wrote is refused by `fuss` unless the
    carrier is guarded), and it is no claim that spawn/join order memory.
  * WHY IT HOLDS (the DRF theorem, Speichermodell/DRF.lean, `schwach_ist_g`): the checker's
    footprint component (`fuss`) already demands that every carrier a thread's graph READS is
    thread-local or lock-guarded -- `atomic` carriers included -- and every access to a guarded
    carrier holds its lock. So a thread's view reaches the newest message of every carrier it
    reads (its own writes, or the lock's view joined at the take), `Lesbar` admits only that
    message, and it carries G's value (`liest_neueste`, `praesentiert_g`).
  * WHY NOTHING IS WEAKENED. `Ziel` gains a conjunct and loses none; no premise of `GabbroZiel`
    changed. Unlike `keinKernHalt` and `zeit` the leg is NOT premise-free: it uses (a) (`fuss`,
    closed graphs) and (c) (`GutO`), and W really is weaker than G where the checker refuses:
    on the refused configuration of `w_nicht_sc` (Speichermodell/Zeuge.lean; `konfig` written
    by one start and read by another, no lock) W reads the initial value after the write and
    stores `0` where every G step of the same thread stores `3` -- as a theorem,
    `schwach_nicht_trivial`: `¬ SchwachSC` at that reached machine (via `g_schritt_0`,
    inversion over the rules of G). W contains G (`w_aus_g`: every run
    of G is a run of W), so the new statement covers every machine the old one did, and more.
    Witness on an accepted program: `schwach_pool_zeuge` (three W steps on the F10 pool,
    every leg of `Ziel` by `gabbro_ziel_schwach`).
  * WHAT IT DOES NOT BUY, named below (NOT CLAIMED, OFFEN O25): the goal still covers no
    program that RELIES on an unguarded atomic read across threads -- `fuss` refuses such a
    program -- so the non-SC outcomes of W never occur on an accepted program.
  -- END weak-memory block --

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
  * Not premises, but assumptions of the reading: machine G is the meaning of the C at G's
    step granularity (translation validation, PLAN-UEBERSETZUNGSVALIDIERUNG). Until
    2026-09-26 a second clause read "the hardware is DRF-SC"; it is WITHDRAWN for accepted
    programs -- sequential consistency of what a step reads is now the leg `schwach`, proved
    (weak-memory hunk, Opus agent B; repaired after the Spec-diff verdict of 2026-09-26, F1,
    F2, F5). What replaces it, FIVE named assumptions of the reading:
    (1) the view machine W over-approximates the C11 (RC11) memory model for the orders the
        emitter writes -- AT G's STEP GRANULARITY and jointly with the translation-validation
        reading above, not on its own: W steps are G's coarse steps, so nothing interleaves
        inside a step (that is exactly "G is the meaning of the C"), all reads of a step are
        checked against the pre-step view, and a release message carries the view before the
        step's own writes (the last two make W weaker than C11, the safe direction).
        `Speichermodell/Sicht.lean`: promise-free timestamp machine, `seq_cst` as
        release/acquire; a published model, not proved here against an axiomatic C11;
    (2) the C compiler and the hardware implement C11 atomics and the orders as specified;
    (3) EVERY lock primitive `<L>_nimm` is an acquire and every `<L>_gib` a release, whoever
        implements it: a driver-defined lock (`pthread_mutex_lock`/`_unlock`, `treiber.rs`);
        an OWN primitive -- a bodied `<L>_nimm`/`<L>_gib` over a declared atomic, `N323`
        (atomicity, the body reads an atomic, hold time) and, since 2026-09-26 (Opus lane
        O25, OFFEN O26; a comment-only correction of this header, no definition moved), the
        orders `N481`-`N483`: the take reads an atomic declared `acquire`/`release`/`seq`,
        the give writes one, and a take and a give of one lock meet on such an atomic -- so
        for own primitives this is CHECKED at the source level, the lowering of the orders
        staying (2); or a foreign one (`extern fn`/`asm`, trust base) -- ASSUMED. Measured
        the same day: `N042` refuses the C name of every own or foreign `<L>_nimm`/`<L>_gib`
        beside `lock L`, so on an accepted program today every lock is driver-defined;
    (4) carriers are the locations (a table or an atomic array is ONE location of W; the DRF
        argument holds per element as well, since it only uses the lock and locality facts);
    (5) what G reads WITHOUT recording it is read over G's memory: the answers of foreign code
        and axioms (`Orakel.wirkt`, `axiomAntwort`), register reads (`O.regLies`) and the
        visibility of `awaits` (`O.sichtbar`) are taken over G's memory at every carrier the
        step does not record (`SchrittW` presents G's memory there; RennfreiVoll.lean lists
        these reads as unrecorded). That the foreign side, the device and the `awaits`
        hand-off see that memory -- the last executed write, not some C11-admissible older
        message -- is ASSUMED, not derived. This is the part of the old "hardware is DRF-SC"
        that the leg `schwach` does not discharge.

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
  * `invRuhe` (`InvRuheG`), `invSicht` (`InvSichtG`) -- NEW (Opus agent D): (b) checks a table
    invariant at the returns of each body only; the theorem's is that it holds in shared
    memory wherever no unfinished thread is inside a writer of it, and at every point of a
    thread that holds one of its guards outside every writer.
  * `sperrWechsel` (`SperrWechselG`), `sperrSicht` (`SperrSichtG`) -- NEW (Opus agent D): (b)
    assumes the invariant at each acquire (`HavocOk`) and checks it at each release of ONE
    body; the theorem's is that every acquire in the interleaved machine really starts from it,
    every release really leaves it, and no thread but the holder touches a protected carrier
    while the lock is held. With `sperrInv` that is the lock invariant everywhere it can be
    observed.
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
  * `schwach` (`SchwachSC`, weak-memory hunk, Opus agent B 2026-09-26) -- NOT in (b): the weak
    machine W takes only G's steps on the program, for every order assignment; hence every
    leg holds on every machine W reaches (`gabbro_ziel_schwach`). From (a) (`fuss`: every
    read carrier is thread-local or lock-guarded, atomics included) and (c) (`GutO`).
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
  * (invariant block) `InvTraeger`, `InvZu`, `InvRuheG`, `InvSichtG`, `SperrWechselG`,
    `SperrSichtG` (here) -- over `InvHaelt`/`schuldet` (ZielOrtInv, Semantik), `FertigG`
    (Verklemmung), `ZugriffG`/`TraegerGleich` (RennfreiVoll, ZielOrt) / an `InvZu` that
    ignored a running writer would claim an invariant the writer is breaking; an `InvZu`
    that asked finished threads too would make `invRuhe` vacuous for every invariant a start
    function writes; a `SperrSichtG` over steps not taken from `M` would say nothing.
  * `InvAmOrtG` ZielOrtInv:66; `StartEndeG` ZielOrtStart:70 (`RetKopf` :59); `KeinStartGrundG`
    :191; `KeinLogikHaltG`/`PrueftG` ZielOrtGanz:658/622 -- no thread stuck at a loop invariant
    or transition test. `FertigG`/`WartetG`/`AnSperre` Verklemmung:746/751/652.
    `BereichG` Fortschritt.lean -- the float range checks pass at every head (proof side,
    not in `Ziel`: `FortschrittG` lists no float stop, so it follows from `fortschritt`).
  * `Eintritt`/`SegLauf`/`aktivVor`/`segZaehle`/`kostenTief`/`rufTief` KostenG:788/740/776/750/955/964.
  * (weak-memory hunk) `RufMaschineW`, `RufStartW`, `SchrittW`, `RufSchrittW`, `RufErreichbarW`,
    `ordVon`, `vorSicht`, `lesenVon`/`genommenVon`/`gegebenVon` Speichermodell/MaschineW.lean;
    `Nachricht`, `Sicht`, `Ordnung`, `beitrag`, `nachricht`, `Lesbar`, `Frisch`
    Speichermodell/Sicht.lean -- the weak machine / a rule W lacks against RC11 (a behaviour
    the C has and W not) would make `schwach` claim SC where the C is weaker; the direction
    that matters is "W admits at least every C11 behaviour", which the header names.
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
  created at run time, Opus agent A 2026-09-26; legs proved in Zielsatz/Faeden.lean);
  `SchwachSC` and the leg `schwach` (the weak machine takes only G's steps, Opus agent B
  2026-09-26, proved in Speichermodell/DRF.lean); `InvTraeger`, `InvZu`, `InvRuheG`,
  `InvSichtG`, `SperrWechselG`, `SperrSichtG`, the legs `invRuhe`, `invSicht`, `sperrWechsel`,
  `sperrSicht` and `ZielF.spawnSicht` (invariants beyond the returns, Opus agent D
  2026-09-26, proved in Zielsatz/Invarianten.lean).

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
  emitted C overflows); the C and the hardware; (weak-memory hunk, 2026-09-26: the line
  "weak memory beyond DRF-SC" is REPLACED -- what is now claimed is the leg `schwach`: W,
  the weak machine, adds no behaviour on an accepted program, for every order assignment,
  and every leg holds on every machine W reaches) programs that RELY on an unguarded atomic
  read across threads -- a flag, counter or per-core cell one thread writes and another reads
  without a lock: the footprint component `fuss` refuses them (a read carrier another start
  writes must be thread-local or lock-guarded, `atomic` or not), so W's non-SC outcomes
  (`mp_rlx_erlaubt`, `sb_erlaubt`) occur on no accepted program and no theorem here speaks
  about them; covering them needs the user's sequential semantics to havoc such a read (a
  rely), OFFEN O25 (the exporter refuses `atomic` items anyway, `LG001`; the MEMORY half is
  proved standalone since 2026-09-26, outside this statement: with the footprint check
  exempting atomics, every W step is a step of G whose atomic reads are answered per W and
  whose plain carriers stay sequentially consistent, `schwach_ist_gA`,
  Speichermodell/Atomar.lean -- the replay of the user's proof over such steps is what is
  missing); that W is exactly
  RC11 (it over-approximates it at G's step granularity: `seq_cst` is modelled as release/acquire, so no SC-order
  fact is claimed; no promises, hence no load buffering, which RC11 forbids as well);
  `atomic` globals stay excluded from `rennfrei` (their accesses are atomic operations, not
  races; `schwach` covers their values); the publish/await hand-off of an unguarded payload (refused by the checker,
  see P3); floats only as the kernel IEEE model of GLEITKOMMA §7 (no float assumption on G's
  side -- true since F1: an out-of-range result is the user's `logik bereich`, not a
  hardware stop; `gleitkomma_ieee` is on the C side); starvation freedom; (Opus agent D,
  2026-09-26: the line "invariants at entry or while locks are held (claimed at returns only)"
  is REPLACED -- what is now claimed is `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`
  and `spawnSicht`, see the invariant block above) a table/group invariant at a point where an
  unfinished thread is inside a function that writes one of its carriers (it may be broken
  there by design; a writer's callee sees what the writer's `requires` to it says), one that is
  false in the start memory (the start is the legs' hypothesis, not a (b) duty), and one whose
  predicate reads carriers outside its declared `traeger` (`InvTraeger`); a lock invariant
  INSIDE its holder's section (the holder may break it; claimed is that no other thread
  observes the protected carriers there, and that every acquire and release sees it); WHICH threads are interrupt handlers and which
  core they share -- the `entry … via idt` dispatch fact is not in `Einheit` and G has no
  cores, so `keinKernHalt` takes them (and the masking discipline `H102` checks) as its own
  hypotheses instead of reading them from (a)/(d), and the emitted C realises no masking at
  all (no `cli`/`sti`; `beispiele/59` says so in its header) -- OFFEN O19; a busy routine declared ONCE on several threads
  (outside (d); a routine declared twice may run on any number of threads since fix lane F10,
  and the checker admits that only pool-safe, `EinzelnPool`); (linking hunk, 2026-09-26: the line
  "linking of separately compiled units" is REPLACED -- what is now claimed is
  `GabbroZielVerbund`: two units over one link declaration, each accepted alone, the link
  check, the SAME hardware assumptions, `ZielF` on the linked program) for LINKED units:
  units whose hardware assumptions DIFFER (the premise `E₂.Q = E₁.Q`; the Rust `N505` refuses
  an assumption both units name with different content); a callback through an imported
  function back into the importer (refused by `KeinRueckruf`, not covered); an importer
  relying on a contract other than the exporter's, weaker or stronger (the link declaration
  has ONE contract per function; a differing head is refused, `N501`-`N504`); dynamic loading
  (the linked unit is fixed before the start); ABI-level linking of foreign C (an `extern fn`
  no Gabbro unit supplies stays an axiom of (c)); the C-level link step itself (symbol
  resolution, calling convention, record layout -- translation validation's, like every "G
  is the meaning of the C"); and the RUST side of premise (a) only as far as the Rust checker
  is the Lean Bool at all (the caveat of one unit): since Opus agent F `gabbro link` checks the
  LINKED program whole -- every start of both units, every footprint from its owner's body --
  and an imported head's declared READS join the importer's own footprint, which closes the
  false accept of review E, F1 (messung/URTEIL-SPECDIFF-OPUS-E-2026-09-26.md,
  messung/OPUS-F-VERBUND-RENNEN.md; OFFEN O28); for threads SPAWNED at run time (claimed since 2026-09-26, see
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
  translation-validation chain, not of this statement. Which corpus program is on which side
  is THE ONE LIST `Grammatik/Zertifikat/REGISTER.txt` (see WHAT A GREEN BUILD COVERS above):
  every UNCERTIFIED program there is NOT CLAIMED, by name.

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
import Grammatik.Speichermodell.MaschineW
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

-- BEGIN weak-memory definition (Opus agent B, 2026-09-26) --
/-- **The weak machine adds no behaviour at `M`** (Opus agent B, 2026-09-26). For EVERY
    assignment `ord` of memory orders to the atomics, every weak state `W` over `M` (`W.g = M`)
    that machine W reaches from the weak start over `M0` (`RufStartW`: every carrier one
    message, every view empty), and every step W takes from there: it is a step of G from `M`
    to the successor's G-part. Machine W (Speichermodell/MaschineW.lean) lets a thread read
    ANY message of a carrier at or above its view -- relaxed, release/acquire and lock views --
    so this is the DRF theorem for the program: on it the weak memory reads only the newest
    write. -/
def SchwachSC (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ord : D.Glob → Speichermodell.Ordnung) (W W' : RufMaschineW D) (u : Faden),
    RufErreichbarW P O passes ord (RufStartW M0) W → W.g = M →
    RufSchrittW P O passes ord W u W' → RufSchrittG P O passes M u W'.g
-- END weak-memory definition --

-- BEGIN invariant definitions (Opus agent D, 2026-09-26) --
/-- **The table/group invariant `i` reads only its declared carriers**: every carrier its
    predicate reads is one of `D.traeger i`. (`invSicht` only asks that a read carrier's GUARDS
    be among those of the declared carriers; a predicate reading another table under the same
    lock, or an unguarded table, reads carriers that functions NOT owing `i` may write.) -/
def InvTraeger (P : Programm D) (i : D.Inv) : Prop :=
  ∀ c ∈ (P.invariante i).orte, ∃ t ∈ D.traeger i, c = Sum.inl t

/-- **The invariant `i` is CLOSED at `M`**: no unfinished thread has a frame -- the head or a
    suspended caller -- of a function that owes `i` (`schuldet`: its effects write a carrier of
    `i`). A finished thread (empty stack, head at its return) is not asked: it moves nothing
    any more, and its start function's owed invariants hold where it stopped (`StartEndeG`). -/
def InvZu (M : RufMaschineG D) (i : D.Inv) : Prop :=
  ∀ t, ¬ FertigG M t → ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false

/-- **Table and group invariants wherever no writer is running** (Opus agent D, 2026-09-26).
    Every invariant that reads only its carriers and held in the start memory holds in the
    shared memory of `M` whenever it is CLOSED there (`InvZu`). In particular at every function
    ENTRY reached while no unfinished thread is inside a writer of it, and at every machine of
    a program none of whose running functions writes it. The start memory is the leg's own
    hypothesis: (b) does not demand table invariants at `E.sp0`, and demanding them would drop
    programs the statement covered before. -/
def InvRuheG (P : Programm D) (M0 M : RufMaschineG D) : Prop :=
  ∀ i ∈ D.invs, InvTraeger P i → InvHaelt P i (M0.speicher.welt []) → InvZu M i →
    InvHaelt P i (M.speicher.welt [])

/-- **What a thread holding an invariant's guard observes** (Opus agent D, 2026-09-26): a
    thread `t` that holds a guard lock of a carrier of `i` and has no frame inside a writer of
    `i` sees `i` intact in shared memory -- whatever the other threads do. -/
def InvSichtG (P : Programm D) (M0 M : RufMaschineG D) : Prop :=
  ∀ i ∈ D.invs, InvTraeger P i → InvHaelt P i (M0.speicher.welt []) → ∀ t,
    (∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false) →
    (∃ tb ∈ D.traeger i, ∃ L, Sum.inl L ∈ D.braucht tb ∧ L ∈ offen (M.faeden t).spur) →
    InvHaelt P i (M.speicher.welt [])

/-- **Lock invariants at every lock move** (Opus agent D, 2026-09-26): every step from `M` that
    ACQUIRES `L` starts from a memory where `L`'s invariant holds and leaves one where it holds
    (the section begins with the invariant); every step that RELEASES `L` leaves a memory where
    it holds. -/
def SperrWechselG (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D)
    (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D) (L : D.Lock), RufSchrittG P O passes M u M' →
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      S.inv L M.speicher = true ∧ S.inv L M'.speicher = true) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → S.inv L M'.speicher = true)

/-- **A held lock's invariant is observed by its holder alone** (Opus agent D, 2026-09-26).
    For every step from `M` and every carrier `c` protected by `L`: the step accesses `c` (a
    recorded read or write, or a change of `c`) only if its thread holds `L`; and while a thread
    holds `L`, no other thread's step changes `c`. So the holder may break the invariant inside
    its section, and no other thread can observe that: every observation of `c` lies inside an
    `L`-section of the observer, which began at an acquire where the invariant held
    (`SperrWechselG`) and in which only the observer moved `c`. -/
def SperrSichtG (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D)
    (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D), RufSchrittG P O passes M u M' →
    ∀ (L : D.Lock) (c : D.Tab ⊕ D.Glob), c ∈ S.orte L →
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)
-- END invariant definitions --

/-- **THE GOAL at a reached machine `M` of a run from `M0`**: the four legs, nothing else.
    (Since Opus agent D, 2026-09-26, the contract leg names invariants beyond the returns:
    `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`.) -/
structure Ziel (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : Prop where
  -- memory safety (typing and in-range: intrinsic in `Programm D`)
  speicherSicher : SpurInv M
  -- data-race freedom
  rennfrei : RennfreiBis P O passes M0 M
  -- the weak memory adds no behaviour (DRF theorem; weak-memory hunk, Opus agent B 2026-09-26)
  schwach : SchwachSC P O passes M0 M
  -- contracts where claimed
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  -- invariants beyond the returns (Opus agent D, 2026-09-26)
  invRuhe : InvRuheG P M0 M
  invSicht : InvSichtG P M0 M
  sperrWechsel : SperrWechselG P O passes S M
  sperrSicht : SperrSichtG P O passes S M
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
    * `fortschritt` -- every stop is named (`FortschrittF`);
    * `spawnSicht` (Opus agent D, 2026-09-26) -- a step that makes a dormant slot live leaves
      the G state alone, and there the spawned thread holds no lock, every free lock has its
      invariant and every closed table invariant holds: its entry sees the invariants. -/
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
  -- a spawned thread's entry sees the invariants (Opus agent D, 2026-09-26)
  spawnSicht : ∀ (K' : FadenMaschine D) (t : Faden), FadenSchritt P O passes K K' →
    K.lebt t = false → K'.lebt t = true →
      K'.m = K.m ∧ (∀ L, L ∉ offen (K'.m.faeden t).spur) ∧ SperrInvG S K'.m ∧
        InvRuheG P M0 K'.m

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


/-! ## Linking separately compiled units (Opus agent E, 2026-09-26)

    `GabbroZiel` is about ONE `Einheit`. A program linked from two separately compiled units is
    stated here as a SECOND statement, `GabbroZielVerbund`, whose conclusion is `ZielF` on the
    LINKED unit `verbinde e E₁ E₂` and whose premises are per unit, plus the link check and the
    SAME hardware assumptions. See "WHAT CHANGED ON 2026-09-26 (OPUS AGENT E)" in the header. -/

/-- The program with the contracts of `P` and the bodies `r`. -/
def mitRumpf (P : Programm D)
    (r : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))) :
    Programm D :=
  { P with rumpf := r }

section Verbund

variable [DecidableEq D.Fn]

/-- **The linked program**: every function's body comes from its OWNER -- unit 1 owns `f` iff
    `e f`, unit 2 the rest -- and the contracts are the link declaration's (`Verbindbar` makes
    the two units' contracts one). -/
def verbindeP (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Programm D :=
  mitRumpf E₁.P (fun f => if e f then E₁.P.rumpf f else E₂.P.rumpf f)

/-- **The linked unit** `verbinde e E₁ E₂`: the linked program, the (shared) lock invariants,
    initial memory and axiom ensures, and BOTH units' declared starts and run-time roots. -/
def verbinde (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Einheit D where
  P := verbindeP e E₁ E₂
  S := E₁.S
  Q := E₁.Q
  starts := E₁.starts ++ E₂.starts
  sp0 := E₁.sp0
  gestartet := E₁.gestartet ++ E₂.gestartet

/-- The OWNER's program of `f` (unit 1 iff `e f`). -/
def teilP (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (f : D.Fn) : Programm D :=
  if e f then E₁.P else E₂.P

/-- **One link declaration** for both units: the two units are checked over ONE `Deklaration`
    (the union of their declarations: types, carriers, locks, signatures with their effects,
    axioms; `gabbro abi` / `--with` hand the importer only the EXPORTED part of it, and each
    Rust unit is checked over its own view, not over the union -- review E, F2), and they agree on everything that is not a
    body: every function's `requires`/`ensures` (so the importer relies on EXACTLY the
    exporter's contract; the Rust `N501`-`N503` refuse a head that differs), every table
    invariant, the lock invariants and the declared initial memory. The hardware assumptions
    are NOT here: `GabbroZielVerbund` names their equality as a premise of its own. -/
structure Verbindbar (E₁ E₂ : Einheit D) : Prop where
  invariante : E₁.P.invariante = E₂.P.invariante
  requires : E₁.P.requires = E₂.P.requires
  ensures : E₁.P.ensures = E₂.P.ensures
  sperren : E₁.S = E₂.S
  speicher : E₁.sp0 = E₂.sp0

/-- **A unit's placeholders are leaves**: every function the unit does not own (`eigen f =
    false`) calls nothing in the unit's own program. That is the `extern fn` of the importer:
    a head with the contract and the effects, and no body the checker could follow. -/
def Platzhalter (eigen : D.Fn → Bool) (P : Programm D) : Prop :=
  ∀ f g, eigen f = false → ruftB P f g = false

/-- **The COMPOSED call graph of a root `w`**, from the two units' own graphs: `h` is reached
    inside the owner of `w`, or `h` is reached inside the owner of a function `f` of the OTHER
    unit that the owner of `w` reaches (an import). The linker computes it from the units'
    summaries; no body crosses the boundary. -/
def HuelleV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w h : D.Fn) : Prop :=
  (e h = e w ∧ reachB (teilP e E₁ E₂ w) fs w h = true) ∨
  ∃ f, e f ≠ e w ∧ e h = e f ∧ reachB (teilP e E₁ E₂ w) fs w f = true ∧
    reachB (teilP e E₁ E₂ f) fs f h = true

/-- **No callback through an import**: the owner's graph of an imported function stays inside
    its owner. -/
def KeinRueckruf (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Prop :=
  ∀ w f h, e f ≠ e w → reachB (teilP e E₁ E₂ w) fs w f = true →
    reachB (teilP e E₁ E₂ f) fs f h = true → e h = e f

/-- A carrier some function relies on as THREAD-LOCAL: it is in the function's footprint (or a
    register's device carriers), no signature lock guards it there, and (for the footprint) no
    lock invariant protects it -- the one case in which `FussS` asks for `lokW`. -/
def LokBedarf (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ f, (c ∈ fussOrte (teilP e E₁ E₂ f) f ∧ sigB f c = false ∧
      ¬ ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L) ∨
    (c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger ∧ sigB f c = false)

/-- `Getrennt` over the COMPOSED hulls: the footprint leg of race freedom across the link. -/
def GetrenntV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, HuelleV fs e E₁ E₂ w₁ f →
    c ∈ fussOrteG (teilP e E₁ E₂ f) f → HuelleV fs e E₁ E₂ w₂ g → TraegerSchreibt g c = false

/-- `SchreibGetrennt` over the COMPOSED hulls: the write leg of race freedom across the link. -/
def SchreibGetrenntV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (ws : List D.Fn)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, HuelleV fs e E₁ E₂ w₁ g → TraegerSchreibt g c = true →
    ∀ h, HuelleV fs e E₁ E₂ w₂ h → TraegerSchreibt h c = false ∧ c ∉ fussOrteG (teilP e E₁ E₂ h) h

/-- `PoolSicher` over the COMPOSED hull of a routine declared twice. -/
def PoolSicherV (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, HuelleV fs e E₁ E₂ w f → ∀ c,
    TraegerSchreibt f c = true → (∃ L, Bewacht c L) ∨ AtomarAusgenommen c

/-- **THE LINK CHECK** (decided exactly by `schnittstelleB`, Zielsatz/Verbund.lean). The
    interface of a unit carries its call graphs and its per-function footprints and writes (the
    effects of an exported head); the check composes them:
    * `blatt₁`, `blatt₂` -- each unit's placeholders for the other's functions are leaves;
    * `keinRueckruf` -- an imported function's graph stays in its owner;
    * `lok` -- every carrier some function relies on as thread-local IS thread-local among the
      linked unit's thread roots, over the composed hulls (footprints compose);
    * `renn` -- every unguarded, non-atomic carrier is write-separated over the composed hulls;
    * `einzeln` -- a routine declared twice in the linked unit is pool-safe over its composed
      hull (a routine both units start counts twice).
    Every per-body component of `AkzeptiertSpec` (fragment, closed graphs, lock floors, lock
    invariant places, roots, answer sites) is each unit's own verdict; these three are the
    whole-program components, and they are the ones the link re-decides. -/
structure SchnittstelleSpec (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Prop where
  blatt₁ : Platzhalter e E₁.P
  blatt₂ : Platzhalter (fun f => !e f) E₂.P
  keinRueckruf : KeinRueckruf fs e E₁ E₂
  lok : ∀ c, LokBedarf e E₁ E₂ c → GetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
    SchreibGetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  einzeln : ∀ w, Mehrfach (verbinde e E₁ E₂).ws w → PoolSicherV fs e E₁ E₂ w

/-- **The user's logic of ONE unit** (the part of (b) a separately compiled unit owes): the
    bodies it OWNS at every budget, its lock and axiom families read only their carriers, and
    its start obligation. A placeholder owes nothing -- its owner proves the body. -/
structure NutzerTeil (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutS E.P passes E.Q E.S f ∧ InvGutS E.P passes E.Q E.S f ∧
        InvGutGrund E.P passes E.Q E.S f) ∧
    SperrInvLokal E.S ∧ AxEnsLokal E.Q
  start : StartPflicht E

end Verbund

/-- **GABBRO_ZIEL FOR LINKED UNITS** (2026-09-26, Opus agent E). Two units `E₁`, `E₂` over one
    link declaration, unit 1 owning the functions where `e` holds:
    (a) each unit is accepted by the checker ALONE, and the link check holds;
    (b) each unit's user proves the logic of the bodies IT owns, and its start;
    (c) the hardware meets the assumptions, and they are the SAME for both units
        (`E₂.Q = E₁.Q`: one oracle answers both units' axioms);
    (d) the runtime starts the LINKED unit.
    Then every leg of `ZielF` holds on every reachable thread machine of the linked program --
    race freedom and lock discipline ACROSS the units, spawned threads and the weak-memory leg
    included, since the conclusion is `GabbroZiel`'s own. -/
def GabbroZielVerbund : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E₁ fs.1 ls.1 cs.1 = true →                    -- (a) unit 1, alone
    C.akzeptiert E₂ fs.1 ls.1 cs.1 = true →                    -- (a) unit 2, alone
    Verbindbar E₁ E₂ →                                          -- (a) one link declaration
    SchnittstelleSpec fs.1 e E₁ E₂ →                            -- (a) the link check
    NutzerTeil e E₁ →                                           -- (b) unit 1's user
    NutzerTeil (fun f => !e f) E₂ →                             -- (b) unit 2's user
    E₂.Q = E₁.Q →                                               -- (c) the SAME hardware assumptions
    ∀ O : Orakel D, HardwareAnnahmen O E₁.Q →                   -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (verbinde e E₁ E₂) sp init →                     -- (d) the runtime, linked
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbar (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
          (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K →
          ZielF (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
            (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) K

end Gabbro.Grammatik.Zielsatz
