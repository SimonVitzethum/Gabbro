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
  Then for every budget and every reached machine: `Ziel`. `fs`/`ls`/`cs` (functions, locks,
  carriers) are `Aufzaehlung`s (complete by their type: finite declarations only).

  WHAT CHANGED ON 2026-09-15, AND WHY (third Opus verdict, URTEIL-OPUS-2026-09-15.md):
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
  * (c) `AxVertragO E.Q O` -- every axiom answer meets the `ensures` the program declares for
    it. That is the contract of foreign code or a device, which the user writes and nothing
    checks: a false `E.Q` is a false NAMED assumption (visible in the declaration), and
    `Q := false` makes (c) unsatisfiable, the honest kind of vacuity.
  * (d) `Laufzeit.lader` -- the loader establishes the program's declared initial memory
    `E.sp0` (initialized data and zeroed storage of the emitted C). A toolchain/loader fact;
    that `E.sp0` meets the lock invariants and start `requires` is the USER's `StartPflicht`.
  * (d) `Laufzeit.start`/`.einmal` -- the runtime starts exactly the declared starts, each on
    its own thread with its declared arguments, and the idle root `none` (MitRuhe.lean: body
    `return`, empty signature, no lock, no reason, writes nothing) on every other thread;
    the statement covers every assignment running some of the declared starts this way.
    Thread creation is the runtime's (the emitted `main`/boot code), not user logic. The
    machine runs `E.P.mitRuhe`, whose `some f` IS `f` of `E.P`: every checker fact transfers
    (`akzeptiertSpec_mitRuhe`, `akzeptiert_mitRuhe`) and every function behaves as in `E.P`
    (MitRuheSemantik.lean).
  * Not premises, but assumptions of the reading: machine G is the meaning of the C
    (translation validation, PLAN-UEBERSETZUNGSVALIDIERUNG); the hardware is DRF-SC.

  WHAT `Ziel` ADDS OVER `NutzerPflicht` (leg by leg). The user proves SEQUENTIAL per-function
  facts: each body, run alone by `execEndH` against every callee answer meeting the callee's
  contract and frame, every register/axiom answer in the (c) class, and every lock move
  keeping the invariant, ends in its `ensures` and owed invariants, meets each callee's
  `requires`, and never ends in `logik`; plus the start obligation. `Ziel` speaks about the
  INTERLEAVED machine G:
  * `speicherSicher` (`SpurInv`) -- NOT in (b) at all: every access in every run carries its
    carrier's guards and those locks are really held. From the checker and G.
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
  * `keineVerklemmung`, `fortschritt` -- NOT in (b): no deadlock from lock ranks, and G
    never stops silently (every thread finished, waiting, at a NAMED hardware stop, or able
    to step). This also keeps the safety legs from being vacuous by G getting stuck.
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
  * `execStmt` Semantik:574, `keinRuf` Maschine:383, `Stmt.istBlatt` Maschine:392 -- one
    statement sequentially; leaves are what G runs in one step / wrong leaves = wrong steps.
  * `execEndH` SperreSem:363, `HavocOk` :71, `SperrInv` :45 -- the sequential body semantics the
    user proves against: `locks L` runs from any move keeping `S.inv L`, a release checks it /
    if it differs from `execStmt` outside `locks`, the user proves the wrong body.
  * `World` Semantik:77 (slots total over `Int`; in-range is the TYPE of `.index` values),
    `Speicher` Maschine:359, `Orakel` Semantik:355, `Faden` Wettlauf:46 (= Nat, all started).
  * `Deklaration.mitRuhe`, `Programm.mitRuhe`, `Orakel.mitRuhe`, `SperrInv.mitRuhe`, `fsRuhe`,
    `wsRuhe`, `speicherR` :268, `envR` :280 MitRuhe.lean -- the idle root added, signature
    numbers and function-pointer types shifted by one, every body translated constructor by
    constructor, memory and arguments carried over / a translation that changed a body would
    make every leg speak about another program.
  Premise definitions:
  * `Einheit`, `Einheit.ws` (here) -- the program as one declaration / a field the exporter
    does not fill from the source would make the statement about another program.
  * `GutO` Satz:965 -- axioms stay in their declared write frames, keep held locks and trace.
  * `RegLokal` ZielOrtGeraetSem:48 -- register/visibility answers depend only on declared carriers.
  * `AxVertragO`/`AxEnsLokal`/`AxEns` AxiomVertrag:50/56/44 -- axiom answers meet the declared
    `ensures`; the declared ensures reads only the axiom's write carriers.
  * `KoerperGutS` SperreFuss:374 -- per function, sequential: triple, caller duty, no `logik`
    outcome, against every frame-respecting handler (`RespektiertRahmen` ZielOrtRahmenSem:48,
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
  * `Eintritt`/`SegLauf`/`aktivVor`/`segZaehle`/`kostenTief`/`rufTief` KostenG:788/740/776/750/955/964.
  NEW here: `Einheit`, `LogikPflicht`, `StartPflicht`, `Laufzeit` (2026-09-15); `InvGutGrund`,
  `InvAmGrundG` (invariants at REASON exits), `HaltBenannt` (the named stops), `RennfreiBis`
  (DRF for every non-atomic carrier), `Getrennt`, `SchreibGetrennt` (write separation of
  unguarded carriers, the counterpart of `H013`; with it `rennfreiBis_of`, Akzeptiert.lean,
  proves `RennfreiBis`), `Ruhig` (an idle start writes NOTHING), `AkzeptiertSpec`,
  `StartZulaessig` (derived, not a premise), `Ziel`, `GabbroZiel`.

  REVIEW QUESTIONS. 1. Does `Ziel` say the four legs, nothing weaker (see WHAT `Ziel` ADDS)?
  2. Is every premise in exactly one group? The start conditions are (b) (`StartPflicht`)
  and (d) (`Laufzeit`) since 2026-09-15; nothing else restricts the quantified runs.
  3. Can a user-controlled choice empty an obligation? Probes A/D: closed by `NutzerPflicht`
  at every budget. An unsatisfiable lock family or start `requires`: closed, it refutes (b)
  (`unerfuellbar_widerlegt`, `start_req_widerlegt`). The run class is never empty: the root
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
  side; `gleitkomma_ieee` is on the C side); starvation freedom; invariants at entry or while
  locks are held (claimed at returns only); one thread per busy start (SMP-symmetric code
  running one start on several cores is outside (d)). Declared `costs` are not in
  `Deklaration`: `zeit` is the syntax-computed bound. The `.gab` -> `Einheit` step is the
  exporter's (lean_g.rs), which today fills neither `starts` nor `sp0` nor the source
  `requires`: the programs `GabbroZiel` covers are reached by hand-written terms.

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
    * `sp0` -- the declared initial memory (every table and global initializer).
    The exporter's output is exactly one such value; a different `starts` (say `[]`) is a
    DIFFERENT program, whose run the statement then describes (`laufzeit_nur_erklaert`). -/
structure Einheit (D : Deklaration) where
  P : Programm D
  S : SperrInv D
  Q : AxEns D
  starts : List (Σ w : D.Fn, Env D (D.params w))
  sp0 : Speicher D

/-- The declared start functions. -/
def Einheit.ws (E : Einheit D) : List D.Fn := E.starts.map (·.1)

/-! ## (a) What the checker decides -/

section Pruefer

variable [DecidableEq D.Fn]

/-- Carrier `c` is thread-local among the declared starts `ws`: no start reaches `c` in a
    footprint while a DIFFERENT start can write it (`GetrenntK` over the starts). -/
def Getrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ f g, reachB P fs w₁ f = true → c ∈ fussOrteG P f →
    reachB P fs w₂ g = true → TraegerSchreibt g c = false

noncomputable def lokW (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (Getrennt P fs ws c) (Classical.propDecidable _)

/-- Carrier `c` is WRITE-separated among the declared starts `ws`: if one start's call graph
    may write `c`, no DIFFERENT start's graph may write it or have it in a footprint. -/
def SchreibGetrennt (P : Programm D) (fs ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, w₁ ≠ w₂ → ∀ g, reachB P fs w₁ g = true → TraegerSchreibt g c = true →
    ∀ h, reachB P fs w₂ h = true → TraegerSchreibt h c = false ∧ c ∉ fussOrteG P h

/-- **What `Akzeptiert` must establish** (the Props of its components): fragment; closed call
    graphs; every footprint carrier signature-guarded, lock-protected or thread-local; lock
    floors; protected carriers guarded by their lock; declared starts hold no lock by
    signature, have no reasons, and are pairwise distinct; every carrier without a guard
    lock that is not `atomic` is write-separated among the declared starts (the counterpart
    of the checker's `H013`; publish payloads INCLUDED since 2026-09-15, verdict P3). -/
structure AkzeptiertSpec (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussS P S (lokW P fs ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : ws.Nodup
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c

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
  req : ∀ a ∈ E.starts, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2

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
    * `einmal` -- no declared start runs on two threads.
    The runtime starts EXACTLY the declared starts, each on its own thread, the root on every
    other thread (`initRuhe E.starts`); that start meets this predicate whenever the checker
    accepts (`laufzeit_initRuhe`, Zielsatz/Proben.lean), and so does every assignment running
    only some of the declared starts. -/
structure Laufzeit (E : Einheit D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) : Prop where
  lader : sp = speicherR E.sp0
  start : ∀ t, init t = ⟨none, .nil⟩ ∨ ∃ a ∈ E.starts, init t = ⟨some a.1, envR a.2⟩
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → (init t).1 = none

/-! ## The start the proof works with (derived from (b) and (d), not a premise) -/

section Start

variable [DecidableEq D.Fn]

/-- An idle start: no signature lock, no reasons, every function it reaches has an empty
    footprint and writes nothing. Any number of threads may run it. -/
def Ruhig (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Prop :=
  D.haelt w = [] ∧ D.gruende w = 0 ∧ ∀ f, reachB P fs w f = true →
    fussOrteG P f = [] ∧ ∀ c, TraegerSchreibt f c = false

/-- **Admissible starts** (the proof's notion; NOT a premise of `GabbroZiel` since
    2026-09-15): every thread runs a declared start (each on ONE thread) or an idle one; the
    start functions' `requires` and every lock invariant hold at the start memory.
    `startZulaessig_aus` (Zielsatz/Beweis.lean) derives it from (b) and (d). -/
structure StartZulaessig (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop where
  wurzel : ∀ t, (init t).1 ∈ ws ∨ Ruhig P fs (init t).1
  einmal : ∀ t u, t ≠ u → (init t).1 = (init u).1 → Ruhig P fs (init t).1
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

/-- The first layer of the head block answers a HARDWARE outcome at the world `σ`: a leaf's
    hardware outcome, an axiom answer outside its type, a register answer outside its type or
    against its promise, an invisible `awaits`, a float result outside its range. Exactly the
    failing side conditions of `blatt`/`dannBlatt`, `dannBindAxiom`, `dannRegLies*`,
    `dannAwaits`, `dannGleit*`. -/
def KopfHardware (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (σ : World D) (ρ : Env D Γ) : Block D V l Γ Λ Λ' → Prop
  | .cons s _ => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .bindAxiom a args .. =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
  | .regLies r .. => ∀ v, einpassen (D.rtyp r) (O.regLies r σ) = some v → D.rzusage r v = false
  | .regLiesElse r .. => einpassen (D := D) (D.rtyp r) (O.regLies r σ) = none
  | .awaits g .. => O.sichtbar g σ = false
  | .gleit op a b lo hi _ =>
      gleitPasst lo hi (gleitRechne op (eval (σ.lese Λ (a.orte ++ b.orte)) a
        (σ.lese Λ (a.orte ++ b.orte)) ρ).x (eval (σ.lese Λ (a.orte ++ b.orte)) b
        (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = none
  | .gleitLit q lo hi _ => gleitPasst lo hi (bruch q) = none
  | .gleitVon e lo hi _ =>
      gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = none
  | _ => False

/-- A residue at a named hardware stop: a spent `forever` budget (`hardware fortschritt`), or
    its head block's first layer answers hardware. -/
def RestHardware (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (σ : World D) (ρ : Env D Γ) : GRest D V l Γ Λ → Prop
  | .ewig _ 0 _ _ _ => True
  | .ende (.cons s _) => s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .dann b _ => KopfHardware O passes σ ρ b
  | _ => False

/-- Thread `t` stands at a named stop: a named hardware assumption fails at its head. -/
def HaltBenannt (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ ∧ RestHardware O passes (M.weltVon t) ρ r

/-- **Every stop is named**: each thread is finished, waits for a lock another thread holds,
    stands at a named hardware stop, or can step. -/
def FortschrittG (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t, FertigG M t ∨ WartetG M t ∨ HaltBenannt O passes M t ∨ ∃ M', RufSchrittG P O passes M t M'

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
  fortschritt : FortschrittG P O passes M
  -- time
  zeit : ZeitAb P O passes M

/-- **GABBRO_ZIEL.** -/
def GabbroZiel : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflicht E →                                           -- (b) the user, on E
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ M : RufMaschineG D.mitRuhe,
        RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M →
          Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M

end Gabbro.Grammatik.Zielsatz
