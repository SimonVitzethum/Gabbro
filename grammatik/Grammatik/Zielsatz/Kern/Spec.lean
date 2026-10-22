/-
  File:    Grammatik/Zielsatz/Kern/Spec.lean -- THE GOAL AS STATEMENTS. Definitions only, no proof. Review target:
           every extension of the goal is a reviewed diff of this file. The history of this header (the review
           rounds, the lanes and agents that moved the statement, every superseded form) is in git:
           `git log -p -- grammatik/Grammatik/Zielsatz/Kern/Spec.lean`.

  GOAL (Simon): a Gabbro user proves only their own logic plus named hardware assumptions; memory safety, race
  freedom, contracts where claimed -- in concurrent runs too -- and time are carried by the language.

  THE STATEMENTS (proofs in Zielsatz/Atomar/BeweisAtomar.lean; `#print axioms` of each is exactly `propext`,
  `Classical.choice`, `Quot.sound`):
  * `GabbroZiel` -- safety, on every reached machine: the legs of `ZielFX` (below). Proof `gabbro_ziel`.
  * `GabbroZielSC` -- the same over machine G without the atomic rely; a corollary (`gabbro_ziel_sc_aus`), kept as a
    name because corpus theorems and embeddings are stated over it.
  * `GabbroZielVerbund` -- a program LINKED from two separately compiled units, each accepted alone, under the link
    check `SchnittstelleSpec` and the SAME hardware assumptions; conclusion `ZielF` on the linked unit
    (`gabbro_ziel_verbund`).
  * `GabbroZielLeben` -- liveness: on every weakly fair run of the ticket lock a thread standing at `locks L` takes
    `L`, or some thread holds `L` from some step on for ever (`gabbro_ziel_leben`).
  * `GabbroZielTerminierung` -- termination: under the measure duty (`decreases`, user logic), on every infinite run
    of machine GX every thread takes only finitely many steps, and a thread whose start the algorithm `klasse` puts
    in class `endet` never stands at a spent `forever` budget (`gabbro_ziel_terminierung`, proof in
    Zielsatz/Atomar/BeweisTerminierung.lean). See TERMINATION below.
  What may be said: "the goal theorem is proved over the model, with witnesses and non-degeneracy". What may NOT be
  said: "Gabbro is verified" -- the checker inside the statement is the Lean Bool, not the Rust checker, and no
  bridge from the model to a binary is built (THE READING, below).

  THE SHAPE. Everything is about ONE value `E : Einheit D`, the program the user wrote: code with contracts `E.P`,
  lock invariants `E.S`, the axioms' declared `ensures` `E.Q`, declared starts with arguments `E.starts`, run-time
  roots `E.gestartet`, the declared initial memory `E.sp0`. Four premise groups:
  (a) `C.akzeptiert E fs ls cs = true` -- ONE Bool of a checker `C : PrueferX`, sound against `AkzeptiertSpecX`
      (fragment, closed call graphs, footprints local/guarded/admitted shared atomics, lock floors, lock places,
      lock-free starts, pool safety, write separation, answer sites, masking discipline). The concrete checker is
      `akzeptiertX_pruefer` (Zielsatz/Atomar/AtomarZiel.lean), deciding `AkzeptiertX`. `fs`/`ls`/`cs` are complete
      enumerations (finite declarations only).
  (b) `NutzerPflichtA E` -- the user's logic: every body, SEQUENTIALLY, at every `forever` budget, against every
      callee answer meeting the callee's contract and frame, every oracle answer of class (c), every lock move
      keeping the invariant (`HavocOk`), and every value a read of an admitted shared atomic may return (the rely):
      its `ensures` and owed invariants at value and reason exits, every callee's `requires`, no `logik` outcome
      (`LogikPflichtA`); and the start (`StartPflicht`: the lock invariants at `E.sp0`, every root's `requires`
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
    all its bytes in its table's region; different cells share no byte (Speichermodell/Adressen/). (c).
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
  * `invRuhe`, `invSicht` -- a table invariant holds wherever no unfinished thread is inside one of its writers,
    and for a thread holding one of its guards outside every writer (hypothesis: it held at the start). (a), (b).
  * `keineVerklemmung`, `keinZyklus` -- no global deadlock, no wait cycle (lock ranks). (a).
  * `keinKernHalt` (`KernHaltEA`) -- for every core assignment and every run the core hardware admits (`KernPlan`,
    inside the leg), a thread whose root the program declares an interrupt handler never stands at a lock another
    thread of its core holds. (a): the masking discipline.
  * `fortschritt` -- every thread is finished, waits for a lock, stands at a NAMED stop, or can step (SAFETY: no
    unnamed stuck state). (a), (b), (c).
  * `zeit` -- a frame with a finite call tree takes at most `kostenTief` own steps while active. --.
  * `folge` -- the order of calls in every thread's call log, for every order specification the program passes
    (Folge.lean). --.
  * on the thread machine: `schlafendUnberuehrt`, `schlafendFrei`, `joinFrei` (dormant and joining threads hold
    nothing), `keineVerklemmung`/`keinZyklus` with join waits, `fortschritt` with the join wait, `spawnSicht` (a
    spawn leaves the G state alone, the new thread holds nothing, every free lock and closed invariant holds).
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
    (5) what G reads without recording it -- foreign answers (`Orakel.wirkt`), register reads, the visibility of
        `awaits` -- is read over G's memory: the last executed write, not an older message.

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
  (`massPflicht_mitRuhe`). Claimed: (1) on every infinite GX run from the runtime's start every thread takes only finitely many steps
  -- a `forever` is finite here because machine G grants `passes` passes from outside; (2) a thread whose start
  function the decision algorithm `klasse` (Logik/Terminierung/Klasse.lean: `endet`, `umgebung`, `bedingt`,
  `abgelehnt`, computed from the syntax) puts in class `endet` never stands at a spent budget: its end does not
  lean on the passes. Classes `umgebung` and `bedingt` are finite per pass (`durchgang_schritte`), not in this
  statement.

  NOT CLAIMED:
  * a waiting bound, a time bound for `forever` or recursion, termination of `umgebung`/`bedingt` beyond the budget
    (whether a `leave` guard or a base path is ever taken is the program's question); termination with threads
    spawned at run time; `GabbroZielLeben` claims that a
    lock wait ends unless a holder never lets go, not when, and not for runs over GX or with threads spawned at run
    time;
  * stack depth (G's stacks are unbounded; the LLVM lowering runs recursion without native stack growth, and
    exhausted memory fail-stops -- outside the model);
  * the compiled code and the hardware (THE READING); that the compiler's byte layout is a `LayoutOk` one;
  * reads in their extents as a statement about runs (they are, by the index types); globals and registers have no
    index;
  * that W is exactly the C11 model; a contract, `requires`, `ensures` or invariant over a shared atomic (refused,
    `N484`); the merge discipline of per-core cells beyond reading them (OFFEN O17); linked units sharing an atomic
    across the link; the publish/await hand-off of an unguarded PLAIN payload (refused);
  * floats beyond the kernel IEEE model (that the FPU computes it is `gleitkomma_ieee`, a hardware fact);
  * an invariant inside a running writer or false in the start memory or reading carriers outside its declared
    `traeger`; a lock invariant inside its holder's section (claimed: no other thread observes it there);
  * interrupt handlers beyond `KernPlan`: re-entry, handler-on-handler preemption, a thrown entry without `via idt`,
    a lock the unit does not declare (OFFEN O19);
  * an order of effects that are not calls of Gabbro functions, an order across a compound statement, an indirect
    call or a lock block, the entry of a `ruf` function run as a thread start, an order "sometime before", the
    promises of `breaking I` about its name (OFFEN O1);
  * a routine declared ONCE running on several threads (outside (d));
  * for linked units: differing hardware assumptions, a callback through an import, an importer relying on a
    contract other than the exporter's, dynamic loading, linking of foreign code below the ABI, the link step
    itself;
  * for threads spawned at run time: arguments per spawn, a root `requires` holding only at the spawn world,
    `old`-reads at the spawn world, the end of a join wait, the child's stack, a failing spawn, the lowering of the
    spawn;
  * dynamic data structures without a declared ceiling (OFFEN O29; an arena with ceiling `M` is a table of `M`
    slots, and the exporter refuses `grow`, `LG005`); probabilistic statements (OFFEN O29);
  * every program the certificate register lists as UNCERTIFIED, by name.

  KNOWN DEBT. There is no definition-only layer: the goal predicates live in mixed files (ZielOrt, SperreFuss,
  SperreMaschine, Verklemmung, RennfreiVoll, KostenG, …), and the import closure includes witness files. To do:
  every definition this file reads out of its proof file.
-/
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
import Grammatik.Logik.Fortschritt.KostenG
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuhe
import Grammatik.Logik.Vertraege.AntwortOrte
import Grammatik.Speichermodell.Maschine.MaschineW
import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMaschine
import Grammatik.Speichermodell.Maschine.GXMaschine
import Grammatik.Logik.Fortschritt.Folge
import Grammatik.Logik.Ruf.Maschine.BudgetMonoton
import Grammatik.Logik.Fortschritt.PlanLauf
import Grammatik.Speichermodell.Adressen.Layout
import Grammatik.Logik.Terminierung.LaufGX

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

-- BEGIN handler discipline (Opus agent H, 2026-09-26, OFFEN O19) --
/-- The feature set "every call, every signature, and ONLY locks declared `masks irqs`": a body
    admitted by it takes no lock that leaves interrupts on. -/
def NurMaskiert (D : Deklaration) : Merkmal D :=
  ⟨fun _ => true, fun _ => true, fun L => D.maskiert L⟩

/-- **The masking discipline of an interrupt handler** (the Rust `H102`, `kontexte.rs`): every
    function of the call graph of a root `w` the program declares entered by hardware
    (`P.unterbricht w`, `entry … via idt`) takes only locks declared `masks irqs`. -/
def MaskenDisziplin [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) : Prop :=
  ∀ w, P.unterbricht w = true → ∀ f, reachB P fs w f = true → mE (NurMaskiert D) (P.rumpf f) = true
-- END handler discipline --

/-- **What `Akzeptiert` must establish** (the Props of its components): fragment; closed call
    graphs; every footprint carrier signature-guarded, lock-protected or thread-local; lock
    floors; protected carriers guarded by their lock; declared starts hold no lock by
    signature and have no reasons, and a start declared twice is pool-safe (`EinzelnPool`,
    since fix lane F10 -- before: pairwise distinct, `ws.Nodup`); every carrier without a guard
    lock that is not `atomic` is write-separated among the declared starts (the counterpart
    of the checker's `H013`; publish payloads INCLUDED since 2026-09-15, verdict P3); no body
    calls an axiom or reads a register at a declared answer type without a value, except an
    axiom whose result is `never` (`antworten`, since 2026-09-15, W1); every function an
    interrupt handler's call graph reaches takes only locks declared `masks irqs` (`masken`,
    since 2026-09-26, Opus agent H: the Rust `H102`). -/
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
  -- the handler discipline `H102` (Opus agent H, 2026-09-26, OFFEN O19)
  masken : MaskenDisziplin P fs

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
          execEndH (V := vertragVon D f) S O' U passes R (P.rumpf f) σ ρ = EndAusgang.why σ' r →
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
      ev = RufEreignisF.why g rho r s0 s1 → InvAmRueck P g s1

/-- **The kinds of named stop** (2026-09-15, verdicts F1 and F3, finding G1). Each is a place
    where G has no rule for a thread and the statement reports it instead of claiming more:
    * `hardware` -- a hardware assumption of (c) fails at the head: an axiom (foreign code)
      answered outside its (answerable) type, a register (a device) outside its type or
      against the promise its declaration makes;
    * `nieZurueck` -- the head calls an axiom whose declared result is `never`: the call does
      not return;
    * `flagge` -- a WAIT for a publication: the head is `awaits g` and `g` is not visible;
    * `budget` -- the `forever` budget is spent: G's finite stand-in for a loop the program runs
      without end (not final: the leg `budgetUnecht`).
    An out-of-range float is NOT a stop any more: it is `Logik.bereich`, excluded by the
    user's obligation, and no reachable machine stands at one (verdict F1). -/
inductive HaltArt where
  | hardware
  | flagge
  | budget
  /-- The head is a call of an axiom whose DECLARED result is `never` -- the call does not
      return. That is the declaration's promise (the lowering marks the call `noreturn`), and
      the code after the call is unreachable in the binary as in G; the
      obligation (b) still covers everything before the call. NEW 2026-09-15 (round-5
      finding G1): before, this stop was filed as `hardware`, as if the machine had answered
      outside a type that has no inside. NARROWED 2026-09-15 (round-6 finding W1): every
      other empty answer type (`.why 0`, an empty range, a sum without a value, a pointer
      type no function has, at an axiom or a register) is refused by the checker
      (`AkzeptiertSpec.antworten`), because there the compiled call returns. -/
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
  | .hardware, .regRead r .. =>
      (∀ v, einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v → D.rzusage r v = false) ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .hardware, .regReadElse r .. =>
      einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r σ) = none ∧
      ¬ AntwortLeer D (some (D.rtyp r))
  | .nieZurueck, .bindAxiom a .. => D.aerg a = some .never
  | .hardware, .bindAxiomElse a args .. =>
      (axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
  | .flagge, .awaits g .. => O.sichtbar g σ = false
  | _, _ => False

/-- A residue at a named stop of kind `k`: a spent `forever` budget (`budget`), a leaf's
    hardware outcome at the end block's head (`hardware`), or its head block's first layer. -/
def RestHalt (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (σ : World D) (ρ : Env D Γ) : HaltArt → GRest D V l Γ Λ → Prop
  | .budget, .ewig _ 0 _ _ _ => True
  | .hardware, .ende (.cons s _) =>
      s.istBlatt = true ∧ ∃ h, execStmt O passes keinRuf s σ ρ = .hardware h
  | .hardware, @GRest.ende _ _ _ _ Λ (.bindAxiom a args ..) =>
      (axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none ∧
      ¬ AntwortLeer D (D.aerg a)
  | .nieZurueck, .ende (.bindAxiom a ..) => D.aerg a = some .never
  | .hardware, @GRest.ende _ _ _ _ Λ (.bindAxiomElse a args ..) =>
      (axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = none
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
    G run. `kern t` is the core thread `t` runs on, `H g` says `g` is an interrupt handler (in
    the leg of `Ziel`: `HandlerVon`, the roots the program declares `via idt`, since Opus agent
    H 2026-09-26).
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

-- BEGIN handler leg (Opus agent H, 2026-09-26, OFFEN O19) --
/-- **Thread `t` is an interrupt handler of the program** (Opus agent H, 2026-09-26): its root --
    the function it started with at `M0` -- is one the program declares entered by hardware
    (`P.unterbricht`, the exported `entry … via idt`). Read off the unit, not chosen by the
    prover; the runtime's idle root is never one (`Programm.mitRuhe`). -/
def HandlerVon (P : Programm D) (M0 : RufMaschineG D) (t : Faden) : Prop :=
  P.unterbricht (M0.faeden t).kopf.f = true

/-- **No same-core interrupt deadlock** (fix lane F11, 2026-09-22; CONTENTFUL since Opus agent H,
    2026-09-26, OFFEN O19). For EVERY core assignment `kern` and every run from `M0` to `M` that
    the core hardware admits (`KernPlan`: masking and preemption as named hardware facts), a
    thread whose root the program declares an interrupt handler (`HandlerVon`) NEVER stands at a
    lock that another thread of its own core holds -- the deadlock `H102` refuses in Rust.

    Unlike the leg of F11 (`KernHaltG`, now in Zielsatz/Masken.lean), nothing of the program side
    is a hypothesis here: WHICH threads are handlers comes from the unit (`P.unterbricht`), and
    the masking discipline from (a) (`AkzeptiertSpec.masken`). The leg is FALSE for programs the
    discipline refuses (`kernHaltE_verletzt`, Zielsatz/MaskenZeuge.lean: a handler entering at an
    unmasked lock its core's thread holds), so it is not a theorem about every program: it is
    carried by (a). The one premise left inside is the hardware schedule `KernPlan`, named in the
    header. -/
def KernHaltE (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufG P O passes M0 ms fs n → ms n = M → KernPlan kern (HandlerVon P M0) ms fs n →
    ∀ (g f : Faden) (L : D.Lock), HandlerVon P M0 g → f ≠ g → kern f = kern g →
      AnSperre M g L → L ∉ offen ((M.faeden f).spur)
-- END handler leg --

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
    (Since Opus agent G, 2026-09-26, a fifth group: the order of effects in the call log,
    `folge`, OFFEN O1.)
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
  keinKernHalt : KernHaltE P O passes M0 M
  fortschritt : FortschrittG P O passes M
  -- time
  zeit : ZeitAb P O passes M
  -- the order of effects (Opus agent G, 2026-09-26, OFFEN O1: L50, L52)
  folge : FolgeG P M

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

-- BEGIN atomic-rely definitions (Opus lane O25c, 2026-09-26) --
/-! ## Shared atomics: the rely (Opus lanes O25, O25b, O25c; OFFEN O25, O17)

    The definitions of the atomic-rely block of the header: (a) `AkzeptiertSpecX`/`PrueferX`,
    (b) `NutzerPflichtA`, the legs `ZielX`/`ZielFX` over machine GX, and `GabbroZiel`. Moved here
    from Zielsatz/AtomarPflicht.lean, AtomarAkzeptiert.lean, AtomarZiel.lean,
    AtomarInvarianten.lean and AtomarMasken.lean (lane O25b) unchanged; `SchwachX`, `ZeitAbX`,
    `ZielX`, `FortschrittFX`, `ZielFX` are new (lane O25c). -/

section Atomar

variable [DecidableEq D.Fn]

/-- **The call closure of `w`** (enumeration-free): `w`, and every function a function of the
    closure calls (`ruftB`). -/
inductive Erreicht (P : Programm D) (w : D.Fn) : D.Fn → Prop
  | wurzel : Erreicht P w w
  | ruf {f g : D.Fn} : Erreicht P w f → ruftB P f g = true → Erreicht P w g

/-- **Thread-local among the starts `ws`, over the call closure** (the twin of `Getrennt`,
    Spec.lean, without a member list). -/
def GetrenntR (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ w₁ ∈ ws, ∀ w₂ ∈ ws, (w₁ ≠ w₂ ∨ Mehrfach ws w₁) → ∀ f g, Erreicht P w₁ f →
    c ∈ fussOrteG P f → Erreicht P w₂ g → TraegerSchreibt g c = false

/-- **A shared atomic of the unit**: `atomic`, unguarded, and not thread-local. -/
def GeteiltA (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  AtomarAusgenommen c ∧ (∀ L, ¬ Bewacht c L) ∧ ¬ GetrenntR P ws c

/-- **A shared atomic the checker admits**: shared (`GeteiltA`) and in no contract. -/
def GeteiltV (P : Programm D) (ws : List D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  GeteiltA P ws c ∧ VertragsFrei P c

/-- **(a) with the atomic rely**: `AkzeptiertSpec` with the footprint property `FussSX` over the
    admitted shared atomics `GeteiltV`. Every other field is `AkzeptiertSpec`'s. -/
structure AkzeptiertSpecX (P : Programm D) (S : SperrInv D) (fs ws : List D.Fn) : Prop where
  frag : programmImFragmentG P fs = true
  abg : ∀ w, AbgK P fs (reachB P fs w)
  fuss : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f
  stufen : StufenM P
  sperrOrte : ∀ L c, c ∈ S.orte L → Bewacht c L
  wurzeln : ∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0
  einzeln : EinzelnPool P fs ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrennt P fs ws c
  antworten : ∀ f, ∀ x ∈ (P.rumpf f).ants, StelleOk D x
  -- the handler discipline `H102` (Opus agent H), as in `AkzeptiertSpec`
  masken : MaskenDisziplin P fs

/-- **Race freedom on GA runs** (`RennfreiBis` with `LaufGA`): on every run of GA -- so on the
    G-part of every run of W -- two accesses by different threads to a non-atomic carrier, one
    a write, are ordered through a guard lock. -/
def RennfreiBisGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufGA P O passes M0 ms fs n → ms n = M →
    ∀ (i j : Nat) (c : D.Tab ⊕ D.Glob), i < j → j < n → fs i ≠ fs j →
      ZugriffG (ms i) (ms (i + 1)) (fs i) c → ZugriffG (ms j) (ms (j + 1)) (fs j) c →
      (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) →
      ¬ AtomarAusgenommen c →
      ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j

end Atomar

/-- **A checker for the rely**: its soundness target is `AkzeptiertSpecX`. -/
structure PrueferX where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpecX E.P E.S fs.1 E.ws

/-- **The logic of the bodies with the atomic rely over `T`.** -/
def LogikPflichtA (P : Programm D) (S : SperrInv D) (Q : AxEns D) (T : D.Tab ⊕ D.Glob → Prop) :
    Prop :=
  (∀ (passes : Nat) (f : D.Fn),
    KoerperGutSA P passes Q S T f ∧ InvGutSA P passes Q S T f ∧ InvGutGrundA P passes Q S T f) ∧
  SperrInvLokal S ∧ AxEnsLokal Q

/-- **The user's own logic with the atomic rely**: the rely over the unit's shared atomics. -/
structure NutzerPflichtA [DecidableEq D.Fn] (E : Einheit D) : Prop where
  logik : LogikPflichtA E.P E.S E.Q (GeteiltA E.P E.ws)
  start : StartPflicht E

/-- **Lock invariants at every lock move, over GX steps** (`SperrWechselG` with `RufSchrittGX`). -/
def SperrWechselGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D) (L : D.Lock), RufSchrittGX P O passes Tg M u M' →
    (L ∉ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur →
      S.inv L M.speicher = true ∧ S.inv L M'.speicher = true) ∧
    (L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur → S.inv L M'.speicher = true)

/-- **A held lock's invariant is observed by its holder alone, over GX steps.** -/
def SperrSichtGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ (u : Faden) (M' : RufMaschineG D), RufSchrittGX P O passes Tg M u M' →
    ∀ (L : D.Lock) (c : D.Tab ⊕ D.Glob), c ∈ S.orte L →
      (ZugriffG M M' u c → L ∈ offen (M.faeden u).spur) ∧
      (∀ t, t ≠ u → L ∈ offen (M.faeden t).spur → TraegerGleich M'.speicher M.speicher c)

/-- **No same-core interrupt deadlock, on GA runs** (`KernHaltG` with `LaufGA`). -/
def KernHaltGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (H : Faden → Prop) (Z : Faden → D.Fn → Prop)
    (A : Faden → D.Fn → Merkmal D),
    (∀ t, H t → MerkAbg P (Z t) (A t)) →
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t)) →
    (∀ t, H t → ∀ (f : D.Fn) (L : D.Lock), Z t f → (A t f).sperre L = true →
      D.maskiert L = true) →
    (∀ (t : Faden) (L : D.Lock), ¬ AnSperre M0 t L) →
    ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufGA P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ (g f : Faden) (L : D.Lock), H g → f ≠ g → kern f = kern g →
        AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **No same-core interrupt deadlock, on GA runs** (`KernHaltE` of Opus agent H with `LaufGA`:
    the handlers are the program's own, `HandlerVon`). -/
def KernHaltEA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
    LaufGA P O passes M0 ms fs n → ms n = M → KernPlan kern (HandlerVon P M0) ms fs n →
    ∀ (g f : Faden) (L : D.Lock), HandlerVon P M0 g → f ≠ g → kern f = kern g →
      AnSperre M g L → L ∉ offen ((M.faeden f).spur)

/-- **The weak machine adds no behaviour outside the shared atomics `Tg`, at `M`**. For EVERY
    assignment `ord` of memory orders, every weak state `W` over `M` reached from the weak start
    over `M0`, and every step W takes from there (with its presented memory `σ`): it is a step
    of GX from `M` to the successor's G-part -- machine G whose reads of `Tg` the weak memory
    answers -- and `σ` is G's memory at every carrier outside `Tg`. With `Tg` empty this is
    `SchwachSC` (`schwachSC_of_X`): the DRF theorem. -/
def SchwachX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M0 M : RufMaschineG D) : Prop :=
  ∀ (ord : D.Glob → Speichermodell.Ordnung) (W W' : RufMaschineW D) (u : Faden) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
    RufErreichbarW P O passes ord (RufStartW M0) W → W.g = M →
    SchrittW P O passes ord W u W' σ M'' wahl neu →
    RufSchrittGX P O passes Tg M u W'.g ∧ ∀ c, ¬ Tg c → TraegerGleich σ M.speicher c

/-- **Time over GX**: `ZeitAb` for every run of GX from `M` (the weak memory answering the
    shared atomics). -/
def ZeitAbX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M : RufMaschineG D) : Prop :=
  ∀ (f : Faden) (g : D.Fn) (n : Nat) (rho : Env D (D.params g)) (s0 : World D) (k : Nat),
    rufTief P (n + 1) g = true → Eintritt P f g rho s0 k M →
    ∀ (M2 : RufMaschineG D) (run : SegLaufX P O passes Tg M M2), aktivVorX f k run →
      segZaehleX run f ≤ kostenTief P passes (n + 1) g

/-- **THE GOAL at a machine `M` of a GX run from `M0`, with the shared atomics `Tg`.** -/
structure ZielX (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 M : RufMaschineG D) : Prop where
  speicherSicher : SpurInv M
  rennfrei : RennfreiBisGA P O passes M0 M
  schwach : SchwachX P O passes Tg M0 M
  vertrag : VertragAmOrtG P M
  sperrInv : SperrInvG S M
  invRueck : InvAmOrtG P M
  invGrund : InvAmGrundG P M
  invRuhe : InvRuheG P M0 M
  invSicht : InvSichtG P M0 M
  sperrWechsel : SperrWechselGX P O passes Tg S M
  sperrSicht : SperrSichtGX P O passes Tg S M
  startEnde : StartEndeG P M
  keinStartGrund : KeinStartGrundG M
  keinLogikHalt : KeinLogikHaltG O passes M
  keineVerklemmung : (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t
  keinZyklus : KeinWarteZyklus M
  keinKernHalt : KernHaltEA P O passes M0 M
  fortschritt : FortschrittG P O passes M
  zeit : ZeitAbX P O passes Tg M
  folge : FolgeG P M
  -- memory at addresses (2026-10-22): if foreign code writes inside the declared extents (`ImBereichO`, a named
  -- assumption inside the leg), every cell the run has changed lies in its extent and, under every correct layout,
  -- with all its bytes in the region of its table
  speicherAdressen : ImBereichO O → ∀ (lay : AdressLayout D), LayoutOk lay → ∀ (t : D.Tab) (k : Int) (f : D.Feld t),
    M.speicher.slots t k f ≠ M0.speicher.slots t k f →
      ImBereich D t k ∧ ∀ a, lay.inZelle t k f a → lay.inTabelle t a

/-- **Every stop is named, on the thread machine over GX.** -/
def FortschrittFX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (K : FadenMaschine D) : Prop :=
  ∀ t, K.lebt t = false ∨
    (K.wartet t ≠ [] ∧ (JoinWartet K t ∨
      ∃ K', FadenSchrittX P O passes Tg K K' ∧ K'.m = K.m ∧ K'.wartet t = [])) ∨
    (K.wartet t = [] ∧ (FertigG K.m t ∨ WartetG K.m t ∨ HaltBenannt O passes K.m .flagge t ∨
      HaltBenannt O passes K.m .budget t ∨ HaltBenannt O passes K.m .hardware t ∨
      HaltBenannt O passes K.m .nieZurueck t ∨
      ∃ M', RufSchrittG P O passes K.m t M' ∧
        FadenSchrittX P O passes Tg K ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩))

/-- **THE GOAL on a thread machine over GX.** -/
structure ZielFX (P : Programm D) (S : SperrInv D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) (K : FadenMaschine D) : Prop where
  g : ZielX P S O passes Tg M0 K.m
  schlafendUnberuehrt : ∀ t, K.lebt t = false → K.m.faeden t = M0.faeden t
  schlafendFrei : ∀ t, K.lebt t = false → ∀ L, L ∉ offen (K.m.faeden t).spur
  joinFrei : ∀ t, K.wartet t ≠ [] → ∀ L, L ∉ offen (K.m.faeden t).spur
  keineVerklemmung : (∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) →
    ∀ t, K.lebt t = true → FertigG K.m t
  keinZyklus : KeinWarteZyklusF K
  fortschritt : FortschrittFX P O passes Tg K
  spawnSicht : ∀ (K' : FadenMaschine D) (t : Faden), FadenSchrittX P O passes Tg K K' →
    K.lebt t = false → K'.lebt t = true →
      K'.m = K.m ∧ (∀ L, L ∉ offen (K'.m.faeden t).spur) ∧ SperrInvG S K'.m ∧
        InvRuheG P M0 K'.m
  -- the budget stop is no stop of the program (2026-10-22): one budget higher, from the same machine with every
  -- `forever` counter one higher, the stopped thread takes its next step
  budgetUnecht : ∀ t, HaltBenannt O passes K.m .budget t →
    ∃ M', RufSchrittG P O (passes + 1) (K.m.plus 1) t M'
-- END atomic-rely definitions --

/-- **GABBRO_ZIEL** (since Opus lane O25c, 2026-09-26: WITH THE ATOMIC RELY). Over the THREAD
    MACHINE OVER GX: every run from the runtime's start, with any set `lebt0` of initially live
    threads -- the others are slots that `start` or `child` spawn at run time -- in which every
    read of an ADMITTED SHARED ATOMIC of the unit (`GeteiltV E.P E.ws`: `atomic`, unguarded, not
    thread-local among the starts, in no contract) may be answered by the weak memory rather
    than by the last write. (a) is a checker for the rely (`PrueferX`: sound against
    `AkzeptiertSpecX`, whose footprint rule admits exactly those carriers), (b) is the user's
    logic with the rely (`NutzerPflichtA`: every body against EVERY value such a read may
    return). Every run of before is such a run (`fadenErreichbarX_of`), every checker of before
    is such a checker (`Pruefer.alsX`), and on every unit it accepts (b) is (b) of before and no
    admitted shared atomic exists: the statement of before, `GabbroZielSC`, is a corollary
    (`gabbro_ziel_sc_aus`, Zielsatz/BeweisAtomar.lean). -/
def GabbroZiel : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) K

/-- **THE STATEMENT OF BEFORE** (verbatim `GabbroZiel` until Opus lane O25c, 2026-09-26): the
    checker of before, (b) without the rely, `ZielF` over the thread machine over G. It is a
    COROLLARY of `GabbroZiel` (`gabbro_ziel_sc_aus`), kept as a name because the corpus theorems
    and the earlier embeddings are stated over it. Since 2026-09-26 over the THREAD MACHINE:
    every thread-machine run from the runtime's start, with any set `lebt0` of initially live
    threads -- the others are slots that `start` or `child` spawn at run time. Every G run is
    such a run (`lebt0` all live, nothing spawned: `fadenErreichbar_von_G`), so the statement of
    before that is a corollary too (`gabbro_ziel_g`). -/
def GabbroZielSC : Prop :=
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


/-! ## Starvation freedom (2026-10-22)

    `GabbroZiel` is a statement about every REACHED machine: safety. Whether a thread that waits for a lock ever
    gets it is a statement about infinite RUNS. It is stated here as a THIRD statement, under the same four premise
    groups, over the runs of the ticket lock (`FifoLauf`, Logik/Fortschritt/PlanLauf.lean) on which the scheduler is
    weakly fair (`Fair`). See the starvation block in the header. -/

/-- **GABBRO_ZIEL_LEBEN.** On every weakly fair run of the ticket lock from the runtime's start, a thread standing
    at `locks L` takes `L`, or some thread holds `L` from some step on for ever (a critical section of the program
    that does not end). -/
def GabbroZielLeben : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ R : FifoLauf E.P.mitRuhe O.mitRuhe passes,                -- the ticket lock
        R.M 0 = RufStartG E.P.mitRuhe sp init →
        Fair E.P.mitRuhe O.mitRuhe passes R.toPlanLauf →        -- the scheduler, weakly fair
        ∀ (n : Nat) (t : Faden) (L : D.mitRuhe.Lock), AnSperre (R.M n) t L →
          (∃ j, n ≤ j ∧ R.akt j = some t ∧ AnSperre (R.M j) t L) ∨
            ∃ u m, ∀ j, m ≤ j → L ∈ offen ((R.M j).faeden u).spur

/-! ## Termination (2026-10-22)

    A FOURTH statement under the same four premise groups, with the measure duty beside (b). See TERMINATION in the
    header. -/

/-- **GABBRO_ZIEL_TERMINIERUNG.** Under the measure duty: on every infinite GX run from the runtime's start every
    thread takes only finitely many steps, and a thread whose start is of class `endet` never stands at a spent
    `forever` budget. -/
def GabbroZielTerminierung : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →                     -- (a) the checker, on E
    NutzerPflichtA E →                                          -- (b) the user, with the rely
    ∀ (passes : Nat) (m : Mass D),
      (∀ f, MassPflicht E.P passes E.Q E.S (GeteiltV (D := D) E.P E.ws) m (zykS E.P fs.1) f) →
                                                                -- (b') the measures fall (`decreases`)
      (∀ f g, zykS E.P fs.1 f g = true → (m f).length = (m g).length) →
    ∀ O : Orakel D, HardwareAnnahmen O E.Q →                    -- (c) the hardware
    ∀ (sp : Speicher D.mitRuhe) (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →                                      -- (d) the runtime, A4
      ∀ R : LaufGX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws),
        R.M 0 = RufStartG E.P.mitRuhe sp init →
        ∀ t : Faden, (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧
          ((∀ w, (init t).1 = some w → klasse E.P fs.1 m.hat w = .endet) →
            ∀ j, ¬ HaltBenannt O.mitRuhe passes (R.M j) .budget t)

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
  -- the dispatch facts agree, like the contracts (Opus agent H, 2026-09-26)
  unterbricht : E₁.P.unterbricht = E₂.P.unterbricht

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
      hull (a routine both units start counts twice);
    * `masken` (Opus agent H, 2026-09-26) -- every function the composed hull of an interrupt
      handler reaches takes only locks declared `masks irqs` (`H102` across the link).
    Every per-body component of `AkzeptiertSpec` (fragment, closed graphs, lock floors, lock
    invariant places, roots, answer sites) is each unit's own verdict; these four are the
    whole-program components, and they are the ones the link re-decides. -/
structure SchnittstelleSpec (fs : List D.Fn) (e : D.Fn → Bool) (E₁ E₂ : Einheit D) : Prop where
  blatt₁ : Platzhalter e E₁.P
  blatt₂ : Platzhalter (fun f => !e f) E₂.P
  keinRueckruf : KeinRueckruf fs e E₁ E₂
  lok : ∀ c, LokBedarf e E₁ E₂ c → GetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
    SchreibGetrenntV fs e E₁ E₂ (verbinde e E₁ E₂).ws c
  einzeln : ∀ w, Mehrfach (verbinde e E₁ E₂).ws w → PoolSicherV fs e E₁ E₂ w
  -- an interrupt handler's COMPOSED hull takes only masked locks (Opus agent H, 2026-09-26)
  masken : ∀ w, E₁.P.unterbricht w = true → ∀ h, HuelleV fs e E₁ E₂ w h →
    mE (NurMaskiert D) ((teilP e E₁ E₂ h).rumpf h) = true

/-- **The user's logic of ONE unit** (the part of (b) a separately compiled unit owes): the
    bodies it OWNS at every budget, its lock and axiom families read only their carriers, and
    its start obligation. A placeholder owes nothing -- its owner proves the body. -/
structure NutzerTeil (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutS E.P passes E.Q E.S f ∧ InvGutS E.P passes E.Q E.S f ∧
        InvGutGrund E.P passes E.Q E.S f) ∧
    SperrInvLokal E.S ∧ AxEnsLokal E.Q
  start : StartPflicht E

/-- **The user's logic of ONE unit, with the atomic rely** (the rely over the unit's own shared
    atomics). -/
structure NutzerTeilA [DecidableEq D.Fn] (eigen : D.Fn → Bool) (E : Einheit D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), eigen f = true →
      KoerperGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f ∧
        InvGutGrundA E.P passes E.Q E.S (GeteiltA E.P E.ws) f) ∧
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
    Then every leg of `ZielFX` holds on every reachable thread machine over GX of the linked
    program -- race freedom and lock discipline ACROSS the units, spawned threads and the
    weak-memory leg included, since the conclusion is `GabbroZiel`'s own. Since Opus lane O25c
    (2026-09-26) WITH THE ATOMIC RELY: (a) a checker for the rely on each unit, (b) each unit's
    logic with the rely over its own shared atomics (`NutzerTeilA`). The link check is
    unchanged: its `lok` demands every footprint carrier a function relies on without a lock
    thread-local over the composed hulls, atomics included, so the linked program has no
    admitted shared atomic (named in NOT CLAIMED). The statement of before is
    `GabbroZielVerbundSC`, a corollary (`gabbro_ziel_verbund_sc_aus`). -/
def GabbroZielVerbund : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E₁ fs.1 ls.1 cs.1 = true →                    -- (a) unit 1, alone
    C.akzeptiert E₂ fs.1 ls.1 cs.1 = true →                    -- (a) unit 2, alone
    Verbindbar E₁ E₂ →                                          -- (a) one link declaration
    SchnittstelleSpec fs.1 e E₁ E₂ →                            -- (a) the link check
    NutzerTeilA e E₁ →                                          -- (b) unit 1's user, rely
    NutzerTeilA (fun f => !e f) E₂ →                            -- (b) unit 2's user, rely
    E₂.Q = E₁.Q →                                               -- (c) the SAME hardware assumptions
    ∀ O : Orakel D, HardwareAnnahmen O E₁.Q →                   -- (c) the hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (verbinde e E₁ E₂) sp init →                     -- (d) the runtime, linked
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
          (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
          (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K →
          ZielFX (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
            (GeteiltV (D := D) (verbinde e E₁ E₂).P (verbinde e E₁ E₂).ws)
            (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) K

/-- **THE LINKED STATEMENT OF BEFORE** (verbatim `GabbroZielVerbund` until Opus lane O25c): a
    corollary of `GabbroZielVerbund` (`gabbro_ziel_verbund_sc_aus`). -/
def GabbroZielVerbundSC : Prop :=
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
