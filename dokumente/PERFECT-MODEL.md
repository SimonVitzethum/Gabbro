# PERFECT-MODEL — the one definition of Gabbro's goal theorem, its model and the way there

Status: **binding** (owner, 2026-11-23). This file is the ONLY place where the goal theorem, the model it speaks
about and the construction of that model in the package `core/` are defined. `AGENTS.md` §3 and the rows B23, B24 and O27 of
[PLAN-COMPILER-READY.md](PLAN-COMPILER-READY.md) point here and hold no own version. It was settled after ten
critical reviews (all on 2026-11-23). It changes only by an owner decision, shown as a concrete diff of this file
before merge; nothing else may restate, extend or soften it. A draft elsewhere is not a decision.

## 1. The promise

> For every text `a` that denotes a program `E` which a perfect checker accepts, and for every hardware and
> environment described by the catalogue rows `E` selects: **every run of the implementation is a run of the
> ideal meaning `I` of `E` with the same environment answers and the same effects in the same order, and
> under the hardware fairness of the selected rows no thread hangs whose next `I` step is enabled.**

Everything `I` allows is the program's logic. Everything else — known or unknown, from memory errors to TOCTOU —
is an error and is excluded. "Effects" are all effects the pinned semantics records: outside questions and
answers, device accesses, outputs, stops, internal state changes and authority effects — an unauthorised internal
write that is undone before any output is an error too. The promise is over the modelled machine (G∞, after
B6/C9 the image). The user is not a premise. Hardware enters only as catalogue rows.

## 2. The theorem

```lean
theorem gabbro_ziel :
    NichtLeer                                             -- §2.1: nothing below holds vacuously
  ∧ (∀ a E, Bezeichnet a E → Akzeptiert E → ∀ H, Hardware (katalog E) H →
      (∀ s, ZulStart E H s → ∃ ρ, Laeufe E H ρ ∧ start ρ = s)
    ∧ ∀ ρ, Laeufe E H ρ → ∃ ι, I.Laeufe E ι ∧ Verfeinert E H ρ ι)
  ∧ NI                                                    -- §3.8
```

One promise, three parts: it is not vacuous; every run of every accepted program refines ONE run of `I`; no
secret leaks. `a` ranges over RAW TEXT. The three names are pinned definitions (§2.1):

```lean
def NichtLeer : Prop :=
    (∀ a, WohlgeformterText a ↔ ∃ E, Bezeichnet a E)
  ∧ (∀ a E E', Bezeichnet a E → Bezeichnet a E' → E = E')
  ∧ (∀ f : Form, ∃ a E, Enthaelt a f ∧ Bezeichnet a E ∧ Akzeptiert E ∧ Realisiert f a E)
  ∧ (∀ E, Akzeptiert E → KatalogWohlgeformt (katalog E))
  ∧ (∀ K, KatalogWohlgeformt K → ∃ H h, Hardware K H ∧ FairLaeufe K H h)
  ∧ (∀ a E, Bezeichnet a E → Akzeptiert E → ∀ H, Hardware (katalog E) H → ∃ s, ZulStart E H s)
  ∧ (∀ a E, Bezeichnet a E → Akzeptiert E → ∀ H s h, Hardware (katalog E) H → ZulStart E H s →
        FairLaeufe (katalog E) H h → ∃ ρ, Laeufe E H ρ ∧ start ρ = s ∧ hw ρ = h)
  ∧ (∀ E, Akzeptiert E → I.Bestimmt E ∧ I.Fortschritt E)

def Verfeinert (E H ρ ι) : Prop :=
    Sim E ρ ι                                             -- §3.6: same effects, same order
  ∧ (∀ t : Schnitt ρ, ZielFX E H ρ t)                     -- today's guarantee on every cut
  ∧ (FairLaeufe (katalog E) H (hw ρ) →                    -- §3.7
       (∀ c, ¬ Haengt E ρ ι c) ∧ Fortschritt (klasse E) ρ ι)
  ∧ ImSchranken E ρ                                       -- stack, memory, cost, time

def NI : Prop :=
  ∀ E H₁ H₂ ρ₁ s₂, Akzeptiert E → Hardware (katalog E) H₁ → Hardware (katalog E) H₂ →
    Laeufe E H₁ ρ₁ → GleicheNiedrigeUmgebung E H₁ H₂ → ZulStart E H₂ s₂ → NiedrigGleich E (start ρ₁) s₂ →
      (∃ ρ₂, Laeufe E H₂ ρ₂ ∧ start ρ₂ = s₂ ∧ GleichePolitik E ρ₁ ρ₂)
    ∧ ∀ ρ₂, Laeufe E H₂ ρ₂ → start ρ₂ = s₂ → GleichePolitik E ρ₁ ρ₂ →
        NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂)
```

**2.1 What the names mean.** `#print axioms gabbro_ziel` is exactly `propext`, `Classical.choice`,
`Quot.sound`. Every name above is ONE pinned concrete definition, never a parameter: the statement of M12 is over
these constants, and the guard of §6 checks the type of `gabbro_ziel` against this text and pins every definition
it depends on down to the approved foundations (a wrapper with an unchanged hash over a changed helper fails).
Bindings that are part of the definitions:
- Text: `a` is raw text. An independent, source-spanned parse relation accounts for EVERY semantic token of `a`
  (a parser that reads `print 1; print 2` as `print 1` violates it); the reference parser and the deployed parser
  are proved to agree with it. `WohlgeformterText` is independently ELABORABLE text — grammar and typing as Lean
  predicates, defined without `Bezeichnet`, acceptance or any parser — so a total `Bezeichnet` into the
  intrinsically typed unit is meaningful; printing and parsing round-trip modulo an explicitly defined trivia and
  canonicalisation relation. `Form` is
  derived from the actual constructors of the reference AST. `Realisiert f a E` ties ONE occurrence of the
  constructor in `a` to its corresponding ideal and implementation transitions in one admissible matched run (for
  a declaration form: its effect on the unit).
- Catalogue: `KatalogWohlgeformt K` is an approved row selection whose composition is valid; `Akzeptiert E →
  KatalogWohlgeformt (katalog E)` follows from `Lokal`. `Hardware K H` says the environment `H` behaves as the
  rows say on the OUTSIDE side of the interaction, mandatory answers included; permitted non-answers are explicit
  in the rows. `hw ρ` is the run's exogenous opportunity schedule (core steps, interrupt and delivery opportunities)
  together with the total reactive outside policy; request-specific replies are separate events of the run, and an
  offered delivery is recorded even when the implementation fails to consume it, so a failure never makes a run
  inadmissible or unfair. `FairLaeufe K H` are the schedules and policies that are fair in the rows' sense — over
  hardware alone, independently of any program and of refinement success; the sixth conjunct proves that each of
  them lifts to a run of every accepted program.
- Starts: `ZulStart E H s` are the catalogue-conformant starts (every legal boot input, start assignment and
  initial outside state the rows allow), defined independently of loader success; every run starts at one. For
  EVERY admissible start a run exists and every admissible fair history lifts to a run from it, so a loader that
  drops a legal input is caught; a loader failure at an admissible start is in scope.
- Runs: `Laeufe E H` are exactly the maximal runs of the composition from the real loader and `start` under
  row-conformant outside behaviour, including finite stuck or failing runs; `Schnitt` covers every finite prefix, also one that issues an invalid request,
  violates authority, gets stuck or prevents a legal reply — an implementation failure stays in scope.
  `Schnitt ρ` contains every state of the run; `hw ρ` is its hardware projection.
- `ZielFX` is defined and proved in `core/` as the core-native form of today's whole guarantee, not a list of leg
  names; the transport package `uebergang/` (M11) proves that it preserves today's guarantee. That proof starts from the FULL premises
  of today's `GabbroZiel`: every retained case (checker, oracle, budget, a `Laufzeit` with a partial start
  assignment, every `lebt0`, every order assignment of `SchwachX`, the address layout) is embedded into an
  accepted text and an actual loader run, its cut is named, and the exact old conclusion is transported with its
  nested quantifiers (`spawnSicht`, `SchwachX`, `ZeitAbX`); an old budget stop transports as a finite prefix. A
  case a new loader or memory rule cannot represent needs a preservation argument or an owner-approved exclusion,
  listed here (none so far).
- `NI`: `GleichePolitik` means the same total policies for the LOW outside choices (outside choice-givers,
  hardware scheduling, answers to low questions), defined on public history before either run; scheduler
  decisions made by program code and high choices stay inside the compared runs and are never equated by a
  premise. The domain of comparison starts (`NiedrigGleich`) is defined independently of the existence claim; for
  every admitted run and every such start a comparison run exists (first part of `NI`). `NiedrigeBeob` is the low
  trace: EVERY low event of §3.4 with its public metadata — outside questions, answer arrivals, committed device
  accesses with their addresses (a secret bit choosing between two public MMIO addresses is observed), public
  memory and outputs, low termination, the declared time of `timed` blocks, for declared
  constant-time code its control, address and cost observations, and speculative accesses under every predictor
  the speculation envelope allows (B15–B17). The two traces are related by `NiedrigAequiv`, a pinned relation:
  equal up to each declared release, differing only as that release authorises; the labelled-flow rule of `Lokal`
  that proves it is named in the registry.

## 3. The definitions

**3.1 Text and meaning.** The language is ONE reference AST: a Lean inductive family in `core/Core/Ast/`,
the single definition of every surface form — today's forms, every low-level form of
[LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md) §4 (execution states and transfers, address spaces, entries,
interrupts and NMIs, cores, devices and DMA, guests, VMs, IOMMU, firmware interfaces, images, timed blocks,
compile-time selection) and async — all on the same level, none in a separate layer. The parser produces it; the
doc comment of each constructor is its reference description; `SYNTAX.md` describes it and never defines a form.
`Elaboriert : Ast → Einheit → Prop` gives one rule per constructor what a tree means; the meaning of raw text is
`Bezeichnet a E := ∃ ast, Parse a ast ∧ Elaboriert ast E`, with `Parse` the source-spanned parse relation of §2.1;
it is functional and the parser is unambiguous. The elaborator is proved sound (`elab_korrekt`) and complete
(`elab_vollstaendig`) against `Elaboriert`, and
printing/parsing round-trips in both directions. The core is the intrinsically typed syntax (`Stmt`, `Block`,
`Endblock`, `Expr`), extended by the low-level constructors at the end of the same inductives; it stays the one
definition of the language. A registry records for every constructor of the reference AST its `Bezeichnet` rule,
its `I` rule, its compatibility lemma and its `_erfuellbar` lemma; a guard (§6) fails the build for a constructor
missing any of them.

**3.2 Acceptance — the perfect checker.** `Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E`.
- `Lokal`: the decidable local rules (types, ownership, lock ranks, units, provenance of outside answers, every
  partial operation covered by an `else` path or a guard, waits only on conditions, a stack bound, a length bound
  per unit, catalogue rows selected by name; data shared with a handler is accessed by the interrupted context
  only under the mask, and a lock shared between a handler and the context it interrupts is refused).
- `KlauselnWahr`: every WRITTEN clause (requires, ensures, invariants, `decreases`, lock and loop invariants) is
  true over `I` under the rely of the whole program. Clauses state user predicates over `I`, never definedness of
  `I` or anything about the implementation.
- `WaechterHalten`: generated from a pinned table of `I`'s partial operations — every guard of a partial
  operation without an `else` holds in every reachable `I` state, AND no reachable ideal cut, a maximal cut
  included, contains an internal deadlock or a closed waiting set as defined in §3.4. Nobody writes it; the
  checker proves it. This is what makes "correct logic produces an error" impossible.
- `Akzeptiert` may use only the syntax, `I` and the catalogue (whitelist); never G, GX, W, the image, runs or the
  error notion. `I` never mentions `Akzeptiert`. The real checker is a separate algorithm with
  `pruefer_korrekt : C.akzeptiert E = true → Akzeptiert E`.

**3.3 The catalogue (`Hardware`).** Pinned, reviewed Lean objects in the repository: target-table rows, CPU, MMU,
interrupt delivery, devices, firmware, operating-system interfaces, float hardware, the loader. A program SELECTS
rows by name and never writes one (AGENTS.md §1: the user "chooses named assumptions" = selects rows). A row's
vocabulary is hardware and environment entities only; it never mentions the program's functions or carriers
except through regions granted to it. Satisfiability is proved jointly for the rows a platform uses. Hardware
events in a run come only from rows. Same-address-space foreign code (`extern fn`) does not exist; in-image
bindings are ordinary Gabbro functions.

**3.4 The ideal meaning `I`.** Derived from G, defined for every `E`, independent of the implementation.
- Each thread steps exactly as its source says; shared state changes only at declared synchronisation points;
  every unit is indivisible. A unit is a stretch of one context with at most one point visible to other contexts
  or to the outside (an atomic operation another context can read, a wait, an outside question, a device access);
  `I` takes the whole unit at that point, its linearisation point. The order of source effects (internal effects
  included) is pinned by `I` independently of the implementation; where mapping a whole unit at one point would
  reverse a recorded effect against another context's effect, the unit is split there. Every unit has a PROVED linearisation point:
  the implementation steps before and after it commute with every interleaved step of other contexts. A stretch
  with several visible points, or without that commutation, is several units. Handlers are cut by the same rule;
  their exclusion from a context is proved from the concrete mask, ownership and NMI semantics, never assumed
  from a local mask. Every source rule of `I` names its units and their commutation proof (registry, §3.1).
- Asynchronous operations are split at their actual visible events: an outside call inside a lock section is
  acquisition, request, arrival of the reply, continuation and release, each its own transition, with the lock
  held across them. The ARRIVAL of an outside reply is a visible event in global order, matched at the same global
  event in `I`; an arrived but unconsumed reply is part of BOTH states across unit boundaries, and only its
  consumption by the context may wait. An operation with several effects at different times (e.g. `flush`: send interrupts, run
  remote handlers, wait for acknowledgements, release frames) has one `I` transition per effect — it is the
  acceptance case of M7.
- `I` states carry lock owners, the ticket queue and hand-off, so a lock section with several units keeps
  ownership, hand-off and its protected invariant. A wait is enabled exactly when its condition holds. Lock
  acquisition is strong-fair (carried by the language's queue/ticket lock).
- Atomics behave as written: `seq_cst` truly sequentially consistent; `acquire`/`release`/`relaxed` with exactly
  their RC11 outcomes, with `po ∪ rf` acyclic (no load buffering; the compiler preserves it). An ideal run
  carries ONE execution witness (reads-from, coherence, SC order) consistent with RC11, chosen together with the
  prefix map of §3.6 — neither one current value per location nor a freely chosen plausible value per read.
- Authority, lifetime, isolation and the reason of every blocking are part of `I`'s state and step rules: a stale
  handle or a revoked capability has no step; an intended wait names its false condition and where it comes from.
  `I` distinguishes an INTERNAL deadlock (a cycle of joins, locks or waits whose conditions only the other members
  can make true — e.g. two threads each awaiting a flag the other sets after its own wait) from a specified
  outside non-answer of a catalogue row; an internal deadlock — including a lone `await` that no context can
  enable and every closed set of waiters — is an error: `Akzeptiert` (`WaechterHalten` over `I`'s reachable
  states) establishes that none is reachable, and it is refused (today's cycle and deadlock
  legs stay), also at maximal cuts.
- Scheduling: contexts the language runtime schedules are dispatched by the runtime with a generic dispatch
  proof. Contexts a program's own scheduler dispatches are scheduled inside `I` by that code: its choice is part
  of the program's logic, and `I` starves a context exactly when that code does. The boundary: starvation is
  logic only when it follows from the program's own scheduler executing in `I`; once that code dispatches a
  context, executing the dispatch is a language obligation. Dispatch and step obligations are defined at the
  current cut, before a scheduling choice can hide an eligible context.
- Outcome type pinned to two kinds: a written value or reason exit, and a catalogue event. No logic, budget or
  visibility stop exists in `I`.
- `I.Bestimmt`: deterministic up to named choice points (scheduler order at sync points, environment answers,
  explicit choice forms); no garbage values (every value has provenance from inputs).
- `I.Fortschritt`: every non-final state has a step or is blocked, and blocked only at a lock, an `await`, a join,
  an outstanding catalogue question whose enabling condition is false, or a HARDWARE DELAY: a context whose
  opportunity is withheld in the exogenous opportunity schedule of the run (a core that stops advancing with a
  runnable thread and no outstanding question) waits in `I` exactly as long.
- Observations: environment questions and answers, device accesses, outputs, stops, and the declared dimensions —
  time inside `timed` blocks, memory where bounded, labelled information flow.

**3.5 The implementation `Impl`.** `I` and the implementation machine are defined over `core/`'s OWN syntax and
events (M3, M4): threads with every interleaving, the memory model of M3 with true SC for `seq_cst`, no loop
budget, real `start`/`child` statements, waits instead of visibility stops. The correspondence to the budgeted
machine G of the frozen `grammatik/` (every finite prefix of a run of the retained fragment is a G run for a large
enough budget) is proved in M11 for the retained fragment only. After B6/C9, the emitted image.

**3.6 Refinement `Sim`.** For every run ONE ideal run, chosen per run (not per prefix): a state-and-step
simulation for the whole run. A state relation holds at EVERY matched cut (not only at the start); every
implementation transition is either matched by its ideal transition or is a checked stutter case; the map is
monotone along prefixes, covers BOTH runs (no unmatched ideal suffix), and matches termination, blocking and
divergence; it keeps the same logical contexts and the same choice resolutions. Concrete accesses and authority
are checked at the transition that uses them, before any projection erases private implementation steps — this
is what makes an unauthorised write that is undone before output an error. For the image (B6/C9), the proof reconstructs every
erased source effect in the ordered source trace, with its value and legality proved; only private machine steps
with no source effect may disappear. ONE event accounting rule holds for `I`, `Sim` and the image: at every cut the
prefix of ARRIVED answers is equal in both runs (an answer event carries its context instance, outside object and
question instance; the order inside a context is kept across objects), and CONSUMPTION by the context is tracked
separately in both states — an arrived reply is never an implementation-only pending answer. Durability changes
are effects, and a crash is possible at every concrete cut (B22). Visible events (outside
questions, device accesses, outputs, stops, atomics read by others, internal and authority effects) appear in the
same global order as in the run; the map neither invents nor swallows ends, answers or effects. Stutter: in every
interval without its ideal step during which its next step stays enabled, a context takes at most the checked
length bound of its unit of its own implementation steps; a blocked context stutters only invisibly.

**3.7 Progress.** State and effect safety (`Sim`, `ZielFX`, bounds) hold on EVERY run. On an unfair hardware
history, a delay of a context caused by the hardware is the same outside delay in `I` (the ideal run waits too),
so whole-run matching never needs an ideal step the hardware withheld. `Hängt E ρ ι c` is defined over persistent
obligations: on a run whose hardware history is fair (finite stuck runs included), an open step instance of context `c` whose `I` step stays enabled on a suffix (weak) or is
enabled infinitely often (strong, for lock acquisition) is never discharged — an obligation is discharged only by
taking the step or by a specified exit or cancellation.
The promise is `¬ Hängt` for EVERY context, per-thread. `Fortschritt (klasse E)` is proved in addition per checked
progress class (`lock_free` constructs also give system-wide progress); it never replaces `¬ Hängt`. Fairness
assumed of the environment is hardware only (cores step, interrupts are delivered): catalogue rows. A kernel's
scheduler is code, never assumed. `ImSchranken` compares the cost, memory and stack determined by the run with the
concrete bounds of `E`; for `timed` blocks §3.4 fixes which time observation `I` shares and where its values come
from (catalogue rows).

**3.8 Noninterference.** `NI` of §2: for every admitted run and every low-equal start, a comparison run under the
same total public-history policies for the low outside choices exists, and every such run has a low trace related
by `NiedrigAequiv` (§2.1: equal up to each declared release); scheduler decisions of program code and high choices stay
inside the runs.

## 4. Inside and outside — how TOCTOU is excluded without being named

- **Inside Gabbro** every state and every interference is known. Every condition an effect relies on — written
  clause or generated guard — is proved under the rely of the whole program. A stale decision that violates no
  written clause, no generated guard, no internal effect rule and no authority rule is logic.
- **Outside Gabbro** (operating system, file system, devices, firmware, guests, VMs, guest memory,
  hardware-changed state): knowledge is valid only at the moment of the answer; the rely for the outside is
  arbitrary change, except a stability a catalogue row states.
- Every outside answer carries the outside object and its generation. Outside provenance flows transitively
  through data, control, aliases, derived handles and object generations. An old answer is historical data: it
  never proves current authority, identity or a precondition, also not after being stored. Every current
  identity, right, generation and precondition an effect uses holds at its COMMIT, across every object it
  touches: established in the same catalogue event through its own handle, or by a pinned row's stability. For an
  asynchronous outside operation this holds at the effect's commit, not at the request: what was checked when the
  request left is established again atomically at commit or proved stable through commit under the arbitrary-change
  rely. A
  copied snapshot may supply historical data, never currency. An effect whose authorisation (on any object)
  rests on an earlier answer is refused. An atomically revalidated
  operation stays writable even when its choice depended on an earlier answer.
- Catalogue interfaces are admitted only if every query goes through a handle the program owns and every
  precondition is checked in the same question (handle-based, atomic, failure channel); name resolution only in
  operations that return a handle. `access`→`open`, double fetch of guest memory and "check, act later" on outside
  state are not writable.
- Stability and footprint rows for devices hold only under a typestate the language tracks (linear device
  authority, `lend`/`take back`); DMA addresses and lengths are capabilities of lent regions, never integers.
  Hardware-held copies of inside state (TLB, caches) are invalidated by the language's own protocols before reuse.

## 5. What the model never contains

`core/` is built without these; they exist only in the frozen `grammatik/`: `D.Annahme`, `AnnahmeEintrag`/`Profil` as program text, `Hardware.fortschritt`, `Hardware.sichtbarkeit`,
`HaltArt.budget`, `flagge` as a stop (it becomes a wait with a named condition), `nieZurueck` as a stop (a catalogue row with an
explicit catalogue-bound wait state or a written exit), the `passes`
budget in the implementation, the spawn over-approximation of `FadenMaschine`, `forever … progress a`,
`retries … a`, program-written environment contracts, `extern fn` in the same address space, and the premises
`GutO`, `AxVertragO`, `AxVertragOSw`, `ForeignPflicht`, `CallSitePflicht`, `PostDeckt`, `ProviderTreueG`,
`RegLokal`, `ImBereichO`, `Laufzeit` (in `core/` they are catalogue rows or proofs). Unbounded recursion without a
computed stack bound and allocation without a failure channel are refused.

## 6. Build guards

Lean modules in `core/Core/Waechter/`, part of the package root, that fail the build of `core/` — strict from its
first semantic commit (M0; the scaffolding commit before it holds only the shape), with NO allow-list and no
ratchet:
1. `core/` depends only on Mathlib and its own modules (its lakefile requires nothing else; it never imports
   `grammatik/`, `stage0/` or `programmlogik/`); every module is reached from `Core.lean`; every file has fewer
   than 500 lines.
2. `Akzeptiert` whitelist (syntax, `I`, catalogue) and the reverse guard (`I` does not mention `Akzeptiert`).
3. Hash pins: the shape (`Rahmen`, `NichtLeer`, `Verfeinert`, `NI`, `GabbroZielForm`), `I` and its outcome type,
   `Bezeichnet`, `Parse`, `Sim`, `Hängt`, `NiedrigAequiv`, every catalogue row.
4. The closing guard (from M12): one argument-free `R₀ : Rahmen` with every field bound to its approved concrete
   constant; the exported `theorem gabbro_ziel : GabbroZielForm R₀`; the guard checks that declaration's
   elaborated type, each field binding of `R₀`, their transitive semantic dependencies down to explicit trusted
   roots, and the axiom set (`propext`, `Classical.choice`, `Quot.sound`).
5. The registry of §3.1, indexed by each actual constructor of the reference AST and of the core syntax: typed
   proofs (not names) of its `Parse` and `Elaboriert` rules, its `I` rule with units and commutation, its
   implementation rule, its preservation lemma, its `Realisiert` evidence (a surface constructor: a source
   occurrence; a core-only constructor: a checked elaboration or runtime origin) and its joint satisfiability
   (`_erfuellbar`). A constructor without its complete entry fails the build — so a constructor enters `core/`
   only together with all of it.
6. No `_ =>` in `I`, the rules and the fundamental proofs; no hardware or stop kind outside the catalogue.
7. No `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `_zeuge`, `decide +kernel`, no witness modules.
8. Fast builds (owner, 2026-11-23): `core/` is elaborated under `maxHeartbeats` 100 000 (half of Lean's default,
   set in its lakefile); a source scan fails the build on any `set_option maxHeartbeats`,
   `synthInstance.maxHeartbeats` or `maxRecDepth`, on `decide` over anything but small finite goals, on bare `simp`
   in a terminal position where `simp only` would do, and on unbounded `aesop`. Proofs go by structure (`induction`,
   `cases`, named lemmas, `simp only [...]`, `omega` on small goals), never by evaluating programs, strings or
   large terms. Budget, measured from the build log by the lead's acceptance: every declaration under 2 s, every
   module under 30 s, a full build of `core/` under 15 min with 12 threads; a slower module is a finding and is
   fixed before more is built on it.

The enforceable promise: **a new constructor keeps the build red until its complete rules, its jointly
satisfiable premises, the generic preservation of the pinned guarantees and the approved semantic diff exist.**
A wrong but consistent `I`-rule or `Bezeichnet`-rule is caught only by the pin and the owner's review — the
review of a new language design stays part of the trusted base.

## 7. Trusted base and honest limits

Trusted: the definitions of `I` and `Bezeichnet` (the language's promise), the catalogue rows, the Lean kernel;
until B6/C9 the bytes. The promise of §1 covers every effect the pinned semantics records (internal state
changes and authority effects included); physical dimensions outside it stay invisible (undeclared side
channels, speculation beyond its envelope). `Akzeptiert` is undecidable as a whole; the real checker decides a
fragment and is connected by `pruefer_korrekt`.

## 8. Building `core/` — the plan

Owner, 2026-11-23: the model is built FRESH in the package `core/`, not by migrating `grammatik/`. Rules:
- `grammatik/` is frozen: no new features; only repairs that keep the `master` gate green. Its `gabbro_ziel` stays
  green and is the interim promise until M12. Deliveries for `grammatik/` that were not merged by 2026-11-23 are
  not merged; what they contain is ported.
- Porting, never importing: a piece of `grammatik/` (or of an unmerged branch) enters `core/` as a copy rewritten
  onto `core/`'s definitions, with its statement reviewed (AGENTS.md §7). The ONLY place that sees both packages is
  the transport package of M11.
- `core/` is green at every commit: the guards of §6 hold from the first semantic commit (M0), so a constructor enters only with
  its complete registry entry, and no step leaves a red build behind.
- Stage 0 and GabbroV stay on `grammatik/` until M12 and then move onto `core/` (PLAN-COMPILER-READY, phase B).
- Each step is merged on its own after a green build of `core/`; sizes are new Lean lines (ranges); no other plan
  text restates them.

| Step | Done when | Depends on | New lines |
|---|---|---|---|
| **M0 Package and guards** | the first commit (DONE 2026-11-23: the package and `Core/Ziel/Form.lean`) is scaffolding; guards 1–3 and 5–8 of §6 are Lean modules of the package root BEFORE the first semantic commit (until then nothing but the shape enters); guard 4 is activated at M12 | — | 2 000–5 000 |
| **M1 Text** | constructor-independent foundations: raw text, tokens with source spans and trivia, the FRAMEWORK of the parse relation `Parse` and of `WohlgeformterText` (each constructor adds its rule when it enters), the canonicalisation relation of the round trip, the registry type of §3.1, and the INVENTORY as data with source reference and owning step: today's forms, every low-level form (LOW-LEVEL-SYNTAX-PLAN §4), async, the M6F forms, the PLAN §0 forms (substring, bounded `while`, effect groups, tuples), aggregate passing and in-place construction (PLAN P1), the clause forms of B11 and the persistence forms of B22 | M0 | 5 000–12 000 |
| **M2 Catalogue** | `Hardware` of §3.3 with rows for x86-64, AArch64 and RISC-V 64 (ported from the S2 branch `agent/s2-catalogue`); catalogue-conformant starts `ZulStart`; hardware histories `hw` with `FairLaeufe`, independent of programs; joint satisfiability per platform; folded in: A1 foreign software as rows, A2 register answers, A3 float hardware, A4 address ranges and core plan, A6 C interop (only outside the address space, as rows — never `extern fn` or a program-written assumption, §3.3 and §5), the persistence envelope of B22 | M0 | 16 000–42 000 |
| **M3 Memory model** | RC11 with truly SC `seq_cst`, `po ∪ rf` acyclic, DRF-SC, the operational graph machine (sound and complete), the sink and append lemmas, ported from `grammatik/Grammatik/Speichermodell/RC11/` and the branch `agent/s5b-w`; an event type that the machines of M4 and `I` both produce | M0 | 15 000–40 000 |
| **M4 Machines and `I`** | constructor-independent foundations of the implementation machine and of `I` (§3.4, §3.5): states, contexts, events over M3, units at proved linearisation points, lock owners with queue and hand-off, the delay rule, authority and lifetime, the pinned outcome type, `I.Bestimmt`, `I.Fortschritt`; the state contains the low-level concepts from the start (per-core state, privilege, active space, masks, interrupt and NMI preemption, devices, DMA and guests as outside with typestates, catalogue events); statements such as `start`/`child` become real when their constructors enter in M6 | M2, M3 | 26 000–65 000 |
| **M10 Outside rule** | the foundation of §4: transitive outside provenance, validity at commit, the catalogue admission rule, device typestates | M2, M4 | 4 000–10 000 |
| **M5 Acceptance** | `Akzeptiert := Lokal ∧ KlauselnWahr ∧ WaechterHalten` over `I` and the catalogue (with the deadlock part of §3.2), the pinned table of partial operations, the whitelist guard | M4, M10 | 3 000–8 000 |
| **M6 Today's forms** | every form of today's language, the PLAN §0 forms (substring, bounded `while`, effect groups, tuples) and P1 (aggregates by value, in-place construction), each constructor in ONE guarded commit with its `Parse`, `Elaboriert`, `Lokal`, `I` and implementation rule, preservation, `Realisiert` and `_erfuellbar`; `Bezeichnet`, `elab_korrekt`, `elab_vollstaendig`, both round trips | M1, M4, M5, M10 | 30 000–80 000 |
| **M6F Further forms** | the same for async (`async fn`, `.await`, `join`, executor; PLAN S8, with its progress under M8's rules), statically checked internal state (PLAN S9), scope regions (PLAN S10), plain payloads of `publish`/`awaits` (B12), invariants inside a running writer (B14), isolation in `I`'s authority (B18) | M6 | 44 000–118 000 |
| **M6L Low-level forms** | the same for every low-level form of LOW-LEVEL-SYNTAX-PLAN §4 (the former L rows); done also requires the cross-constructor theorems of the L rows — isolation, TLB shootdown, DMA through the IOMMU, the boot hand-off chain from 16 bit | M6 | 236 000–596 000 |
| **M7 Refinement** | `Sim` of §3.6 for every run; STARTS on M4 from the S7 prototype (`grammatik/Grammatik/Zielsatz/Ideal/Prototyp/`, ported) and grows with every form; CLOSES only with the cases of M6F and M6L (the acceptance case `flush`; linearisability of lock-free structures, B20) and the missing legs (B10) | starts M4; closes M6, M6F, M6L | 48 000–125 000 |
| **M9 Observations and NI** | `ImSchranken`: hold bounds and cost and time first (B8), then stack (B9), memory (B21), real time (B19); `NI` of §2 with information flow (B15), constant time (B16), speculation safety (B17); crash consistency over the persistence envelope with the B22 forms and their registry entries | M7 | 69 000–178 000 |
| **M8 Progress** | §3.7 per context and per class under hardware-only fairness; liveness with spawned threads (B7, model side); waiting bounds and starvation freedom (B13) on M9's hold bounds | M7, M9 (B8 part) | 24 000–63 000 |
| **M9P Probability** | random sources as rows with their draw laws; the B11 clause forms with their registry entries; a CAUSAL, measure-preserving lifting under every admitted scheduler and non-random policy; from it the B11 guarantees (model side) | M9 | 30 000–80 000 |
| **M11 Transport** | `ZielFX` is defined and proved in `core/`; the package `uebergang/` imports `grammatik/` and `core/` and proves that `ZielFX` preserves today's whole guarantee from the full premises of today's `GabbroZiel` (§2.1), including the budgeted-G prefix correspondence for the retained fragment (§3.5); an excluded case only with the owner's approval | M6, M6F, M6L, M7, M8, M9, M9P, M10 | 6 000–20 000 |
| **M12 Closing** | the model is closed: `R₀` and `gabbro_ziel : GabbroZielForm R₀` over the concrete constants; non-degeneracy of every premise bundle (C11); the closing guard of §6 active; zero open registry entries. `grammatik/` and `uebergang/` stay until Stage 0, the bridge and the guardians have switched to `core/` (PLAN-COMPILER-READY phase B); then both are removed in one green cutover and the header of `Spec.lean` gives way to this file's §2 | M11 | 4 000–11 000 |
| **Total** | | | **562 000–1 453 000** new (without the low-level forms 326 000–857 000; M6L 236 000–596 000) |

**Image gate** (PLAN-COMPILER-READY B6 in phase B, C9 in phase C; outside this plan): it lifts the WHOLE promise
to images — an image run for every catalogue-conformant start, the lift of every admissible fair hardware history,
`Verfeinert` on EVERY image run (fair or not), and `NI` with comparison-run existence; state reachability alone
does not pass it.

Critical path: M3 → M4 → M10 → M5 → M6 → M6L → M7 (close) → M9 → M8 → M11 → M12. M1, M2 and M3 start at once;
M7 starts on M4 and grows with every form; M6F and M6L run form by form beside M7–M9. Riskiest step: M7, the refinement to `I`; its prototype exists. Scope: every
model item of [PLAN-COMPILER-READY.md](PLAN-COMPILER-READY.md) is inside a step above (the L rows, S8–S10, A1–A4, A6,
B7–B22, C11); Stage 0, GabbroV and the compiler and kernel are not — they are rebuilt on `core/` and get easier
through it: Stage 0 parses into the reference AST and its input's meaning is `Bezeichnet` with `elab_korrekt`;
GabbroV generates its duties from the one AST and the registry; the image theorem proves `Verfeinert` for the image.
