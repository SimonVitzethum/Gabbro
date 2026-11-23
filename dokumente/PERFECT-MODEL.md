# PERFECT-MODEL — the one definition of Gabbro's goal theorem, its model and the way there

Status: **binding** (owner, 2026-11-23). This file is the ONLY place where the goal theorem, the model it speaks
about and the migration of `grammatik/` onto it are defined. `AGENTS.md` §3 and the rows B23, B24 and O27 of
[PLAN-COMPILER-READY.md](PLAN-COMPILER-READY.md) point here and hold no own version. It was settled after five
critical reviews (all on 2026-11-23). It changes only by an owner decision, shown as a concrete diff of this file
before merge; nothing else may restate, extend or soften it. A draft elsewhere is not a decision.

## 1. The promise

> For every text `a` that denotes a program `E` which a perfect checker accepts, and for every hardware and
> environment described by the catalogue rows `E` selects: **every run of the implementation is a run of the
> ideal meaning `I` of `E` with the same environment answers per context, and no thread hangs while `I` could proceed.**

Everything `I` allows is the program's logic. Everything else — known or unknown, from memory errors to TOCTOU —
is an error and is excluded. The user is not a premise. Hardware enters only as catalogue rows.

## 2. The theorem

```lean
theorem gabbro_ziel :
    -- non-vacuity
    (∀ K, KatalogWohlgeformt K → ∃ H, Hardware K H ∧ Antwortet H ∧ (FairLaeufe H).Nonempty)
  ∧ (∀ f : Form, ∃ a E, Enthaelt a f ∧ Bezeichnet a E ∧ Akzeptiert E)
  ∧ (∀ E, Akzeptiert E → I.Bestimmt E ∧ I.Fortschritt E)
  -- the promise
  ∧ ∀ a E, Bezeichnet a E → Akzeptiert E → ∀ H, Hardware (katalog E) H →
      (Laeufe (Impl E ∥ H)).Nonempty
    ∧ ∀ ρ ∈ Laeufe (Impl E ∥ H), ∃ ι ∈ I.Laeufe E ρ.antworten,
          Sim E ρ ι                                   -- §3.6: one ideal run per run
        ∧ (∀ t, ZielX (ρ.zustand t))                  -- today's state legs, explicit
        ∧ (FairH ρ → Fortschritt (klasse E) ρ ι)      -- §3.7
        ∧ Beob ρ ≤ Schranke E                         -- stack, memory, cost
  ∧ NI                                                -- §3.8, over pairs of implementation runs
```

`#print axioms gabbro_ziel` is exactly `propext`, `Classical.choice`, `Quot.sound`.

## 3. The definitions

**3.1 Text and meaning.** The language is ONE reference AST: a Lean inductive family in `grammatik/Grammatik/Ast/`,
the single definition of every surface form — today's forms, every low-level form of
[LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md) §4 (execution states and transfers, address spaces, entries,
interrupts and NMIs, cores, devices and DMA, guests, VMs, IOMMU, firmware interfaces, images, timed blocks,
compile-time selection) and async — all on the same level, none in a separate layer. The parser produces it; the
doc comment of each constructor is its reference description; `SYNTAX.md` describes it and never defines a form.
`Bezeichnet : Ast → Einheit` gives one rule per constructor what a text means; it is functional and the parser is
unambiguous. The elaborator is proved sound (`elab_korrekt`) and complete (`elab_vollstaendig`) against it, and
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
  operation without an `else` holds in every reachable `I` state. Nobody writes it; the checker proves it. This
  is what makes "correct logic produces an error" impossible.
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
  every unit is indivisible. A unit is a reducible stretch of one context: lock acquisitions and local accesses,
  at most one sync point (an atomic operation, a wait, an outside question), then lock releases; a handler under
  its mask is one unit. `I` states carry lock owners, so a lock section with several sync points is several units.
- A wait is enabled exactly when its condition holds. Lock acquisition is strong-fair (carried by the language's
  queue/ticket lock).
- Atomics behave as written: `seq_cst` truly sequentially consistent; `acquire`/`release`/`relaxed` with exactly
  their RC11 outcomes, with `po ∪ rf` acyclic (no load buffering; the compiler preserves it).
- Outcome type pinned to two kinds: a written value or reason exit, and a catalogue event. No logic, budget or
  visibility stop exists in `I`.
- `I.Bestimmt`: deterministic up to named choice points (scheduler order at sync points, environment answers,
  explicit choice forms); no garbage values (every value has provenance from inputs).
- `I.Fortschritt`: every non-final state has a step or is blocked, and blocked only at a lock, an `await`, a join
  or an outstanding catalogue question whose enabling condition is false.
- Observations: environment questions and answers, device accesses, outputs, stops, and the declared dimensions —
  time inside `timed` blocks, memory where bounded, labelled information flow.

**3.5 The implementation `Impl`.** Machine G∞ (G without the loop budget `passes`; every finite prefix is a G run
for a large enough budget) over GX with every interleaving and W with true SC for `seq_cst`. `start`/`child` are
real statements. After B6/C9, the emitted image.

**3.6 Refinement `Sim`.** For every run ONE ideal run, chosen per run (not per prefix), with the same environment
answers per context (per outside object) and the same observations; answers received inside a running unit are
pending until the unit ends, where `I` takes the unit in one step. Stutter is bounded by the checked length bound
of the running unit while the thread's `I` step is enabled; a blocked thread may take any
number of steps that change no observation. Choice resolutions are preserved by the map.

**3.7 Progress.** `Hängt`: on a hardware-fair run, a thread whose `I` step stays enabled (weak) or is enabled
infinitely often (strong, for lock acquisition) never takes it. `Fortschritt (klasse E)` holds per checked
progress class: blocking constructs give per-thread progress; `lock_free` constructs give system-wide progress.
Fairness assumed of the environment is hardware only (cores step, interrupts are delivered): catalogue rows. A
kernel's scheduler is code, never assumed.

**3.8 Noninterference.** A two-run statement over pairs of implementation runs with the same resolution of every
choice point and the same catalogue answers to low questions.

## 4. Inside and outside — how TOCTOU is excluded without being named

- **Inside Gabbro** every state and every interference is known. Every condition an effect relies on — written
  clause or generated guard — is proved under the rely of the whole program. A stale decision that violates
  nothing declared is logic.
- **Outside Gabbro** (operating system, file system, devices, firmware, guests, VMs, guest memory,
  hardware-changed state): knowledge is valid only at the moment of the answer; the rely for the outside is
  arbitrary change, except a stability a catalogue row states.
- Every outside answer carries the outside object it is about. An effect on that object that depends — by data
  or control — on an earlier answer about it is refused.
- Catalogue interfaces are admitted only if every query goes through a handle the program owns and every
  precondition is checked in the same question (handle-based, atomic, failure channel); name resolution only in
  operations that return a handle. `access`→`open`, double fetch of guest memory and "check, act later" on outside
  state are not writable.
- Stability and footprint rows for devices hold only under a typestate the language tracks (linear device
  authority, `lend`/`take back`); DMA addresses and lengths are capabilities of lent regions, never integers.
  Hardware-held copies of inside state (TLB, caches) are invalidated by the language's own protocols before reuse.

## 5. What leaves the language

`D.Annahme`, `AnnahmeEintrag`/`Profil` as program text, `Hardware.fortschritt`, `Hardware.sichtbarkeit`,
`HaltArt.budget`, `flagge` as a stop (it becomes blocking), `nieZurueck` as a stop (a catalogue row), the `passes`
budget in the implementation, the spawn over-approximation of `FadenMaschine`, `forever … progress a`,
`retries … a`, program-written environment contracts, `extern fn` in the same address space, and the premises
`GutO`, `AxVertragO`, `AxVertragOSw`, `ForeignPflicht`, `CallSitePflicht`, `PostDeckt`, `ProviderTreueG`,
`RegLokal`, `ImBereichO`, `Laufzeit` (all become catalogue rows or proofs). Unbounded recursion without a
computed stack bound and allocation without a failure channel are refused.

## 6. Build guards

A Lean module set (`grammatik/Grammatik/Zielsatz/Waechter/`) that fails the build:
1. `Akzeptiert` whitelist (syntax, `I`, catalogue) and the reverse guard (`I` does not mention `Akzeptiert`).
2. Hash pins: `I` and its outcome type, `Bezeichnet`, the error notion (`Sim`, `Hängt`), the theorem, every
   catalogue row.
3. Shape of `gabbro_ziel`'s type: only the premises of §2.
4. No `_ =>` in `I`, the rules and the fundamental proof.
5. The registry of §3.1: for every constructor of the reference AST and of `Stmt`/`Block`/`Endblock`/`Expr` a
   `Bezeichnet` rule, an `I` rule, a compatibility lemma and an `_erfuellbar` lemma.
6. No hardware or stop kind outside the catalogue.
7. No `_zeuge`, no `decide +kernel` outside probe modules.

During the migration each guard is a ratchet: today's measured violations are an allow-list that may only shrink.
Adding unsound syntax turns the build red. A wrong but consistent `I`-rule or `Bezeichnet`-rule is caught only by
the pin and the owner's review — that is the trusted part.

## 7. Trusted base and honest limits

Trusted: the definitions of `I` and `Bezeichnet` (the language's promise), the catalogue rows, the Lean kernel;
until B6/C9 the bytes. Errors in dimensions that are not declared observations stay invisible (undeclared side
channels, speculation beyond its envelope). `Akzeptiert` is undecidable as a whole; the real checker decides a
fragment and is connected by `pruefer_korrekt`.

## 8. The migration of `grammatik/` — the plan

Rules: `grammatik/` first; Stage 0 is not restructured until step S12 is done (it holds no forms and is not the
core). **`gabbro_ziel` need not build green during the migration** (owner, 2026-11-23); `dev` may be red;
`master` keeps its gate. When it builds, it is on the standard axioms and without `sorry`. Each step is merged on
its own when it builds; no step starts its trust-path work before the steps it depends on are merged. Sizes are
new Lean lines (ranges); no other plan text may restate them.

| Step | Done when | Depends on | New lines |
|---|---|---|---|
| **S0 Guards** | the seven guards of §6 build as ratchets with today's allow-lists | — | 2 000–5 000 |
| **S1 Purge** | witnesses, fixtures, witness-style `decide +kernel` probes, the `bindCtx`/`context<P>` parts of `Niedrig/` and the 12 wildcards in `Kern/Semantik` are deleted; side statements are lemmas | S0 | 0 (removes 20 000–60 000) |
| **S1b Reference AST** | `grammatik/Grammatik/Ast/` defines every surface form including all low-level forms (LOW-LEVEL-SYNTAX-PLAN §4) and async; the parser produces it; `Bezeichnet` exists as a relation with the registry of §3.1, every constructor on the guard's ratchet list until its four entries exist | S0 | 5 000–12 000 |
| **S2 Catalogue and premises** | `Hardware` is the catalogue of §3.3; everything in §5 that is an assumption is a row; `D.Annahme`, `fortschritt`, `sichtbarkeit`, `extern fn` are gone | S0 | 8 000–20 000 |
| **S3 Honest G** | G∞ with the prefix lemma; `start`/`child` statements; `flagge` blocking; no `budget` | S0 | 6 000–15 000 |
| **S4 Premise shape** | `Akzeptiert := Lokal ∧ KlauselnWahr ∧ WaechterHalten`; `gabbro_ziel` without (b) and (d) | S2, S3 | 3 000–8 000 |
| **S5 Memory model** | W with true SC, RC11 without load buffering, DRF-SC | S0 | 15 000–40 000 |
| **S6 Ideal meaning** | `I` of §3.4 in `Zielsatz/Ideal/` with `I.Bestimmt`, `I.Fortschritt`, pinned outcome type; its state and steps contain the low-level concepts from the start (per-core state, privilege, active space, masks, interrupt and NMI preemption, devices, DMA and guests as outside with typestates, catalogue events) | S1b, S3, S5 | 20 000–50 000 |
| **S6L Low-level forms** | every low-level constructor of the reference AST has its core constructor, G rule, `Akzeptiert` rule, `I` rule, compatibility lemma, `_erfuellbar` and `Bezeichnet` rule — the former L rows of the plan, now on the same level as every other form | S1b, S6 | 236 000–596 000 |
| **S7 Refinement** | `Sim` of §3.6 for every run of G∞, reusing `ZielInvSA` and the race and lock legs; first a prototype on two threads with assignment, lock, atomics, an interrupt handler under a mask preempting a unit, a device register as outside and `lend`/`take back` of a DMA buffer | S6 | 30 000–80 000 |
| **S8 Progress** | §3.7 per class under hardware-only fairness | S7 | 15 000–40 000 |
| **S9 Observations and NI** | bounds on stack, memory, cost; §3.8 | S7 | 20 000–55 000 |
| **S10 Meaning of text** | every `Bezeichnet` rule, `elab_korrekt`, `elab_vollstaendig`, both round trips (the relation and registry exist since S1b) | S1b, S4 | 30 000–80 000 |
| **S11 Outside rule** | §4: provenance of outside answers, the catalogue admission rule, device typestates | S2 | 4 000–10 000 |
| **S12 Swap** | linking per module; `gabbro_ziel` of §2 proved; old statements deleted; Spec header replaced by this file's §2 | S4–S11 | 10 000–30 000 |
| **Total** | | | **404 000–1 041 000** new (core 168 000–445 000, low-level 236 000–596 000), 20 000–60 000 removed |

Critical path: S5 → S6 → S7 → S8 → S12. Riskiest step: S7 (a global ideal run from per-thread replays, with
interrupts and devices); its prototype comes first and contains low-level from the start. Parallel tracks within
the agent limit: {S1, S1b, S2, S3, S5} at once; S6L from S6 on, form by form, alongside S7–S9; S10 from S4 on; S11
after S2; S8 and S9 together. Low-level is never a separate layer: every low-level form is a constructor of the
reference AST and of the core, with the same four registry entries as every other form.
