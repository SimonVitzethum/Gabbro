# Noninterference -- isolation as a theorem over machine G

*Written 2026-09-14. Lean: `grammatik/Grammatik/Nichtinterferenz/` (11 files, about 4,000 lines).
Axioms of every theorem named here: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
no `admit`, no `native_decide`, no new `axiom`. The full library builds.*

## 0. Standing, in one paragraph

**Proved:** for every program that passes the decidable flow condition `flussB`, every observer
domain `B`, and every two runs of machine G with the same schedule from start memories that
agree on everything `B` may see, `B` sees the same at every step (`nichtinterferenz`). The
schedule may also be produced by a scheduler, provided its choice depends only on what `B`
sees (`nichtinterferenz_planer`); the fixed-timetable partition scheduler is the instance
(`nichtinterferenz_zeitplan`). The metatheorem is proved ONCE, over all 74 rules of machine G;
the program supplies its premises through a check the checker can run. **Not proved:** anything
about timing, anything about a scheduler that looks at the other tenant's state, anything about
runs in which a scheduled thread cannot step, anything with declassification (only its statement
exists), anything below machine G (the emitted C, the binary, the hardware).

## 1. Why this is its own theorem

The product promise is isolation instead of VMs: *tenant A learns nothing about tenant B*. That
is noninterference, a property of PAIRS of runs (a hyperproperty, `BEWEIS.md` §"Item 5 has a
floor"): no pre/postcondition of a single run can state it, and no amount of Hoare logic over
single runs yields it. An external review put it plainly: the isolation claim the product sells
was not in the carried fragment.

The architecture is the one data-race freedom already uses (`rennfrei_g_voll`): the
METATHEOREM is proved once in Lean over machine G; the LANGUAGE supplies its premises per
program, decided by the checker. The user writes labels, not proofs.

## 2. The model

**Domains and policy.** A type of domains `Dom` with a flow relation `darf a b` ("data of `a`
may flow to `b`"), reflexive and transitive (`Politik`). A lattice is a special case. The tenant
case is three points: `K` (kernel/configuration) may flow to `A` and to `B`; `A` and `B` only to
themselves (`NIZeuge.nπ`).

**Labels** (`FlussEtiketten`, `Etiketten`):
* every CARRIER -- table, global (`static`, `atomic`), and therefore every device carrier
  (`rtraeger`: a device's state lives in declared carriers) and every carrier a lock invariant
  ranges over -- has a domain `lab c`;
* every AXIOM (foreign body, device driver, `extern`) has a domain `labAx a`;
* every ENTRY ROOT has a domain (`wurzel f = some d`); a THREAD has the domain of the root it
  starts in (`fdom t`, premise `hW`: `wurzel (init t).1 = some (fdom t)`).

**The observation of `B`** (`beob`): the memory of every carrier whose label may flow to `B`,
and the ghost-free state (`kern`: stack of frames with function, parameters, residue and local
environment; the thread's trace) of every thread whose domain may flow to `B`. NOT observed:
the per-frame entry worlds `s0` and the call logs (proof bookkeeping that copies all of memory;
nothing is emitted for them), the global run log `lauf` (instrumentation over every thread).

**Low-equivalence** (`NiGleich`): equal observations; `beob_gleich_iff` says the two coincide
(this is output consistency, and it holds by definition).

## 3. The attacker model

* **Possibilistic, schedule-parametric.** Two runs are compared step by step under the SAME
  scheduler choices. What a step does to the acting thread's observable state and to memory is
  a function of the state before (`schrittK_von`), so there are no probabilities to speak of.
* **Inputs are per domain.** `A`'s secret inputs are the contents of `A`-labelled carriers at
  the start -- device state included, since a register answers only from its device carriers
  (`RegLokal`). The two runs use the same program, the same oracle, the same budget.
* **The hardware is an input too, and constrained.** Axioms that may flow to `B` answer and act
  on `B`-visible data only (`OrakelTreu`); every axiom keeps its declared frame (`GutO`).
* **Timing is NOT covered.** Machine G has no time. How long a step takes, caches, TLBs, branch
  predictors, speculative execution, DRAM and interconnect contention, power and electromagnetic
  emanation: none of it is in the model, so none of it is in the theorem.
* **Enabledness is NOT covered.** The theorem compares two runs that BOTH follow the schedule.
  A run in which the scheduled thread cannot step -- blocked on a lock another domain holds,
  finished, halted on a failed check -- is not a run of the theorem. See §5 and §7.4.
* **Declassification is out of scope for the first cut** (§8).

## 4. The theorems (exact statements)

**Unwinding conditions for one step of G** (`AbwicklungG π E B P O passes init`), on every
machine reachable from a start with entry `init`:
* LOCAL RESPECT: a step of a thread `f` with `sichtbarF f = false` (its domain may not flow to
  `B`) leaves the `B`-observation unchanged: `NiGleich M M'`.
* STEP CONSISTENCY: a step of a thread `f` with `sichtbarF f = true`, taken from two
  low-equivalent machines, ends in low-equivalent machines.
* OUTPUT CONSISTENCY: low-equivalent machines show `B` the same (`beob_gleich_iff`).

**Metatheorem** (`ni_aus_abwicklung`):

```
AbwicklungG π E B P O passes init →
SpeicherGleich (sichtbarC π E B) sp₁ sp₂ →
LaufG P O passes (RufStartG P sp₁ init) ms fs n →
LaufG P O passes (RufStartG P sp₂ init) ns fs n →
∀ k ≤ n, beob π E B (ms k) = beob π E B (ns k)
```

It is the instance of `ni_allgemein`, which is generic over any pair of step relations.

**The combined theorem** (`nichtinterferenz`), for `E := etiketten L fdom`:

```
(∀ g, g ∈ fs) → (∀ c, c ∈ cs) →              -- the enumerations (exporter)
flussB π P fs cs L = true →                   -- the flow check (checker)
(∀ t, L.wurzel (init t).1 = some (fdom t)) →   -- threads start at labelled roots
GutO O → RegLokal O →                         -- hardware: frames, register locality
OrakelTreu (zuDom π L.lab B) (axZuDom π L.labAx B) O →  -- hardware: B's axioms see B only
SpeicherGleich (sichtbarC π E B) sp₁ sp₂ →    -- same B-inputs
LaufG … sp₁ … ms fs' n → LaufG … sp₂ … ns fs' n →        -- same schedule
∀ k ≤ n, beob π E B (ms k) = beob π E B (ns k)
```

**With a scheduler** (`nichtinterferenz_planer`): the thread of step `k` is `plan k (ms k)`,
resp. `plan k (ns k)`, and `plan` satisfies
`beob π E B M = beob π E B N → plan k M = plan k N`. Conclusion: equal observations at every
index AND the same thread chosen at every step. **Fixed timetable** (`nichtinterferenz_zeitplan`):
`plan k _ := tafel k`.

## 5. The scheduler is a channel

The first theorem holds the schedule as a parameter; it does not explain the schedule. If the
scheduler picks the next thread from state that `A` influences (`A`'s load, `A`'s queue lengths,
whether `A`'s thread is blocked), then `B`'s observation depends on `A` through the schedule --
`B`'s thread runs sooner or later, reads a shared configuration before or after a write, finishes
its computation at a different step. seL4's information-flow proof holds only for a partition
scheduler with a fixed timetable, for exactly this reason.

`nichtinterferenz_planer` closes the gap for every scheduler whose choice depends only on `B`'s
observation; the fixed timetable is the degenerate case (it depends on nothing). A scheduler
that is NOT covered:
* round robin over runnable threads (whether `A`'s thread is runnable is `A`'s state),
* any load balancer, any work stealing, any priority boost from `A`'s behaviour,
* a timetable that SKIPS a slot whose thread is blocked instead of idling it (enabledness, §3).

## 6. The customer-facing sentence

**The sentence in the form in which it is TRUE:**

> If a Gabbro program is accepted by the checker with domain labels -- every table, static,
> device and foreign function labelled with the tenant (or the shared kernel domain) it belongs
> to, every entry point labelled with the tenant it serves -- and it runs on a Gabbro runtime
> whose scheduler hands out time slices by a fixed timetable (or by any rule that looks only at
> tenant B's own state), with a blocked slot left idle rather than given away, then nothing in
> tenant A's data changes what tenant B's threads compute or what tenant B's memory holds, step
> for step. This holds for the Gabbro language model (machine G), under these named
> assumptions: every foreign function and device driver writes only what it declares, device
> registers answer only from their declared device state, and every foreign function tenant B
> may call acts only on data tenant B may see. It says nothing about timing: how long anything
> takes, caches, speculative execution, memory and bus contention, power and electromagnetic
> side channels are not covered. It says nothing yet about the compiled binary: the transfer
> from machine G to the emitted C is the concurrent stage of the translation-validation plan.

**The sentences that are NOT true, and may not be written:**

* *"Tenant A learns nothing about tenant B on a shared, dynamically load-balanced machine."*
  FALSE under a load-based scheduler: the scheduler reads A's load, B's progress then depends
  on A, and the theorem makes no claim. It becomes true only for a scheduler that meets the
  condition of §5.
* *"Gabbro isolates tenants as well as VMs, including side channels."* FALSE: timing and every
  physical side channel are excluded -- from this theorem, and in practice from VMs as well.
* *"Isolation is proved down to the binary."* FALSE today: the theorem is over machine G.
* *"Any Gabbro program is isolated."* FALSE: only programs that pass the flow check with
  domain labels; a program without labels has one domain and the theorem says nothing about it.
* *"Tenants cannot interfere through shared data structures."* FALSE as a promise and TRUE as
  a restriction: a structure written by two tenants is REFUSED by the check (§9); isolation is
  obtained by forbidding sharing, not by making sharing safe.

The rule for anyone writing about it: every sentence about isolation carries the scheduler
class, the timing exclusion and the level (machine G), or it is not written.

## 7. The language surface and the checker rule

### 7.1 Surface (smallest proposal)

```
domain kernel;
domain tenant_a;
domain tenant_b;
flows kernel -> tenant_a, kernel -> tenant_b;     -- the policy; reflexive-transitive closure

table konten_a count 64 domain tenant_a { … }
table konten_b count 64 domain tenant_b { … }
atomic konfig : u32 domain kernel;
device nic_a domain tenant_a { … }                 -- labels its device carriers
extern fn nic_a_senden(…) domain tenant_a effects { … };

concurrent { handle_a domain tenant_a, handle_b domain tenant_b, verwalte domain kernel };
entry syscall_a vector 0x80 domain tenant_a { dispatch …; }
```

Absent labels mean one default domain: every existing program is unchanged, and the theorem is
vacuous for it (one domain has nothing to hide from itself).

### 7.2 The rule `flussB`, and what the checker reports

For every labelled root `r` of domain `d` and every function `g` the call graph from `r` reaches
(the closure is checked, `abgB`):

| code | rule (Lean: `wurzelB`) |
|---|---|
| `I001` read up | every carrier `g` reads -- in any expression, as the device carrier of a register read, as an awaited/exchanged global -- has a label that may flow to `d` (`nE (zuDom lab d) …`) |
| `I002` write down | every carrier `g`'s write frame (`effects { writes … }`, axiom frames included) has a label `d` may flow to |
| `I003` foreign call | every axiom `g` calls has a label that may flow to `d` |
| `I004` unlabelled root | a program with more than one domain starts no thread at an unlabelled root |

**Explicit and implicit flows.** An explicit flow `tabB[0] = tabA[0]` and an implicit flow
`if tabA[0] == 0 { tabB[0] = 1 }` both need one thread that reads an `A` carrier and writes a
`B`-observable one: its domain `d` must admit `A → d` (`I001`) and `d → B` (`I002`), hence
`A → B`. The Lean rule is thread-granular -- the footprint form of the statement-level rule --
and refuses both. The checker's DIAGNOSTIC should be statement-granular: name the write, and
either the read in its expression (explicit) or the condition of the enclosing branch or loop
(implicit).

**Calls.** Labels travel through the call graph: a function is checked at the domain of every
root that reaches it, so a helper shared by both tenants must pass both checks (a pure helper
over its parameters does; a helper that writes `konto` does not). Parameters and results are
thread-local values; they carry the thread's domain.

### 7.3 What the thread-granular rule refuses that a finer rule would admit

One thread that handles both domains -- a dispatcher that reads `A` and writes `B` on paths that
never mix the two. The statement-level rule (every write checked against its expression's reads
and the reads of its enclosing conditions, with a program-counter label) would admit it; its
proof needs a per-thread pc label and a low-equivalence on partially visible thread states, and
is outside this proof. Until then: one thread, one domain.

### 7.4 Locks shared across domains (proposal, not in `flussB`)

Taking a lock writes "who holds it"; blocking on it reads that. A lock taken by roots of two
incomparable domains is a channel through ENABLEDNESS, which the theorem does not see (§3). The
checker should refuse it (`I005`): a lock may be taken only by roots whose domains are all below
one label, and that label must flow to every domain that takes it -- in the tenant case, a lock
is private to a tenant or taken by the kernel domain alone.

## 8. Declassification

A flow rule that forbids every `A → B` flow is sound and refuses much legitimate code -- the
history of JIF and FlowCaml. Every usable system needs controlled release: a tenant's own data
back to that tenant through a shared service, an aggregate statistic, an error code.

**Surface proposal.**

```
let n : u32 = declassify (zaehle_aktive(konten_a)) to tenant_b;   -- an escape hatch
```

`declassify e to d` is admitted only in functions of the domain that owns every carrier `e`
reads, and only where the condition of every enclosing branch is itself below `d` (the release
decision is not attacker-controlled: robust declassification).

**The weaker statement** (Lean: `FreigabeNI`, statement only). Release breaks plain NI by
construction, so the theorem weakens to DELIMITED RELEASE: the escape hatches, evaluated on the
start memory, form one value `frei sp`; two runs whose starts agree on `B`'s view AND on the
released values show `B` the same. Proved: plain NI implies it for every hatch
(`freigabe_aus_abwicklung`); with nothing released it IS plain NI (`freigabe_leer_iff`); the
leak's counterexample to plain NI (`n3_verletzt`) is no counterexample to delimited release with
the hatch `tabA[0] == 0`, because its two starts differ in the released bit
(`n3_freigabe_kein_gegenbeispiel`).

**Why the proof gets harder.** (1) The release step writes an `A`-derived value to a `B`
carrier, so `NiGleich` is not preserved step by step; the invariant must carry "the values
released so far agree". (2) That holds only if the released value is a function of the START
memory: the `A` data a hatch reads must not be updated before the release (the side condition of
delimited release), or the statement weakens again (gradual release). (3) In a concurrent run
the MOMENT of the release is observable and depends on `A`'s progress; under a fixed timetable
that is harmless, under any other scheduler it is a second channel.

## 9. Measurement: what the plain rule refuses in the corpus

The corpus (`beispiele/*.gab`, 107 programs) has no tenants; it cannot answer the question for
real tenant code. What it can answer: the programs with more than one root, split naturally --
each root its own domain, each carrier labelled with the root that owns it, a carrier touched by
both roots labelled every way there is.

Six programs have more than one root (`concurrent` or two `entry` points): 07, 59, 108, 109,
124, 125. Two of them have a Lean form (108 as a mechanical export, 124 as the hand model in
`MehrfadenZeuge.lean`); two more corpus programs with a Lean form, 104 and 118, have two
functions each that a tenant split would make roots. For these four the answer is mechanical
(`Nichtinterferenz/Korpus.lean`, by `decide`):

| program | roots | result |
|---|---|---|
| 108 disjoint-start-locks | `read_a` / `read_c` | ADMITTED (`k108_fluss`); the crossed labelling is refused (`k108_gekreuzt`) |
| 104 referenz | `einzahlen` / `lies` | REFUSED for every label of `Konto` (`k104_abgelehnt`) |
| 118 sperrinvariante-erhaltung | `gib` / `nimm` | REFUSED for every labelling of `A`, `B` (`k118_abgelehnt`) |
| 124 two-threads-private | `hauptA` / `hauptB` | REFUSED for every label of `konto` (`k124_abgelehnt`) |

By hand, for the two that have no Lean form: 109 (`entry_a` writes `T`, `entry_b` writes `U`)
and 59 (timer writes `Takte`, syscall writes `Auftraege`) touch disjoint carriers and pass; 125
(both roots write `z`) is refused. 07 (`syscall`, `nmi`) is kernel code of one domain.

**One more labelling admits 124.** With a fourth domain `T` above both tenants (an auditor),
`konto` labelled `T` is a write-only sink for the tenants -- both may write it, neither may read
it -- and 124 passes (`ZeugeMehrfaden.lean`, `n124_fluss`; every premise of `nichtinterferenz`
jointly on that fixture with a reached run, `n124_zeuge`). The same fixture shows the gap of
§7.4: its lock `L` is taken by both tenants.

**Reading.** Every refusal is a carrier WRITTEN by two roots (or written by one and read by the
other). That is interference in the theorem's sense -- one root's activity is visible to the
other -- even where no tenant DATA flows (124 writes constants). The plain rule cannot tell the
two apart. What would measure the real question is a program the corpus lacks: a two-tenant
service with per-tenant tables, a shared request queue, a shared log and a shared error-code
path -- the three places where tenant code in practice needs a release (§8) or a
kernel-domain intermediary.

## 10. The obligations, counted

The extension is the product promise only if the checker supplies its premises. For
`nichtinterferenz`:

| premise | who supplies it |
|---|---|
| `flussB π P fs cs L = true` | **checker-decided** (`I001`–`I004`), from labels the user writes |
| `∀ g, g ∈ fs`, `∀ c, c ∈ cs` | **checker/exporter**: the finite enumeration of functions and carriers |
| `hW`: threads start at labelled roots | **checker** for the labels; the **runtime** for "threads start only at declared roots" -- the same assumption as A4 of `schlusssatz_104` (thread creation) |
| `GutO O`, `RegLokal O` | **named hardware assumptions**, the ones every G theorem already carries |
| `OrakelTreu …` | **named assumption** about foreign code and devices labelled below `B`; in the same list as the hardware profile |
| scheduler class (`hplan`, or the fixed timetable) | **named runtime assumption**, in the SAME list as the lock primitives and thread creation (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 4, §5) |
| blocked slots idle (enabledness) | **named runtime assumption**, same list; plus the checker proposal `I005` |
| same `B`-inputs, same schedule | the STATEMENT's premises (they say what "learns nothing" means) |

**User logic: none.** No contract, no obligation, no proof per program. The flagship obligations
(`KoerperGutS` and the like) are not premises of noninterference; a program need not be
verified to be isolated, only labelled and checked.

For the binary, the transfer from machine G to the emitted C is stage (b) of the
translation-validation plan -- DRF-SC, the lock primitives (a ticket lock must reveal nothing but
"held or not"), thread creation, the scheduler -- with the same named assumptions, not a second
list.

**The list in Lean** (2026-09-15, `CNebenlaeufig.lean`; PLAN-UEBERSETZUNGSVALIDIERUNG §7.4). The
runtime entries of the table above are one structure, `LaufzeitC`, a hypothesis of the stage (b)
closing theorem (`schlusssatz_124`):
* thread creation -- `FadenStartC`: threads start only at declared roots, each root on at most
  one thread, from the declared initial memory, with no lock held (the C counterpart of `hW`'s
  runtime half and of `Laufzeit` (d) of the goal theorem, which it yields: `laufzeit_w`);
* the lock primitive -- every behaviour of the runtime's `L_nimm`/`L_gib` is one of
  `sperrAbstrakt`: acquire only a free lock, release only one's own, program memory untouched;
  and it reveals nothing but held or free: whether a call proceeds depends on that lock's holder
  entry alone (`sperrAbstrakt_nur_eigen`), and it changes no other entry
  (`sperrAbstrakt_rahmen`).
The two scheduler entries (the scheduler class, blocked slots idle) are premises of
`nichtinterferenz_planer` only: the stage (b) safety statement is quantified over EVERY schedule
(every interleaving is an SC run), so it needs neither. DRF-SC itself is the separate named
premise `DRFSC`, whose hypothesis (race freedom of the C) stage (b) proves from machine G.
What stage (b) does NOT yet give is noninterference for the C: it carries single-run facts
(every C configuration is related to a G machine where the goal holds). Carrying a PAIR of runs
needs two more facts, neither proved: that two C runs under one schedule lift to two G runs
under one schedule (the lifting `sim_lauf` chooses G segments per C step, and their lengths may
differ between the two runs), and that the relation determines the observed C state from the
observed G state.

## 11. Comparison: seL4's confidentiality proof

seL4's information-flow proof (Murray et al., 2013) states intransitive noninterference over
the kernel's abstract specification, proves it by unwinding conditions over single steps
(roughly the pair used here: a step consistent on what the observer sees, and a step of an
unobservable domain leaving that view alone), and transfers it to C through
the refinement proof, which preserves the property because the specification was first made
deterministic. It holds only for a static domain schedule with a fixed timetable, and it
excludes timing channels. The differences: seL4 proves isolation for ONE program, the kernel,
with the partition fixed by its configuration; here the metatheorem is proved for EVERY program
of the language over machine G, and the per-program premises are a decidable check. seL4's
theorem reaches the C code; this one stops at machine G until stage (b) of the
translation-validation plan exists. Both exclude timing; both need the fixed timetable (seL4 by
construction, here as the instance of the scheduler condition).

## 12. How it is proved

1. `Grundlagen.lean`: labels, `beob`, `NiGleich`, `AbwicklungG`, `ni_allgemein`,
   `ni_aus_abwicklung`, `ni_planer`, `ni_zeitplan`.
2. `Schritt.lean`: `kSchrittK`, the step of one thread as a FUNCTION of its ghost-free state and
   the memory. Two derivations of G over two machines cannot be paired rule by rule (their
   premise types mention `(M.faeden f).kopf.f`); two applications of one function to the SAME
   ghost-free state can.
3. `SchrittTreu.lean`: `schrittK_von` -- each of the 74 rules computes `kSchrittK`.
4. `Lokal.lean`, `LokalSchritt.lean`: the syntactic flow check `nS/nB/nE`, `blatt_rel` (a leaf is
   local, relationally) and `schrittK_rel` (one state, two memories agreeing on `T`, reads in
   `S ⊆ T`: equal new state, memories agreeing on `T`).
5. `Invariante.lean`: `knr_erreichbar` -- every frame of every thread passes the flow check on
   every reachable machine.
6. `Fluss.lean`: `flussB`, `abwicklung_aus_fluss` (local respect from the write frames and
   `schritt_traeger`; step consistency from `schrittK_von` + `schrittK_rel` + `knr_erreichbar`),
   and the three combined theorems.
7. `Zeuge.lean` (namespace `NIZeuge`): a two-tenant program admitted, with NI on two concrete
   runs under a fixed timetable from memories that differ in tenant A's table (`n1_zeuge`); a
   shared lock-free counter refused for every label (`n2_abgelehnt`); a leak refused for every
   root domain and violating NI on two concrete runs (`n3_verletzt`).
8. `ZeugeMehrfaden.lean`: every premise of `nichtinterferenz` jointly on the project's
   two-thread reference fixture (a lock, a shared account, two private tables, a reached run),
   under the write-up labelling (`n124_zeuge`).
9. `Korpus.lean`, `Freigabe.lean`: §9 and §8.

## 13. What is outside, precisely

* Timing and every physical side channel (§3).
* Schedulers whose choice depends on more than `B`'s observation (§5).
* Enabledness: runs in which a scheduled thread cannot step; locks shared across domains (§7.4).
* The statement-level (pc-labelled) rule: one thread serving two domains (§7.3).
* Declassification: statement only (§8).
* Device OUTPUT: a register write is not part of the world in the model (`Orakel.regSchreib`
  returns `Unit`), so what a device does with it is not observed by anyone.
* Every level below machine G: the emitted C, the compiler, the binary, the hardware.
* Integrity (A cannot corrupt B) follows for carriers from the write rule `I002`, but is not
  stated as its own theorem.
