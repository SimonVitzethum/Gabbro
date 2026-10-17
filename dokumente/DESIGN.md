# Design

**The architecture of Gabbro, GabbroV and the CaprockOS plans: decisions, and the reasons they
still stand.** This is neither a work list ([`TODO.md`](../TODO.md)) nor a record of what was
measured ([`MESSUNGEN.md`](MESSUNGEN.md)); what the language *is* lives in
[`SPRACHE.md`](SPRACHE.md), what is *proved* in [`BEWEIS.md`](BEWEIS.md).

Every statement carries its standing, because a design document that mixes the three is worth
less than a shorter honest one:

| | |
|---|---|
| **[DECIDED]** | settled; changing it is a decision with a cost, not an edit |
| **[PROPOSED]** | argued for here, not adopted |
| **[OPEN]** | known question, no answer yet |

*CaprockOS lives in its own tree, which is **read-only** reference from here: nothing in this
repository is committed into it, and corrections for it are findings (§9), not patches. The
CaprockOS sections (§§5–8, 10–11) record decisions of the project's owner that cannot be
verified from this tree; they are kept as stated.*

---

## 1. The thesis

**[DECIDED]** *Plumbing belongs to the language, not to the proof.* Verifying system software is
dominated by obligations that are not about the system — index bounds, overflow, aliasing,
framing, lock order, data races, termination, phase, leafness, publication, refinement: the same
classes in every kernel ever written. Gabbro carries them in the grammar, so what is left to
prove is the program's own logic. The economic claim is one sentence:

> **A proof template falls once, not once per program.**

**[DECIDED]** **No SMT solver in the trust base.** Where a solver would get slow and answer with a
timeout, a grammar names the construct it will not carry, and why, **by name**: the answer is
yes, or no with a code — never "unknown", never "maybe tomorrow". This is a statement about the
trust base, not about automation (§4.2).

**[DECIDED]** Multicore and DMA are set, not optional: the pairing of publication and reception is
load-bearing, and the device space carries real statements rather than a classification.

**[DECIDED]** *Safety is never traded for features.* No work weakens a guarantee — memory
safety, race freedom, contracts, costs, lock discipline — to make a wall go green; a wall that
only yields by weakening is recorded as a finding. *Simplicity is a goal, but no guarantee is
given up for it*: ceremony goes down while the register of passes stays constant; `ensures` is
never derived, and a refusal is never turned into a warning.

**[DECIDED]** *Guarantees come from generic theorems only.* Nothing in the compiler, checker or
printers exists for particular programs; the verification must be provable for **every** source
text, with its statements computed in Lean from the source rather than trusted from a Rust
print. Per-program Lean files are witnesses off the trust path.

**[DECIDED]** *Everything new is modelled in Lean before it is merged:* a new construct,
runtime primitive or template gets its semantics, its checker side, its front-end and its
correspondence — otherwise it stays unmerged. A theorem over syntax needs a non-degenerate
witness.

## 2. One principle, applied three times

**[DECIDED]** Where a component is too large or too messy to verify, it is **not trusted**: it
shows its work, and a small checker rechecks it. The property this buys is one-way failure — *a
broken component can only reject good inputs; it can never let a bad one through* — and it is the
building principle of the project, not a coincidence.

| Where | The untrusted component | What it emits | Who checks |
|---|---|---|---|
| Compiler | the Rust checker and the code producers (about 158 000 lines of `std`-only Rust, three crates, no third-party dependency) | a certificate per program | Lean |
| Drivers | a binary rewriter (§6) | **[PROPOSED]** a certificate per driver | a small independent checker |
| Logic | **[PROPOSED]** an SMT solver as an oracle | a proof certificate | Lean |

## 3. The language and its compiler

**[DECIDED]** The compiler is **never verified**. Proving it was costed at roughly 700 000 lines
of proof, and it would have been proved against a second copy of the model rather than against
the model. The checker is likewise never self-applied: a project that rebuilds its checker has
none.

**[DECIDED]** **The checker comes first and the backend is untrusted.** What the checker refuses
never reaches a producer; every unlowered form is refused *by name*, not guessed.

| Backend | Standing |
|---|---|
| **LLVM** (`gabbro llvm`, x86-64 and AArch64) — Gabbro to IR with **no C, no libc, no linked runtime** | current ([`LLVM-BACKEND.md`](LLVM-BACKEND.md)) |
| **C11 emitter** | **deprecated**; keeps building where it builds, its refusals (`C001` and kin) stand, no new construct is shaped for it ([`C-SPEICHERMODELL.md`](C-SPEICHERMODELL.md)) |
| **Native machine code with validation of the final bytes** | the long-term path; needs a **Lean model of the CPU** first (AArch64 on the Sail Arm specification with the multicore memory model added in Lean, [`ARM-PLAN.md`](../ARM-PLAN.md); x86-64 work has stopped), then a per-access bridge to the existing concurrency model. [`PLAN-UEBERSETZUNGSVALIDIERUNG.md`](PLAN-UEBERSETZUNGSVALIDIERUNG.md) |

### 3.1 Translation validation

**[DECIDED]** For every program the untrusted compiler accepts, it emits a certificate that Lean
checks. The intended closing theorem: *Lean accepts the certificate ⟹ the source text parses to
a program `P`, `P` satisfies the model — types, safety, lock order — and the produced code
refines `P`.* What stays in the trust base: the Lean kernel, the hardware profile, and named
assumptions about devices and the scheduler — as **premises inside the theorem, not prose beside
it**. The forms that cannot have a correspondence lemma by construction (inline assembly, device
reads) are *named assumptions*; the guardian that watches emitted forms distinguishes three
states, not two: **lemma · named assumption · no semantics**.

The five pieces of the original chain: **T3** a parser in Lean (the certificate starts from the
source text, not from a representation Rust produced), **T1** model certificates (typing and
safety as decidable certificates per constructor), **T4** semantics of the produced code, **T2** a
correspondence re-checker (*this* program consists of exactly those correspondences — the piece
that closes the chain), **T5** proof templates (each recurring obligation gets a soundness
theorem over the real semantics). **Standing:** the chain is closed for five programs (README §5 counts them)
against the legacy C backend; for every other program the Rust checker and the producers are
still trusted. **[OPEN]** The concurrent half (a concurrent model run against a run with
interleaving, with the lock specification, thread creation and DRF-SC as named assumptions) is
the largest single open piece and is not on the sequential chain's critical path.

**[PROPOSED]** *Pull the witness forward:* close the chain end to end for **one** real program in
a minimal form first. A closed chain over one program changes the character of the project more
than any coverage increase, because every further form is then routine work on a chain that
already carries.

### 3.2 Standing decisions of the language

* **Refuse by name, never interpret.** One code per reason, a sentence per code
  ([`PRUEFER.md`](PRUEFER.md)); an unknown version or a crooked length is a named refusal, never
  a guess.
* **The operating system is user logic, never an assumption in the compiler.** A system call is
  a generic gate whose contract the program or its binding library declares *in Gabbro*; the
  Lean model, the checker and the compilers know no operating system and no libc. **No
  handwritten C in a finished binary as far as possible**: runtimes and bindings are Gabbro,
  OS access goes through `syscall` items, and handwritten C or assembly stays only where Gabbro
  cannot express the thing, each piece with its written reason. Code moved from C into Gabbro is
  checked like user code, with no relaxed mode. (`SPRACHE.md` §16.)
* **Memory from outside comes as a region, never from a number.** No int-to-pointer
  conversion; an external allocation is a region of declared extent whose contract (user logic)
  says it is fresh and disjoint.
* **Heap, but with a ceiling.** Dynamic structures are in scope on regions with a declared
  ceiling and refuse-on-full; a heap without a ceiling stays refused by default. **[PROPOSED]** An
  explicitly declared region *without* a ceiling as an opt-in beside the default (every
  allocation may fail and must be handled; the static memory bound is lost for such a program).
  *The heap's ceiling is a limit, not a standing reservation:* memory is taken when needed and
  given back when not. (`SPRACHE.md` §17.)
* **Floats are in scope** (a concrete IEEE model); probabilistic statements are out of scope.
* **Rule A: no construct without a measured need.** If the measurement shows the need is absent,
  the *named refusal* is the result, and a good one.
* **A target-portable compiler.** The direct compiler must support extensible profiles for
  arbitrary operating systems and freestanding environments: ABI, image and entry requirements
  are checked profiles, environment services are Gabbro bindings with user-logic obligations,
  and nothing implies Linux, POSIX, libc or ELF. This is a requirement, not a claim that such
  targets exist.
* **Hardware model: common x86-64 / Arm architecture, not a vendor.** Whatever a vendor calls
  undefined or model-specific stays **free** in the model (all allowed results, never one
  observed value).

### 3.3 How a decision is made

Process rules that repeatedly paid for themselves:

1. **Before building, ask whether the obvious form already parses.** Write it down and run it
   through the *unchanged* checker: if it parses, where does it fall — at the parser, or at
   something behind it? Several "missing constructs" turned out to be a missing callee or a
   missing reader, and one booking was simply wrong.
2. **A decision document comes before the build** and has four parts: the finding with the command
   that recomputes it; at least two forms, with arguments for *and against* each; the decision
   with its reason — **the reason is the concept, not the price**; and **what the decision does
   not buy**.
3. **No new word without checking it against an existing notion.** A second word for an existing
   concept costs more than a second site for an existing word; a new word costs the keyword
   table, the grammar's vocabulary and its terminal count.
4. **A contract is a hypothesis, never an axiom.** Entering a callee's postcondition as an axiom
   builds a prover that closes any nonsense as soon as one `ensures` is false; it belongs in the
   theorem as a premise.
5. **A delegation is booked by name.** Where the checker hands something to a downstream tool
   (register allocation to the C compiler, say), the product says so next to the assembly; a
   silent delegation is not a booking.
6. **A ratchet is not moved when it jams; the cause is cured.** If one falls in the good
   direction it is still a finding, and the mark is re-set with its reason written out.
7. **A correction is struck, not painted over,** with the old wording beside it, and a count that
   falls by a correction is booked as no work.
8. **A report ends with what was NOT built and why** — usually its sharpest sentence.

## 4. GabbroV — the logic obligations

**[DECIDED]** GabbroV is for programs written **in** Gabbro, not for Gabbro itself. It emits, per
program, a logic specification in Lean 4 against which the program's logic can be proved:

> Gabbro proves everything except logic. The programmer proves the logic. GabbroV writes down
> exactly what that is.

**Standing:** the goal is one Lean theorem proved over the model (`gabbro_ziel`; README §5 with
its limits). The checker inside the statement is the Lean checker, and the bridge to the Rust
checker and to the produced binary is open. "Proves everything except logic" is the design; for
the implementation it is not yet a theorem. **[DECIDED]** What the generator pays for:
composition over every call, the frame, the rule of every loop, the precondition at every call
site, and the wiring from the obligations to the contracts. What a person owes is the *statement*
of each obligation with every hypothesis the proof can need standing in front of the turnstile —
a person who must first re-derive framing, aliasing and loop induction gives up before reaching
their own statement. ([`GABBROV.md`](GABBROV.md).)

### 4.1 The three criteria

* **E1 — completeness of treatment.** Every obligation gets a verdict; none is silently skipped
  or lost to a parser error. Checkable by one command, line count in against line count out, in
  *every* run; a deviation is a failure, not a hint.
* **E2 — decision share, with a named exception list.** How many treated obligations end in
  *passed* or *refuted* rather than *undecided* — **named, not a percentage**, because a
  percentage lets the exception list grow silently with every hard obligation. An obligation
  joins the list only for a structural reason; "the solver does not get through" is *undecided*,
  not an exception.
* **E3 — channel fidelity.** A specification that says something no Gabbro program can assert is
  a failure, not a finding.

**[PROPOSED]** The metric this gives back: *obligations discharged by the generator against
obligations handed to the person*, per program — prover-independent, needing no prover run, and
the project's actual promise. **[OPEN]** A second number beside it: of the generated files, how
many carry the composition the generator promises and how many state it without delivering it.

### 4.2 The solver question

The measurement splits the sayable obligations into a quantifier-free shape and those needing
quantifiers, folds or reachability, and seems to force a choice between an SMT solver in the trust
base and weaker automation. **[PROPOSED]** That is a false alternative: "no SMT" was a decision
about the *trust base*. A solver run as an **untrusted oracle** emitting a certificate Lean
rechecks violates nothing — §2 a third time. The quantifier-free share is where certificate
reconstruction works well; the rest is where a solver would have been unreliable anyway.

### 4.3 Synthesis from a manifest (GabbroK) — **[PROPOSED]**, no code

*A manifest in, a program out — or a refusal that names the manifest line that cannot be built.*
Two exits per line, **emitted** (Gabbro source with an anchor per line) or **refused** (the checker
diagnostic quoted verbatim), and a line-count comparison that aborts on deviation (E1 wired in).
The oracle is always `gabbro check` and the producers; the tool never joins the trust base. The
synthesis manifest is a second file with a second subject — *what the program must be* — kept
apart from the build manifest (which says which files form a unit); conflating them repeats the
"one register over two things that drift" class. Stages: freeze the spec (versioned, every
reader refuses an unknown version), a skeleton expander, a body search per obligation kind
(templates first; loops only in the `traverse` and `retry` forms, anything else is *undecided*,
never guessed — and the search never stops at its first hit), a back-mapping from every refusal
to the manifest line, a ratchet keyed `(name, class, text)`. Not on the path to anything else.

## 5. CaprockOS — scope

**[DECIDED]** Everything is formally verified except the user's own programs and the Linux
hardware drivers. Not only the microkernel: shell, file system, network stack, firewall and the
rest are written in Gabbro and verified. **[DECIDED]** No adopted third-party userland — a system
whose central claim is that verified components are cheap to write cannot stand on a large body
of unverified code. **[DECIDED]** Until the base components exist, only what can run on them
runs; no interim product. **[PROPOSED]** Build order, chosen to serve the product and produce
comparable numbers: network stack, component and process manager, firewall, file system, shell
last. Networking protocols are ordinary Gabbro modules over the program's own gates (HTTP and TLS
are neither built into the language nor forbidden).

**[PROPOSED]** *The component set is also the measurement.* Each component has a published
counterpart verified with conventional tools at a known proof cost; a component reaching the same
guarantees at a fraction of the proof burden gives the proof-to-code figure a measured value
against named prior work. **[OPEN]** What runs tenant workloads between now and the point where
that set exists — a narrower first product or a longer wait; a decision, not something the
schedule should discover.

## 6. Drivers

**[DECIDED]** No compatibility layer and no runtime. Compiled Linux driver binaries are rewritten
by a separate tool — **the Modifier** — so they run under Caprock's discipline. It is GPLv2, a
separate program invoked as a tool, never linked into the kernel. **[DECIDED]** The boundary is a
real boundary: a rewritten driver runs in its own isolation domain and talks over a defined
interface, never by direct calls into kernel internals — what the contract wants, and what keeps
the licence question from arising. **[PROPOSED]** The Modifier is a second compiler and currently
trusted: everything the kernel claims about isolation rests on the rewriting being correct, at a
level without types or source. It should emit a certificate per driver, rechecked by a small
independent checker, and the kernel's isolation theorem should carry that certificate as a named
premise (§2's one-way property). **[OPEN]** No driver mirror exists yet.

## 7. Namespaces and the file system

**[DECIDED]** No single root tree: one tree per user, plus one each for drivers, programs and the
kernel. What this buys is *structural*: no path by which a user's tree can name the kernel tree,
so the whole traversal-to-root class of defects does not exist — the same move as a grammar that
refuses a construct. **[PROPOSED]** Crossings between trees happen by handle, never by a name that
resolves across trees. **[OPEN]** Who assembles a process's namespace, and out of what: granted
at creation and immutable afterwards is the provable case; run-time mounting enlarges the proof
surface considerably. **[PROPOSED]** The tree separation is a short, cheap invariant; what costs
in a verified file system is *crash consistency* — what holds after power loss mid-operation,
over a block device that may reorder writes — and a schedule planning access control without
crash semantics is not slightly wrong.

## 8. Keys, signing and updates

**[DECIDED]** The kernel tree is writable only with a cryptographic key plus a password; keys are
unique per installation and change only on reinstallation of the microkernel; the private key is
never on the device. Kernel updates come only from the CaprockOS mirrors, and the general signing
key is never on a mirror — an image is signed offline and uploaded afterwards. **The property
bought: no process can change the kernel without user input.** Offline signing leaves a mirror
compromise able to withhold, unable to forge. What it does not cover — all **[PROPOSED]**:

* *Freshness.* A compromised mirror can serve an old, validly signed image with a known hole;
  signed metadata with an expiry, or a monotonic counter in the installation, closes it. Rare
  updates make this worse: silence is the normal state, so withholding is invisible.
* *What is signed.* An offline key does not protect against signing the wrong thing;
  **reproducible builds** make a signature "recheck it" instead of "trust me".
* *A transparency log* against **targeted delivery** and a stolen offline key: an attacker with the
  key can still sign, but no longer *secretly*.
* *Key rotation is circular as specified* (a key changes only through an update signed with that
  key): a two-tier hierarchy — an offline root certifying signing keys — fixes it; The Update
  Framework already specifies roles, rotation, revocation, thresholds and rollback protection.
* *Two update models:* user input per kernel change is right for a workstation and impossible for
  a fleet, where immutable images are redeployed and the authority sits in the pipeline; both use
  the same mirror and freshness rules.
* *Write the signing procedure down now* — which machine, which checks, who witnesses — because
  an offline key is used rarely, by a human, and most urgently when something is on fire.

## 9. Findings handed to Caprock

Findings whose subject is Caprock, taken out of this project's work list so that a task list does
not sort for two projects. Measurement base: Caprock `arch/x86_64` at commit `a1bf707` (read
only).

| | Finding | Standing |
|---|---|---|
| N1 | the two lock orders in the kernel's `system.rs` contradict each other: the header places `MEM` innermost (R4, "never holds another lock") and a later comment places it *before* `SCHEDS[*]`. **Measured:** `MEM` holders that take another lock: 0 of 54; `MEM` taken after outer locks: 2 (both under `CAPS`); nestings of `MEM`/`SCHEDS`: 0 — `MEM` is a leaf, the header is right and the later comment wrong. Proposal: `CAPS < {EPS[i], NTFNS[i]} < SCHEDS[*] < FP_STATES < MEM` | both comments re-read at the base; **not applied** |
| N2 | `FP_OWNER` is named an atomic tender of the lock order but appears in neither documented order, though the deadlock argument relies on it; the ordering census needs a column "order participant" | open |
| K1–K3 | removals, not refutations, in the ordering census: a lock removes the atomic; the inside of a construct counts toward the template surface; `accumulates` with a record is strictly better than the original at one site | taken |
| FP | FP state is **eager on x86** (`system.rs`, with the CVE justification), lazy on aarch64; the only aarch64 tree in reach is an older snapshot of the same lineage, not a second kernel | the decree hits the other architecture |
| — | two plumbing obligations remain: an index after `31 − leading_zeros()` needs the data-structure invariant; every refinement lemma if the lowering is not flat enough | open |
| D8 | progress/starvation falls under none of M1–M4; whether it needs a sixth mechanism is a question for the scheduler guarantees, not the type system | open |

## 10. Licensing

**[DECIDED]**

| Component | Licence |
|---|---|
| Gabbro — compiler, checker, Lean semantics | AGPL-3.0 with two additions ([`LICENSE-ADDENDUM.md`](../LICENSE-ADDENDUM.md)): a program written in Gabbro is **not** a derived work; and a notice is owed only if the result is presented as verified, proved or secure |
| Caprock kernel and every self-written OS component | AGPL-3.0 |
| The Modifier | GPLv2 |
| Mirror service software | AGPL-3.0 |
| Interface definitions, the driver contract | permissive — implementing against an interface must not infect the implementer |
| Documentation | CC-BY-4.0 |

The kernel's interface exception exists: services obtained by ordinary system calls do not make
the calling program a derived work. A driver mirror, when it exists, distributes under GPLv2 with
the complete corresponding source (including the Modifier and its invocation, since that is how the
shipped binary is reproduced), change notices and retained copyrights; no modified driver binary
is distributed today, so no distribution obligation has arisen. **[OPEN]** Whether a shipped image
containing kernel and rewritten drivers is a combined work (AGPL-3.0 and GPLv2-without-upgrade are
not compatible as one work; separate distribution avoids the question — a legal question, and a
further reason for §6's technically sharp boundary). **[OPEN]** Anything an application links (a
libc, the component API, an SDK) needs a linking exception of its own. **[PROPOSED]** SPDX
identifiers per file and a `LICENSES/` directory. **[OPEN]** The contribution arrangement: a
sign-off keeps friction low and freezes the licence, a contributor agreement keeps relicensing
possible and deters contributors — the decision whose cost rises fastest.

## 11. Release model and hot reload

**[DECIDED]** The kernel is not a rolling release: rare, signed, key-gated. Everything above it —
desktop, firewall, drivers, services — rolls, and Caprock hot-reloads processes and drivers
without reboot (the microkernel payoff). Minor versions stay interoperable across the supported
window. **[PROPOSED]** That rule must be *mechanically* checked: protocol and state schema are a
declared, versioned artefact, and a guardian falls when a minor bump changes them incompatibly.
**[PROPOSED]** The reload authority belongs in the frozen kernel: a hot reload is an authorised
code-injection path, and if its authority is part of the rolling layer it is circular.
**[PROPOSED]** Proof time is on every release's critical path, so proofs must be per component,
incremental and cacheable; steer by *proof-check wall clock per component* and by *proof survival
under semantically irrelevant code change* (reorder independent assignments, rename a local, see
whether the proof still closes) — measured at the first component, not the third.

**Across versions, two statements are needed:** each version is correct on its own, and every
reachable transition between versions preserves the invariants — the second does not follow from
the first. **[DECIDED]** **An abstract specification that both versions refine.** Every state
reachable in the old version is then meaningful in the new, and the sequence of configurations is
provable as a whole; *a template falls once, not once per program; an abstraction falls once, not
once per version pair.* **[OPEN]** What the abstract specification of each component looks like —
abstract enough that plausible future implementations refine it, concrete enough that refinement
says something. **[PROPOSED]** Per component class: stateless — swap directly; stable
representation — a version-tolerant format, migration a no-op; rich internal state — quiesce,
then a migration `m` with `I_old(s) → I_new(m(s))`, generated per version pair; owns hardware —
always quiesce; a transactional swap with rollback as the safety net.

**[DECIDED]** The honest claim: *no reboot for the rolling layer, with the state provably described
throughout.* Two limits no technique removes: **the kernel** (reloading components does not fix it,
which argues for keeping it small) and **the hardware** (microcode, firmware and side-channel
mitigations arrive through a restart). "Never a reboot" is neither achievable nor defensible.

## 12. Out of scope, deliberately

**[DECIDED]**

* **Functional correctness** of a program is the programmer's, not the language's.
* **The Linux drivers themselves**: what is checked is that a driver keeps its boundary, not that
  it drives its device correctly.
* **The Modifier and the compiler are not proved.** Both emit certificates; the certificates are
  checked. That is the mechanism, not a gap in it.
* **Timing channels.** Non-interference cannot be established in software on hardware with shared
  execution units; the contract states what it claims about functional interference and names
  timing channels as an assumption about the hardware configuration.
* **What a DMA-capable device does on the bus** is carried by the IOMMU and stands in the
  assumption list as such.
* **A verified libc** is not on the critical path — the isolation comes from the kernel boundary.
* **Generated and self-modifying code in user programs.** A JIT, a trampoline: none is analysed,
  because **the isolation guarantee is enforced, not analysed** — it rests on the kernel and the
  hardware. Code a program writes for itself runs in the same domain with the same authority and
  is exactly as harmless as any other code it runs. Two places lie just inside the line and are
  easy to lose: *the grant of execute permission* (a page made executable for one domain is never
  reachable from another — an ordinary footprint-and-label obligation, easy to forget) and *the
  Modifier* (its output runs with driver authority inside the verified perimeter — "generated code
  is the user's logic" covers every JIT and exactly one code generator not at all: our own).
* **Probabilistic statements.**

**[OPEN]** Who ships the runtime that tenant workloads run on, and with whose authority: if a
tenant brings it, it runs in that tenant's domain and the rule above settles the matter; if the
platform ships it and tenants share an instance, its sandbox becomes a platform guarantee — the
hardest component on any list, since it is where multi-tenant platforms actually break.

## 13. Comparison — who proves what

*An architectural comparison, not one of maturity: SPARK ships certified systems, ATS is an
academic lineage, Gabbro is pre-product. The statements about SPARK and ATS are external
characterisations and were not re-verified here.* The three make opposite bets on the same
question: **who proves what, and what happens when the proof fails.**

| | Gabbro | ATS | Ada/SPARK |
|---|---|---|---|
| plumbing (memory, races, framing, locks, overflow, bounds) | the language: grammar and passes; refused *by name* where unwritable | linear/dependent types, proof terms where types do not reach | language restrictions + flow analysis, the rest as contracts |
| functional correctness | the user, as Lean obligations per program (`NutzerPflichtA`) | the user, as proof terms | the user, as contracts + loop invariants + ghost code, discharged by solvers |
| hardware and foreign code | named assumptions *inside the theorem* as premises | `extern`, trusted | `Import` + contracts, trusted; driver boundary is prose |
| time and cost | in the language: `costs`, `held`, deadlines (the goal theorem carries only the syntax-computed bound) | not carried | not in the language |
| failure mode | yes, or no with a **code**: no timeout, no "unknown" | a missing proof is a type error | timeout, unknown, unproved-but-possibly-true — the verdict depends on solver behaviour |
| amortisation | one generator obligation per construct, proved once over the semantics; the per-program remainder is the user's logic | proof terms per program | the prover is reused, but every program pays its own VCs and solver time |
| concurrency | multicore and DMA required; race freedom a conjunct of the goal theorem; atomics ordered by an axiom | no verified-concurrency story of comparable depth | Ravenscar: restriction instead of proof; DMA has no story |
| output / trust | untrusted producers plus a checkable certificate (target; closed for few programs today) | unchecked C | GNAT to machine code; the toolchain is qualified, not the build output |

**When to pick which:** SPARK to ship a certified system today, in Ada, with an established
qualification path; ATS to experiment with linear/dependent types and proof terms inside one
language; Gabbro if the bet holds that plumbing belongs to the language — multicore plus DMA, time
as a first-class bound, refusals instead of timeouts, and a certificate a second tool checks — at a
price stated up front: the chain is built program by program, and what is not yet carried is refused
by name rather than promised. What is **not** claimed is the `Spec.lean` header's NOT CLAIMED list,
the one place that states it.

## 14. The open decisions, gathered

| | Where | Cost of deciding late |
|---|---|---|
| The contribution arrangement | §10 | rises fastest — after outside commits it needs everyone's agreement |
| Namespace assembly: fixed at creation or mutable | §7 | the proof surface of the file system |
| What runs tenant workloads before the component set exists | §5 | the product date, discovered rather than chosen |
| The abstract specification per component | §11 | the whole hot-reload argument rests on it |
| Combined-work question for a shipped image | §10 | a legal answer needed before anyone else operates the system |
| Whether a header audit finds Linux-derived code in AGPL parts | §6 | quiet until it is loud |
| Who ships the tenant runtime, and with whose authority | §12 | decides where the verification perimeter ends |
