# Design

**The architecture of Gabbro, GabbroV and CaprockOS, in one place.** This document records
decisions and their reasons. It is not a plan (that is [`TODO.md`](TODO.md)) and not a record of
what was measured (that is [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md)).

Every statement carries its standing, because a design document that mixes the three is worth
less than one that is shorter and honest:

| | |
|---|---|
| **[DECIDED]** | settled; changing it is a decision with a cost, not an edit |
| **[PROPOSED]** | argued for here, not yet adopted |
| **[OPEN]** | known question, no answer yet |

*The CaprockOS sections live here for now because this is where the reasoning happened. They
belong in the Caprock tree once that tree has a place for them.*

---

## 1. The thesis

**[DECIDED]** Plumbing belongs to the language, not to the proof.

Verifying system software is dominated by obligations that are not about the system: index
bounds, overflow, aliasing, framing, lock order, data races, termination, phase, leafness,
publication, refinement. Eleven classes, the same eleven in every kernel ever written. seL4 pays
roughly twenty lines of proof per line of code, and its verified configuration is single-core
without DMA.

Gabbro carries those classes in the grammar, so that what is left to prove is the program's own
logic. The economic claim underneath is one sentence:

> **A proof template falls once, not once per program.**

**[DECIDED]** No SMT solver in the trust base. Where a solver gets slow and answers with a
timeout, a grammar names the construct it will not carry and why, by name. This is a statement
about the trust base, not about automation — see §4.3.

**[DECIDED]** Multicore and DMA are set, not optional. The pairing is load-bearing and the
device space carries real statements rather than a classification.

## 2. One principle, applied three times

**[DECIDED]** Where a component is too large or too messy to verify, it is not trusted. It is
made to show its work, and a small checker rechecks it.

| Where | The untrusted component | What it emits | Who checks |
|---|---|---|---|
| Compiler | the Rust checker and emitter, ~110 000 lines | a certificate per program | Lean |
| Drivers | the binary rewriter (§6) | **[PROPOSED]** a certificate per driver | a small independent checker |
| Logic | **[PROPOSED]** an SMT solver as an oracle | a proof certificate | Lean |

The property this buys is one-way failure: **a broken component can only reject good inputs. It
can never let a bad one through.** That is why the same shape appears three times; it is the
building principle of this project, not a coincidence.

## 3. Gabbro — the language and its compiler

**[DECIDED]** One output: C11 plus inline assembly. The compiler is safe Rust with zero external
dependencies.

**[DECIDED]** The compiler is never verified. Proving it was costed at roughly 700 000 lines of
proof, and it would have proved it against a *second copy* of the model rather than against the
model itself.

### 3.1 Translation validation

**[DECIDED]** For every program the compiler accepts, it emits a certificate, and Lean checks it.
The closing theorem:

> Lean accepts the certificate ⟹ the source text parses to a program `P`, `P` satisfies the
> model — types, safety, lock order — and the emitted C refines `P`.

**[DECIDED]** What remains in the trust base: the Lean kernel, the C compiler, the hardware
profile, and named assumptions about devices and the scheduler. Those assumptions stand as
premises inside the theorem, not as prose beside it.

The five pieces:

| | What it establishes |
|---|---|
| **T3 — Parser in Lean** | source text → `P`, so the certificate starts from the source and not from a representation Rust produced |
| **T1 — Model certificates** | `P` satisfies the typing and safety rules, by a decidable certificate per constructor |
| **T4 — Semantics of the emitted C** | memory model, integer semantics, a full UB list, one correspondence lemma per emitted form |
| **T2 — Correspondence re-checker** | *this* C program consists of exactly those correspondences. **The piece that closes the chain** |
| **T5 — Proof templates** | each recurring obligation gets a soundness theorem over the real semantics |

**[DECIDED]** Forms that cannot have a correspondence lemma by construction — inline assembly,
device reads — become *named assumptions* carried as premises, not silent gaps. The guardian that
watches emitted forms distinguishes three states, not two: lemma · named assumption · no
semantics.

**[OPEN]** The concurrent half: the correspondence between a concurrent model run and a C run
with interleaving, with the lock specification, thread creation and DRF-SC as named assumptions.
This is the largest single open piece, and it is deliberately not on the critical path of the
sequential chain.

### 3.2 Ordering

1. Finish the Lean parser — generic, round trip.
2. Close the C-semantics gaps.
3. Build T2.
4. Bind the remaining templates.
5. The concurrent half.
6. The closing theorem with a witness, then a second witness on a program with real sharing.

**[PROPOSED]** Pull the witness forward: build T2 first in a minimal form, covering only the
forms one real program needs, and close the chain end to end for that one program. A closed chain
over one program changes the character of the project more than any coverage increase, because
afterwards every further form is routine work on a chain that already carries.

## 4. GabbroV — the logic obligations

**[DECIDED]** GabbroV is for programs written **in** Gabbro, not for Gabbro itself. It emits, per
program, a logic specification in Lean 4 against which the program's logic can be proved.

The division of labour it makes visible:

> Gabbro proves everything except logic. The programmer proves the logic. GabbroV writes down
> exactly what that is.

**[DECIDED]** What the generator pays for: composition over every call, the frame, the rule of
every loop, the precondition at every call site, and the wiring from the obligations to the
contracts. What a person owes: the statement of each obligation, with every hypothesis the proof
can need standing in front of the turnstile. That last clause is the design decision that makes
the remaining obligation workable — a person who must first re-derive framing, aliasing and loop
induction gives up before reaching their own statement.

### 4.1 The three criteria

**[DECIDED]**

- **E1 — completeness of treatment.** Every obligation gets a verdict; none is silently skipped,
  none falls through a parser error. Checkable with one command, line count in against line count
  out, in *every* run. A deviation is a failure, not a hint.
- **E2 — decision share, with a named exception list.** How many treated obligations end in
  *passed* or *refuted* rather than *undecided*. **Named, not as a percentage** — a percentage
  lets the exception list grow silently with every obligation that turns out to be hard. An
  obligation joins the list only for a structural reason; "the solver does not get through" is
  *undecided*, not an exception.
- **E3 — channel fidelity.** A specification that says something no Gabbro program can assert is
  a failure, not a finding.

### 4.2 The metric this gives back

**[PROPOSED]** *Obligations discharged by the generator against obligations handed to the person*,
per program. It is prover-independent — which is exactly the flaw that killed the earlier
proof-to-code figure — it needs no prover run, and it measures the project's actual promise. It
belongs on the front page beside the template count.

**[OPEN]** A second number belongs beside it: of the generated obligation files, how many carry
the composition the generator promises and how many state it without delivering it yet.

### 4.3 G2 — the solver question

The measurement splits the sayable obligations into those in quantifier-free shape and those
needing quantifiers, folds or reachability, and presents a choice between an SMT solver in the
trust base and weaker automation.

**[PROPOSED]** That is a false alternative. "No SMT" was a decision about the *trust base*, not
about automation. A solver running as an untrusted oracle, emitting a proof certificate that Lean
rechecks, violates nothing — it is §2 a third time. The quantifier-free share is exactly the
ground where certificate reconstruction works well; the rest is the ground where a solver would
have been unreliable anyway, so the "weaker automation" horn hurts far less than the split
suggests. The reconstruction work is one-time, hence a template in this project's own sense.

## 5. CaprockOS — scope

**[DECIDED]** Everything is formally verified except the user's own programs and the Linux
hardware drivers. Not only the microkernel: shell, file system, network stack, firewall and the
rest are written in Gabbro and verified.

**[DECIDED]** No adopted third-party userland. A system whose central claim is that verified
components are cheap to write cannot stand on a large body of unverified code.

**[DECIDED]** Until the base components exist, only what can run on them runs. No interim
product.

**[PROPOSED]** Build order, chosen to serve the product and to produce comparable numbers:
network stack, then the component and process manager, then the firewall, then the file system,
and the shell last.

### 5.1 The component set is also the measurement

**[PROPOSED]** Each component on that list has a published counterpart verified with conventional
tools, each with a known proof cost, each individually a doctorate-sized effort. That makes them
benchmarks. A component reaching the same guarantees at a fraction of the proof burden gives the
proof-to-code figure a measured value against named prior work, rather than an estimate from a
formula.

**[OPEN]** What runs tenant workloads between now and the point where that set exists. The honest
answers are a narrower first product or a longer wait; it should be a decision rather than
something the schedule discovers later.

## 6. Drivers

**[DECIDED]** No compatibility layer and no runtime. Compiled Linux driver binaries are rewritten
by a separate tool — the Modifier — so that they run under Caprock's discipline.

**[DECIDED]** The Modifier is GPLv2 and stays a separate program, invoked as a tool, never linked
into the kernel.

**[PROPOSED]** The Modifier is a second compiler, and it is currently trusted. Everything the
verified kernel claims about isolation rests on the rewriting being correct — on a level without
types, without source and without the invariants that catch a mistake everywhere else. It should
emit a certificate per driver that a small independent checker rechecks, and the kernel's
isolation theorem should carry that certificate as a named premise. Then §2's one-way property
holds here too.

**[DECIDED]** The boundary must be a real boundary: a rewritten driver runs in its own isolation
domain and communicates over a defined interface, not by direct calls into kernel internals. This
is both what the contract wants and what keeps the licence question from arising.

**[OPEN]** No driver mirror yet. One is planned; see §9.

## 7. Namespaces and the file system

**[DECIDED]** No single root tree. One tree per user, plus one each for drivers, programs and the
kernel.

The property this buys is structural rather than checked: **there is no path by which a user's
tree can even name the kernel tree**, so the whole traversal-to-root class of defect does not
exist rather than being guarded against. It is the same move as a grammar that refuses a
construct.

**[OPEN]** Who assembles a process's namespace, and out of what. A namespace granted at process
creation and immutable afterwards is the provable case; run-time mounting enlarges the proof
surface considerably.

**[PROPOSED]** Crossings between trees happen by handle, never by a name that resolves across
trees. A path that can land in another tree reintroduces the global namespace through the back
door.

**[PROPOSED]** On cost: the tree separation is a short invariant and cheap to prove. What costs
in a verified file system is crash consistency — what holds after power loss mid-operation, over
a block device that may reorder writes. That is where the published verified file systems spent
their proof budget, and a schedule that plans for access control and forgets crash semantics is
not slightly wrong.

## 8. Keys, signing and updates

**[DECIDED]** The kernel tree is writable only with a cryptographic key plus a password. Keys are
unique per installation. A key changes only on reinstallation of the microkernel. The private key
is never stored on the device; only public keys live there.

**[DECIDED]** Kernel updates come only from the CaprockOS mirrors. The general signing key is
never on a mirror: an image is signed offline, from secure storage, and uploaded afterwards.

**[DECIDED]** The property being bought: no process can change the kernel without user input.

Offline signing is the strongest single measure in this design. It leaves a mirror compromise
able to withhold, and unable to forge. What it does not cover:

**[PROPOSED]** *Freshness.* A compromised mirror can still serve an old, validly signed image
with a known hole. Signed metadata with an expiry, or a monotonic counter the installation
carries, closes it. **Rare updates make this worse, not better**: where updates are frequent,
silence is suspicious; where they are rare, silence is the normal state and withholding is
invisible.

**[PROPOSED]** *What is signed.* An offline key protects against someone signing without you. It
does not protect against you signing the wrong thing: a compromised build pipeline gets its
malware signed correctly. Reproducible builds are the complement — anyone can rebuild the image
from published source and get the same bytes, so a signature becomes "recheck it" rather than
"trust me".

**[PROPOSED]** *A transparency log*, as the remaining insurance. With an offline key it no longer
protects against forged signatures; it protects against **targeted delivery** — the stale image
sent to exactly one victim — and against the case where the offline key is stolen after all. An
attacker with the key can still sign, but can no longer sign *secretly*.

**[PROPOSED]** *Key rotation is circular as specified.* If the key changes only through an update
and updates are signed with that key, replacing a compromised key requires the compromised key. A
two-tier hierarchy fixes it: an offline root key used rarely and only to certify signing keys, and
an online signing key for everything else. Rotation, revocation, thresholds, rollback protection
and roles are already specified by The Update Framework; adopting its role model is cheaper than
rediscovering it.

**[PROPOSED]** *Two update models, deliberately different.* User input per kernel change is right
for a workstation and impossible for a fleet — nobody touches a token on a thousand nodes. For
fleets the answer is immutable images: a node is redeployed rather than patched, the kernel is
read-only at run time, and the authority sits in the deployment pipeline. Both models use the same
mirror and the same freshness rules.

**[PROPOSED]** *Write the signing procedure down now.* An offline key is used rarely, by a human,
and most urgently exactly when something is on fire. That is when "just this once, on the laptop"
happens. Which machine, which checks before signing, who witnesses it — the cheapest piece of
security here and the first one lost under pressure.

## 9. Licensing

**[DECIDED]**

| Component | Licence |
|---|---|
| Gabbro — compiler, checker, Lean semantics | AGPL-3.0 with the existing additional permission (generated C and binaries are not derived works) |
| Caprock kernel and every self-written OS component | AGPL-3.0 |
| The Modifier | GPLv2 |
| Mirror service software | AGPL-3.0 |
| Interface definitions, the driver contract | permissive — implementing against an interface must not infect the implementer |
| Documentation | CC-BY-4.0 |

**[DECIDED]** The kernel's interface exception exists: services obtained by ordinary system calls
do not make the calling program a derived work.

**[DECIDED]** A driver mirror is planned. It will distribute under GPLv2 with the complete
corresponding source, the change notices, retained copyright notices and attribution. The
corresponding source includes the Modifier and its invocation, because that is how the shipped
binary is reproduced — which is a second reason it is GPLv2 and ships with the mirror. Attribution
alone satisfies none of those clauses; it is worth doing for a different reason, which is that a
mirror rewriting Linux driver binaries will be examined by people who care.

**[DECIDED]** No modified driver binary is distributed today — rewriting happens on the operator's
machine — so no distribution obligation has arisen yet.

**[OPEN]** Whether a shipped image containing kernel and rewritten drivers would be a combined
work. AGPL-3.0 and GPLv2-without-upgrade-clause are not compatible as one work. Separate
distribution avoids the question. This is a legal question, not a technical one, and it is a
further reason for §6's real boundary: a boundary that is technically sharp is easier to defend
in licensing too.

**[OPEN]** Anything an application links — a libc, the component API, an SDK — needs a linking
exception of its own, or every application on the system becomes a derivative work.

**[PROPOSED]** SPDX identifiers per file and a `LICENSES/` directory. A project spanning four
licences is auditable only if it says per file which one applies.

**[OPEN]** The contribution arrangement. A sign-off keeps friction low and freezes the licence; a
contributor agreement keeps relicensing possible and deters some contributors. There is no neutral
choice — only choosing now, cheaply, or later, expensively. It is the decision whose cost rises
fastest, because after outside commits it needs everyone's agreement.

## 10. Release model

**[DECIDED]** The kernel is not a rolling release: rare, signed, key-gated. Everything above it —
desktop, firewall, drivers, services — is rolling.

**[DECIDED]** Caprock hot-reloads processes and drivers, so updates in the rolling layer need no
reboot. This is the microkernel payoff: in a monolithic kernel the driver and the network stack
are *in* the kernel, which is why live patching there is fiddly and still does not cover data
structure changes.

**[DECIDED]** Minor versions stay interoperable: old and new components work together across the
supported window.

**[PROPOSED]** That rule must be mechanically checked, not intended. The protocol and the state
schema are a declared, versioned artefact, and a guardian falls when a minor version bump changes
them incompatibly — otherwise "minor" becomes whatever someone called minor.

**[PROPOSED]** The reload authority belongs in the frozen kernel. A hot reload is, by
construction, an authorised code-injection path — no worse than an update or a reboot, but checked
by a component that is itself already running. If that component is part of the rolling layer, it
can be replaced by whoever can replace components, and the authority is circular. In the kernel it
is verified and not hot-swappable.

**[PROPOSED]** Proof time is now on the critical path of every release. Rolling means a continuous
stream of versions, each needing its proofs; the wall-clock time of the proof check *is* the
release cadence. The consequence is a design constraint: proofs must be per component,
incremental and cacheable, not one large run over everything. The figure to steer by is
**proof-check wall clock per component**, measured from the first component rather than when it
starts to hurt.

**[PROPOSED]** A second figure: **proof survival under semantically irrelevant code change.** The
specification stays when the code changes — that is the point of the generator — but the *proof*
of a handed-over obligation is a term built against a goal whose shape came from the body. How
much of it survives depends on how far the handed-over goal is normalised away from the body, and
that is a lever this project controls. Take a program with a discharged obligation, reorder
independent assignments, rename a local, and see whether the proof still closes. If the rate is
high, the rolling-release argument carries; if it is low, proof maintenance is the release
bottleneck after all, and it is better to know that at the first component than at the third.

## 11. Hot reload across versions

**[DECIDED]** Each version being verified is not the same as the running system being verified.
With hot reload the system is a *sequence* of configurations, and two statements are needed:

1. each version is correct on its own, and
2. every reachable transition between versions preserves the invariants.

The second does not follow from the first. Without it, "all components verified" holds of every
snapshot and says nothing about the system during an upgrade — the same shape as an update path
that is never exercised.

### 11.1 The chosen approach

**[DECIDED]** **An abstract specification that both versions refine.**

Rather than proving a transition per version pair, each version is proved to refine one common
abstract specification of the component. Every state reachable in the old version is then
meaningful in the new one, and the sequence of configurations is provable as a whole rather than
snapshot by snapshot.

This is the project's own amortisation argument, one level up:

> A template falls once, not once per program.
> **An abstraction falls once, not once per version pair.**

The cost sits at the front — writing the abstract specification of each component and proving the
first version against it — and after that version pairs are free. For a rolling release, which
produces version pairs indefinitely, that is the arithmetic that works out. It is also what keeps
the proof effort from growing with the release cadence, which §10 identifies as the thing that
would otherwise strangle it.

**[OPEN]** What the abstract specification of each component looks like. It has to be abstract
enough that plausible future implementations still refine it, and concrete enough that refinement
says something worth having. That balance is the real work, and it is per component.

### 11.2 The supporting techniques, per component class

**[PROPOSED]** Refinement is the frame; these are how a swap is carried out underneath it.

| Component class | Technique |
|---|---|
| stateless, or complete per request | swap directly; nothing to carry |
| stable representation (file system, firewall rule table) | a version-tolerant state format both versions read; migration is a no-op |
| rich internal state (network stack with live connections) | quiesce to a defined state, then a migration function `m` with the obligation `I_old(s) → I_new(m(s))` |
| owns hardware (drivers) | quiesce, always — there is no second owner of a device |

Running both versions side by side, with new work routed to the new instance while the old drains,
avoids a handover instant entirely and works wherever the resource can be partitioned.

**[PROPOSED]** A transactional swap with rollback is the safety net rather than a fifth technique:
a verified snapshot, attempt, and return to the snapshot if the new version's precondition does not
hold. The invariant is never violated, because either the swap succeeds or it did not happen.

**[PROPOSED]** GabbroV should generate the migration obligation per version pair, the same way it
generates logic obligations per program. Verified hot code swap at component level does not appear
to exist anywhere; here it falls out of machinery that exists for another reason.

### 11.3 Where the claim stops

**[DECIDED]** The honest form of the claim is: **no reboot for the rolling layer — which is
almost every change — with the state provably described throughout.**

Two limits no technique removes, and they are better stated than discovered by a reviewer:

- **The kernel.** A defect there is not fixed by reloading components, and the kernel is by
  construction the one thing that is not swapped. This is an argument for keeping it small: the
  smaller it is, the rarer the one change that forces a restart.
- **The hardware.** Microcode, firmware and side-channel mitigations arrive through a restart
  regardless.

"Never a reboot" is neither achievable nor defensible, and claiming it invites the one
counterexample that damages everything else in this document.

## 12. What is deliberately out of scope

**[DECIDED]**

- **Functional correctness** of a program is the programmer's, not the language's.
- **The Linux drivers themselves** are not verified. What is checked is that a driver keeps its
  boundary, not that it drives its device correctly.
- **The Modifier is not proved**, and neither is the compiler. Both emit certificates; the
  certificates are checked. That is the mechanism, not a gap in it.
- **Timing channels.** On hardware with shared execution units, non-interference cannot be
  established in software; the group furthest along on the problem states that complete time
  protection is not possible on present hardware. The contract says what it claims about
  functional interference and names timing channels as an assumption about the hardware
  configuration.
- **What a DMA-capable device does on the bus** is carried by the IOMMU and stands in the
  assumption list as such.
- **A verified libc** is not on the critical path. The isolation the platform sells comes from the
  kernel boundary, and a libc sits nowhere on it.
- **Generated and self-modifying code in user programs.** A JIT, a trampoline, a patched
  instruction sequence: none of it is analysed, and none of it needs to be. **The isolation
  guarantee is enforced, not analysed** — it rests on the kernel and the hardware, not on anyone
  having inspected a program's code. Code that a program writes for itself runs in the same domain
  with the same authority, and is therefore exactly as harmless as any other code that program
  runs. This is not a concession; it is the property that makes the whole line possible. *A system
  whose guarantees depended on analysing user programs could not draw the boundary at "verified
  except the user's programs" at all.*

**Where that line reaches, and where it stops.** Two places sit just inside it and are easy to
lose sight of precisely because the rule above is so clean:

- **The grant of execute permission.** Somewhere a page becomes executable, and that operation
  belongs to the kernel, so it is in scope. The obligation there is not about the generated code
  but about the grant being domain-faithful: a page made executable for one domain is never
  reachable from another. That is an ordinary footprint and label obligation inside the existing
  frame — a new instance, not a new class, and one that is easy to forget for exactly that reason.
- **The Modifier is not covered by this.** It generates code that runs with *driver* authority
  inside the verified perimeter, not inside a user domain. "Generated code is the user's logic"
  covers every JIT and covers exactly one code generator not at all: our own (§6).

**[OPEN]** Who ships the runtime that tenant workloads run on, and with whose authority it runs.
If a tenant brings it and it executes in that tenant's domain, the rule above settles the matter.
If the platform ships it and several tenants share one instance, its sandbox becomes a platform
guarantee — and that is the hardest component on any list, because it is the class at which
multi-tenant platforms actually break. This is a product decision, not a technical fact, and it
decides whether the verification perimeter ends at the kernel boundary or begins again one level
up.

## 13. The open decisions, gathered

| | Where | Cost of deciding late |
|---|---|---|
| The contribution arrangement | §9 | rises fastest — after outside commits it needs everyone's agreement |
| Namespace assembly: fixed at creation or mutable | §7 | the proof surface of the file system |
| What runs tenant workloads before the component set exists | §5.1 | the product date, discovered rather than chosen |
| The abstract specification per component | §11.1 | the whole hot-reload argument rests on it |
| Combined-work question for a shipped image | §9 | a legal answer needed before anyone else operates the system |
| Whether the header audit finds Linux-derived code in AGPL parts | §6 | quiet until it is loud |
| Who ships the tenant runtime, and with whose authority it runs | §12 | decides where the verification perimeter ends |
