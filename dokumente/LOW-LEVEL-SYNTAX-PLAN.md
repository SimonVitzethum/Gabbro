# Future low-level syntax and proof boundary

Status: design only, 2026-10-31. This document proposes a future canonical language/model change;
none of its new syntax is accepted or implemented by this task. Source ASM, boot, privileged
instructions and raw-address access are outside the current userspace Gabbro-to-IR assignment.
Device-register forms remain excluded; normal RAM authority below never authorizes MMIO, ports,
DMA or device-register operations. Keep the existing assembly IR runner. Do not restore a source
interpreter, create a second runner or modify seL4 for this design.

## Evidence and present gaps

Read against this checkout's AGENTS.md and CLAUDE.md, and these definitions:

- [Canonical source parser](../grammatik/Grammatik/Parser/Item/ElementTief.lean):
  `SItemTief.asmT` stores a signature and a string; `bootT` stores steps and a dispatch path;
  `trustT` stores a named destination, registers, stack and assumption. `SEingang` has register
  maps, preservation/clobbers, stack, nesting and dispatch. These represent syntax, not an
  instruction-semantics proof of the stored string.
- [Core syntax](../grammatik/Grammatik/Kern/Syntax/Syntax.lean): foreign bodies use `D.Ax`,
  `aparams`, `aerg`, `aschreibt` and `Stmt.axiomCall`. Linear marks and interrupt declarations
  already provide resources and handler identity; they do not establish CPU privilege or mappings.
- [Spec](../grammatik/Grammatik/Zielsatz/Kern/Spec.lean), especially its ONE ASSUMPTION LIST:
  `GutO`, `AxVertragO`, `ImBereichO`, `Laufzeit.lader/start/einmal`, `KernPlan` and the five
  weak-memory reading assumptions. It currently includes software ASM/entry behavior in the foreign
  oracle boundary. The proposed separation below is a real change of premises, not today's theorem.
- [Address layout](../grammatik/Grammatik/Speichermodell/Adressen/Layout.lean) and
  [extent preservation](../grammatik/Grammatik/Speichermodell/Adressen/Bereich.lean): `Adresse` is
  `Nat × Nat`; `LayoutOk` separates carriers; OPEN tables occupy separate abstract spaces.
  G's carrier/index memory and arbitrary natural-byte layouts are not a finite physical-address,
  translation-table, alias-coherence or revocation model. `ImBereichO` constrains foreign writes;
  it is not a proof that an ASM load has authority.
- [Provider model](../grammatik/Grammatik/Hardware/Anbieter/Region.lean): `PStep` requires fresh,
  disjoint reservations and aligned commits, with lifetime/release events. Its header calls the
  provider promise a named hardware assumption and also calls kernel correctness user logic.
  Future integration must resolve that classification: a software provider must prove its contract.
- [Profiles](../grammatik/Grammatik/Kern/Syntax/Profil.lean): keyed architecture/memory modes and
  library requirements exist. `erfuellt` maps free entries to `True`; a free prose profile entry
  cannot certify ASM, a bootloader, or a mapping invariant.
- [Surface reference](SYNTAX.md), sections 1, 7, 12 and 14, and
  [memory rules](LANGUAGE.md), section 5: existing `arch`, `requires`, `ensures`, `effects`,
  `costs`, `in/out/clobbers`, `entry`, `boot`, `entrust`, phase marks and region extents are reused.
  Rust `AsmRumpf` in `crates/gabbro-syntax/src/ast.rs` explicitly treats instruction strings as
  unread assumptions. Neither that representation nor a constraint string proves machine effects.

Exact missing connections for this proposal are: structured, validated source ASM operands and decoded
bytes tied to its contract; an architectural entry/exit state and privilege transition relation in G's
bridge; authority provenance, finite address arithmetic and physical alias accounting; a mapping/lifetime
relation connecting raw spans to existing carriers; proof-producing boot initialization and root handoff;
and a generic interleaving simulation discharging the software portions of the oracle and runtime premises.
Existing isolated hardware/runner lemmas do not by themselves supply those connections. LANGUAGE.md's
section 5.5 reports byte-region certification gaps; implementation lanes may advance that baseline. Reuse
their actual canonical region model at implementation time rather than introducing a parallel heap model.
No build, completeness measurement or proof audit was performed for this document.

## Alternatives and recommendation

1. An unrestricted integer-to-pointer cast inside an `unsafe` block is compact, but exports alias,
   lifetime, privilege and race obligations to every caller and invalidates the current memory rule.
   Reject it; a block marker cannot prove safety.
2. A separate boot/ASM language with its own memory and concurrency rules isolates early work, but
   duplicates semantics, ownership and contracts and makes the safe handoff a second compiler boundary.
   Reject a parallel language/runtime; architectural instruction semantics remain a necessary layer.
3. Extend existing callable contracts with checked architectural contexts and linear authority. ASM
   supplies a body, boot composes calls, raw access creates an ordinary bounded view under existing
   ownership. Choose this approach: a small interface with a substantial shared proof implementation.

The interface has three concepts: an address value, a linear context carrying authority, and a bounded
region view. Calls and existing read/write effects carry the operations. Privileged instructions stay
inside contracted ASM functions; do not add one source statement per privileged opcode. Architecture and
ABI details belong to checked target bindings. No implicit host OS, ELF, libc or reset protocol is required.

## Candidate syntax (not current grammar)

Keep existing declaration shapes. The following extensions are explicitly proposed tokens/types, with
final spelling subject to the canonical Lean grammar review: `address<S>`, `context<P>`, `region<C,R>`,
`with`, `proof`, `ram_view`, and an explicit `entry` contract tail. `S` names an address space, `P` a
checked architecture/ABI state profile, `C` a memory class, and `R` access rights. Names in predicates
below denote library specifications to be defined in Lean, not magic built-in truths.

```gabbro
// Proposed address values have width fixed by the selected architecture.
const SCRATCH : address<physical> = 0x1000;

// Proposed generic operation: success borrows authority, never manufactures it.
raw fn ram_view(c: context<boot_el1>, a: address<physical>, n: u64)
    -> region<normal,rw>
    requires owns_ram(c, a, n) && mapped(c, a, n) && nonwrapping(a, n)
    ensures view_of(result, c, a, n)
    effects { reads c };

// Existing ASM body shape, proposed context and proof clauses.
prim fn install_root(c: context<boot_el1>, root: address<physical>)
    -> context<boot_el1>
    requires valid_root(c, root)
    ensures installed(result, root)
    effects { consumes c }
    arch aarch64 with el1_abi proof install_root_correct
    = asm {
        "msr ttbr0_el1, $root"
        "isb"
        in { root : "r" }
        clobbers { memory }
    };

// Existing boot shape; each step must now carry a checked state transition.
boot reset arch aarch64 {
    step establish_boot_context();
    step initialize_ram();
    step establish_user_context();
    dispatch userspace_main;
}
```

The ASM sample is deliberately not certified: it is only admissible if `valid_root` and the proof
cover the exact translation regime, required barriers/TLB maintenance, operand substitution and all
architecturally allowed outcomes. It is not a recommended complete MMU setup sequence. `proof` resolves
to a kernel-checked certificate indexed by the elaborated body and profile, not a name accepted on trust.
`costs` is omitted here because no numeric bound has been proved; absence must never create a finite bound.

`ram_view` is one generic elaboration primitive, not an unverified foreign implementation of memory safety.
Its returned region is a scoped borrow tied to `c`, with its original ownership identity and declared extent.
The `context` is linearly owned; `reads c` borrows it for this view's lifetime. A consuming context call such
as `install_root` is forbidden while views or derived references remain live. A privilege return or `never`
call consumes the context through its contract. Internally split contexts may hold disjoint RAM authorities;
only checked split/merge of the existing resource discipline may create such partitions. Phase marks still
express ordered software stages; possessing a mark alone never grants RAM or CPU privilege.

Extend an existing entry declaration with the same `with P proof certificate` contract tail before its
body. Its `regs in`, `regs out`, `preserves`, `clobbers`, `stack`, nesting and `dispatch` retain their
roles. An entry contract describes the pre-stack architectural state, not merely a normal function ABI.
Extend `entrust` through this same contract mechanism, replacing software `assume` with an isolation/handoff
proof. A named code destination remains mandatory: no address-to-function-pointer conversion is proposed.
Unproved guest behavior earns no guest contract, cost or termination guarantee; the proven monitor/isolation
boundary must protect every retained carrier against the guest's permitted behavior and re-entry.

## Canonical typing, semantics and acceptance

An address is inert data with a space and architectural width. Construction from a fitting integer is
allowed; narrowing and arithmetic require explicit non-wrapping bounds or a checked failure channel.
Equality does not imply authority. Serialization loses authority. A physical and a virtual address are
different types. A numeric value cannot be dereferenced, called, freed or promoted to a reference.

A context contains a non-forgeable authority ledger: live spans, space/translation regime, permissions,
memory class, owner, lifetime epoch and current privilege/interrupt state. Authority originates in an
explicit initial machine-state specification and proved acquisition, never a `context` literal or an OS
assumption. A software allocator must prove partition/freshness; CPU privilege alone cannot establish it.
An initial-state premise describes the chosen starting boundary; proving software before that boundary
requires moving the boundary back, not relabeling the software as hardware.

`ram_view` checks the complete half-open span, alignment, normal-memory classification, mapping, permissions,
liveness and initialization requirements. Uninitialized writable bytes must be initialized before typed
reads. Typed views also require representation validity, endianness and layout proofs. Zero-length views
provide no access; one-past values remain non-dereferenceable. Dynamic failure follows an explicit existing
reason/else channel when checks are executable; unproved static ownership or privilege conditions refuse.
Subsequent accesses use ordinary region/reference rules and effects. Two virtual aliases must share the
same physical ownership/carrier identity; unequal address-space numbers never prove physical disjointness.
Remapping, reuse and revocation require quiescence of all affected references and cores, with epoch changes
and proved TLB synchronization. Do not model a finite machine's OPEN region as infinite physical storage.

An ASM body denotes the set of all architectural executions of its decoded bytes under its context and
hardware profile. Its certificate proves a simulation into G/GX, including all intermediate observable
steps, faults and interleavings, not just matching input/output values. Internal loops need invariants;
finite budgets/costs require bounds. Non-returning transitions have no invented return state. A hardware
fault is only a named hardware outcome if the model specifies it; malformed software cannot silently turn
into an allowed `hardware` stop or satisfy `ensures` vacuously.

Acceptance checks the signature, resource/effect accounting, context flow, body/certificate identity,
instruction semantics availability, ABI and final-image validation. Reject unknown instructions, privilege
mismatches, unspecified architectural behavior, missing certificates or unsupported targets by name.
Architectural nondeterminism must be covered universally, never resolved to an observed result. No fallback
to opaque ASM execution, implicit `unsafe` acceptance or signature-only GREEN is permitted. Existing runner
support alone does not imply source acceptance; do not extend the runner in this planning task.

## Obligations and precise trust boundary

Every actual ASM/boot software body owes:

- Entry and exit: all reachable entries, register/flag/vector state, privilege level, translation regime,
  interrupt masks, stack availability/alignment/extent, exception frames, return address and return mode.
  Bootstrap before a stack exists has a separate pre-stack state in the same transition relation.
- Frame and memory: complete reads and writes including hidden stack traffic; carrier extents, permissions,
  physical aliases, initialization and lifetimes; preservation of everything not declared. `clobbers memory`
  is an optimizer constraint, not permission to overwrite arbitrary memory. Register clobbers must include
  condition codes and implicit architectural operands where relevant; ABI-preserved state must be restored.
- Control and logic: `requires`/`ensures`, all error/fault exits, named destinations, call logs, locks,
  ownership and invariants at their required places. An external symbol or handwritten assembly blob is
  software with the same obligations. A source `ensures` assertion is not an ASM correctness proof.
- Concurrency and time: accesses in the trace, GX/W atomic ordering and release/acquire correspondence,
  no shared atomic hidden from the rely, interrupt nesting/masking and core locality, no deadlock introduced
  by privilege transitions. ASM is not implicitly atomic. `cli`-like masking is not a multicore lock.
  Preserve the existing meaning of finite own-step costs; hardware latency needs separately named CPU
  assumptions and must not assert a boot wait is bounded without software and hardware evidence.

The trusted logical base remains Lean's kernel and exactly `propext`, `Classical.choice`, `Quot.sound` for
the goal theorem. Decoders, assemblers, compiler and certificate generators produce untrusted candidates;
the checker must bind certificates to final bytes, operands, relocation, entry addresses and target profile.
CPU instruction/MMU/interrupt/memory behavior may be named hardware assumptions with precise domains.
Firmware, bootloaders, OS services, allocators, ABI setup and ASM algorithms are software user logic.
Probes and CPU differential tests help validate models; they never discharge arbitrary ASM correctness.
A separate diagnostic mode may display unresolved software obligations but cannot certify the binary.

## Boot handoff to safe userspace

Start from an explicit architectural state set: reset or an explicitly delimited prior-loader entry.
Prove that boot's actual instructions establish stack, mappings, initialized data/zero storage, region
ledger, lock/invariant state and declared root arguments. Reserve image, stacks, page tables and live boot
storage before splitting the userspace RAM authority; account for other cores and external agents.
Boot then transfers bounded regions and permitted capabilities to the declared userspace root and consumes
or retains the remaining privileged context according to the contract. Userspace receives no ambient
physical-memory authority. Boot-space retirement proves absence of references/mappings across all cores,
not just consumption of a ghost mark. Re-entry and interrupts must preserve that handoff invariant.

Derive the applicable `Laufzeit.lader/start/einmal`, `StartGut`, `GutO`, `AxVertragO` and `ImBereichO`
software facts from this proof and the connected execution simulation. Do not claim that proving the root's
precondition verifies the loader. If a prior loader is outside the image, state its entry-state requirement
as a software obligation explicitly; whole-boot verification is unavailable until it is discharged.

## Rule changes and owner decisions

Replace the current absolute memory rule with the following proposed rule, only after owner approval:

> Safe memory access always requires a live region/reference. External software returns proved regions.
> Low-level code may select a normal-RAM span by an explicit address only through checked authority,
> producing a bounded region view. A number alone never grants memory or code authority.

This is a new controlled producer of regions, not removal of `M140`'s ban on ordinary integer-to-pointer
casts. `ptr`/reference access, freshness, race freedom and extent checks retain their force. Update AGENTS.md,
LANGUAGE.md section 5.5 and the canonical typing rules together when implementing; this document does not
change those standing rules now. Device memory must be rejected by `ram_view`, even with a privileged context.

The owner must decide these language/goal changes before implementation:

1. Approve address/context/view types and the revised region-producer rule above. Recommendation: scoped
   borrows first, explicit ownership transfer through proved provider contracts; no unrestricted casts.
2. Approve splitting `Spec.lean`'s software foreign assumptions into user obligations with hardware-only
   assumptions separately named. Recommendation: derive software `GutO`/`AxVertragO`/`ImBereichO` instances
   and runtime initialization from certificates; extend `NutzerPflicht`/the bridge with their discharge.
   Preserve current theorem users by proving the old-domain corollary, not retaining a second execution path.
3. Choose the initial boot verification boundary (reset, or specified loader entry) and first architecture/ABI.
   Recommendation: one AArch64 EL1 normal-RAM profile, then a proved transition to userspace; other entry
   modes refuse until modelled. An externally established entry state remains an explicit scope limit.
4. Approve the goal's additional coverage: authority/lifetime/privilege preservation and raw-access traces,
   and the `speicherAdressen` extension relating finite mapped physical bytes to existing carriers. Retain
   existing contract/race/deadlock/budget claims and NOT CLAIMED items; add no general termination, fairness,
   guest correctness or hardware-time promise. Review required changes to `KernPlan` and weak-memory reading
   assumptions where masking, mappings or ASM expose intermediate architectural steps.

## Future implementation and validation order

1. Freeze the baseline with the userspace integration owner. Inventory actual region and body support then;
   resolve the decisions above with an explicit proposed `Spec.lean` diff. No current lane depends on this work.
2. Canonical Lean grammar/model first: extend source nodes, address/context typing, state/effect semantics,
   normal-RAM authority and boot transition relations. Append constructors where required. Prove generic
   preservation and non-degenerate joint witnesses, including actual writes and privilege handoff. Check the
   goal theorem's exact standard axioms and preserve its old-domain consequence. No Rust-first acceptance.
3. Prove the generic instruction-block/ABI/body refinement and ownership/alias/interleaving bridge, including
   final bytes and relocation. Add a small precisely supported instruction domain before any ASM acceptance.
   Certificates are per-body evidence under a generic soundness theorem, not per-program compiler logic.
4. Implement parser/exporter/checker, proof obligations and lowering only after their canonical rules exist.
   Update source references and replace assumption-only software acceptance without aliases or silent migration.
   Existing safe userspace forms keep their semantics. Existing opaque ASM/entrust inputs lacking evidence
   become explicit refusals in certification; no promise of backward acceptance for unsafe foreign bodies.
5. Validate positive cases (RAM write/read, context transition, boot-to-root handoff, interrupt entry/return)
   and negative cases (forged authority, wraparound, stale epoch, physical alias, bad stack, undeclared clobber,
   missing barrier, hidden shared write, wrong privilege, unknown opcode, certificate/byte mismatch, MMIO view).
   Exercise the existing runner only where it supports the exact target/domain. Future canonical builds use
   the global lock and memory scopes; run full model/axiom/layout and applicable compiler guardians then.

Totality claims must name a domain: parsing/refusal is total over source input; certified lowering covers
only the explicitly modelled architecture, ABI, instructions, contexts and region operations. Unsupported
forms refuse; they are not silently erased. Record both accepted and refused forms and connect generic
correctness through the actual pipeline before claiming any new low-level case complete. This design itself
changes no compiler coverage and authorizes no grammar rebuild, code implementation or push.
