# Future low-level syntax and proof boundary

Status: design 2026-10-31; ORDERED FOR COMPLETE IMPLEMENTATION by the owner on 2026-11-03 (recommendations of
"Rule changes and owner decisions" approved; the `Spec.lean` diff of decision 2 goes to the owner before merge).
The confirmed owner decisions O12–O17 of [PLAN-COMPILER-READY.md](PLAN-COMPILER-READY.md) §8 (2026-11-12)
replace source ASM with contracted target-binding calls and generated entry/exit code; no assembly text is allowed.
The syntax below is still not accepted until its canonical Lean rules exist. Boot, privileged operations,
raw-address access and device-register reads, writes, fallible reads and register transitions are in scope
(owner, 2026-11-03; AGENTS.md). Normal RAM authority below never authorizes MMIO, ports, DMA or device-register
operations; device memory has its own class and rules (PLAN-COMPILER-READY §3, L2, after A2 lifts `RegLokal`).
The implementation targets are the Lean model, parser/exporter and checker, never Stage 0 or the runner.
Keep the existing assembly IR runner. Do not restore a source
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
  weak-memory reading assumptions. It currently includes software foreign/entry behavior in the foreign
  oracle boundary. The proposed separation below is a real change of premises, not today's theorem.
- [Address layout](../grammatik/Grammatik/Speichermodell/Adressen/Layout.lean) and
  [extent preservation](../grammatik/Grammatik/Speichermodell/Adressen/Bereich.lean): `Adresse` is
  `Nat × Nat`; `LayoutOk` separates carriers; OPEN tables occupy separate abstract spaces.
  G's carrier/index memory and arbitrary natural-byte layouts are not a finite physical-address,
  translation-table, alias-coherence or revocation model. `ImBereichO` constrains foreign writes;
  it is not a proof that a low-level load has authority.
- [Provider model](../grammatik/Grammatik/Hardware/Anbieter/Region.lean): `PStep` requires fresh,
  disjoint reservations and aligned commits, with lifetime/release events. Its header calls the
  provider promise a named hardware assumption and also calls kernel correctness user logic.
  Future integration follows O14: a provider inside the verified image proves its contract; one outside it
  has a declared environment contract, separate from hardware.
- [Profiles](../grammatik/Grammatik/Kern/Syntax/Profil.lean): keyed architecture/memory modes and
  library requirements exist. `erfuellt` maps free entries to `True`; a free prose profile entry
  cannot certify a binding operation, a bootloader, or a mapping invariant.
- [Surface reference](SYNTAX.md), sections 1, 7, 12 and 14, and
  [memory rules](LANGUAGE.md), section 5: existing `arch`, `requires`, `ensures`, `effects`,
  `costs`, `in/out/clobbers`, `entry`, `boot`, `entrust`, phase marks and region extents are reused.
  The Rust front end was deleted on 2026-11-10 (AGENTS.md §3); the Lean parser/exporter and checker are
  the front-end targets, and the existing `asmT` string form must be refused and then removed (L10).

Exact missing connections for this proposal are: contracted binding operations with GIR cells as their
meaning and target-table rows as their bytes; an architectural entry/exit state and privilege transition
relation in G's bridge; authority provenance, finite address arithmetic and physical alias accounting; a mapping/lifetime
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
2. A separate boot language with its own memory and concurrency rules isolates early work, but
   duplicates semantics, ownership and contracts and makes the safe handoff a second compiler boundary.
   Reject a parallel language/runtime; neutral architectural state belongs in the canonical model.
3. Extend existing callable contracts with checked architectural contexts and linear authority. A target-binding
   function denotes a GIR cell, boot composes calls, raw access creates an ordinary bounded view under existing
   ownership. Choose this approach: a small interface with a substantial shared proof implementation.

The interface has three concepts: an address value, a linear context carrying authority, and a bounded
region view. Calls and existing read/write effects carry the operations. Privileged operations are calls of
target-binding functions with contracts over linear `context<P>`; no binding has an instruction-text body or
per-body certificate. Its GIR cell is neutral; its bytes are a row of the target table (PLAN-COMPILER-READY §4.1).
Entry and exit code is generated from `entry` declarations, with one generic theorem per frame kind.
The `asmT` string form and `prim fn … = asm { … }` are refused first and removed with L10. Architecture and
ABI details belong to checked target bindings. No implicit host OS, ELF, libc or reset protocol is required.

## Candidate syntax (not current grammar)

Keep existing declaration shapes. The following extensions are explicitly proposed tokens/types, with
final spelling subject to the canonical Lean grammar review: `address<S>`, `context<P>`, `region<C,R>`,
`ram_view`, and an explicit `entry` contract. `S` names an address space, `P` a
checked architecture/ABI state profile, `C` a memory class, and `R` access rights. Names in predicates
below denote library specifications to be defined in Lean, not magic built-in truths.

```gabbro
// Proposed address values have width fixed by the selected architecture.
const SCRATCH : address<physical> = 0x1000;

// Proposed generic operation: success borrows authority, never manufactures it.
raw fn ram_view(c: context<P>, a: address<physical>, n: u64)
    -> region<normal,rw>
    requires owns_ram(c, a, n) && mapped(c, a, n) && nonwrapping(a, n)
    ensures view_of(result, c, a, n)
    effects { reads c };

// Target-binding contract; the meaning is a GIR cell, the bytes a target-table row.
prim fn install_root(c: context<P>, root: address<physical>)
    -> context<P>
    requires valid_root(c, root)
    ensures installed(result, root)
    effects { consumes c };

// Existing boot shape; each step must now carry a checked state transition.
boot firmware_entry arch x86_64 {
    step establish_boot_context();
    step initialize_ram();
    step establish_user_context();
    dispatch userspace_main;
}
```

The binding contract is schematic, not an implemented operation: its GIR cell must cover the translation
regime, required barriers/TLB maintenance and all architecturally allowed outcomes. `TargetOk` checks the
target row's shape, M measures it on silicon (privileged rows on a bare-metal image, K2), and `Hardware T`
is the named assumption that each row computes its cell. No per-body certificate or instruction string exists.
`costs` is omitted here because no numeric bound has been proved; absence must never create a finite bound.

`ram_view` is one generic elaboration primitive, not an unverified foreign implementation of memory safety.
Its returned region is a scoped borrow tied to `c`, with its original ownership identity and declared extent.
The `context` is linearly owned; `reads c` borrows it for this view's lifetime. A consuming context call such
as `install_root` is forbidden while views or derived references remain live. A privilege return or `never`
call consumes the context through its contract. Internally split contexts may hold disjoint RAM authorities;
only checked split/merge of the existing resource discipline may create such partitions. Phase marks still
express ordered software stages; possessing a mark alone never grants RAM or CPU privilege.

An existing entry declaration supplies the contract from which entry/exit code is generated, covered by
one generic theorem per frame kind (L5). Its `regs in`, `regs out`, `preserves`, `clobbers`, `stack`, nesting
and `dispatch` retain their roles. An entry contract describes the pre-stack architectural state, not merely a normal function ABI.
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
explicit initial machine-state specification and proved acquisition, never a `context` literal or an address
number. At firmware entry the initial state is the declared `FirmwareHandoff` environment contract (§4.4 of
PLAN-COMPILER-READY). A software allocator must prove partition/freshness; CPU privilege alone cannot establish it.
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

Binding operations denote GIR cells over the neutral architectural state (L4), with contracts over the linear
context. Their generic connection to G/GX must preserve intermediate observable steps, faults and interleavings,
not just matching input/output values; entry and exit frames have one generic theorem per frame kind (L5).
Software loops need invariants; finite budgets/costs require bounds. Non-returning transitions have no invented
return state. A hardware fault is only a named hardware outcome if the model specifies it; malformed software cannot silently turn
into an allowed `hardware` stop or satisfy `ensures` vacuously.

Acceptance checks the signature, resource/effect accounting, context flow, modelled binding operation,
entry contract and checked profile. Reject privilege mismatches, unmodelled operations, unspecified architectural
behavior and unsupported targets by name; the full compiler's generic GIR/target-table route establishes
final-byte correspondence, without refinement or per-compilation translation validation (MACHINE-IR-PLAN §8).
Architectural nondeterminism must be covered universally, never resolved to an observed result. No fallback
to opaque instruction strings, implicit `unsafe` acceptance or signature-only GREEN is permitted. Existing runner
support alone does not imply source acceptance; do not extend the runner in this planning task.

## Obligations and precise trust boundary

Every binding contract, generated entry/exit frame and boot software body must account for:

- Entry and exit: all reachable entries, register/flag/vector state, privilege level, translation regime,
  interrupt masks, stack availability/alignment/extent, exception frames, return address and return mode.
  Bootstrap before a stack exists has a separate pre-stack state in the same transition relation.
- Frame and memory: complete reads and writes including hidden stack traffic; carrier extents, permissions,
  physical aliases, initialization and lifetimes; preservation of everything not declared. A clobber declaration
  is not permission to overwrite arbitrary memory. Register clobbers must include
  condition codes and implicit architectural operands where relevant; ABI-preserved state must be restored.
- Control and logic: `requires`/`ensures`, all error/fault exits, named destinations, call logs, locks,
  ownership and invariants at their required places. An external symbol without a proved contract is refused;
  assembly text is refused and removed. A source `ensures` assertion alone is not a correctness proof.
- Concurrency and time: accesses in the trace, GX/W atomic ordering and release/acquire correspondence,
  no shared atomic hidden from the rely, interrupt nesting/masking and core locality, no deadlock introduced
  by privilege transitions. A binding call is not implicitly atomic. Interrupt masking is not a multicore lock.
  Preserve the existing meaning of finite own-step costs; hardware latency needs separately named CPU
  assumptions and must not assert a boot wait is bounded without software and hardware evidence.

The trusted logical base remains Lean's kernel and exactly `propext`, `Classical.choice`, `Quot.sound` for
the goal theorem. The compiler's lowering and every pass are proved generically; target-table shape is checked
by `TargetOk`, and M is evidence for the named assumption `Hardware T` that every row computes its GIR cell
(MACHINE-IR-PLAN §8–§9). There is no assembler or per-body certificate in this design.
CPU/MMU/interrupt/memory behavior may be named hardware assumptions with precise domains.
Software inside the verified image, including boot, allocators and ABI setup, is user logic. Software outside
the image, including firmware before entry and an operating system below a hosted program, is a named environment
assumption with a declared contract, listed per unit (PLAN-COMPILER-READY §4.4, O14). Both software classes require
the caller to prove `pre` at every call; software inside the image proves `pre → post`, while environment software
has `pre → post` named in premise (c) (A1). Hardware retains its separate, unconditional contract.
Probes and CPU differential tests provide evidence for hardware assumptions; they never discharge software logic.
A separate diagnostic mode may display unresolved software obligations but cannot certify the binary.

## Boot handoff to safe userspace

The first boundary is firmware entry in 64-bit mode on x86-64 (UEFI), with paging already on and
`FirmwareHandoff` stating mode, mappings, stack, the truth of the memory map and reserved memory
(PLAN-COMPILER-READY §4.2, O13). The image is firmware-loadable; the kernel takes over the memory map and leaves
boot services. Further x86-64 cores use the binding's generated start item made of mode-transition table rows,
with one proved contract for arrival in 64-bit mode with the declared stack and context (K4, O17); no assembly text.
Reset in 16-bit mode or a 32-bit loader protocol is outside the first gate.
Prove that boot's Gabbro calls and generated entry code establish stack, mappings, initialized data/zero storage,
region ledger, lock/invariant state and declared root arguments. Reserve image, stacks, page tables and live boot
storage before splitting the userspace RAM authority; account for other cores and external agents.
Boot then transfers bounded regions and permitted capabilities to the declared userspace root and consumes
or retains the remaining privileged context according to the contract. Userspace receives no ambient
physical-memory authority. Boot-space retirement proves absence of references/mappings across all cores,
not just consumption of a ghost mark. Re-entry and interrupts must preserve that handoff invariant.

Derive the applicable `Laufzeit.lader/start/einmal`, `StartGut`, `GutO`, `AxVertragO` and `ImBereichO`
software facts from this proof and the connected execution simulation. Do not claim that proving the root's
precondition verifies the loader. If a prior loader is outside the image, state its entry-state requirement
as a named environment contract explicitly; software before that boundary is outside the verified image.

## Rule changes and owner decisions

The approved region-producer design is the following rule, to be connected through the canonical model
before acceptance:

> Safe memory access always requires a live region/reference. External software returns regions under its declared contract.
> Low-level code may select a normal-RAM span by an explicit address only through checked authority,
> producing a bounded region view. A number alone never grants memory or code authority.

This is a new controlled producer of regions, not removal of `M140`'s ban on ordinary integer-to-pointer
casts. `ptr`/reference access, freshness, race freedom and extent checks retain their force. Update AGENTS.md,
LANGUAGE.md section 5.5 and the canonical typing rules together when implementing; this document does not
change those standing rules now. Device memory must be rejected by `ram_view`, even with a privileged context.

The recommendations were approved on 2026-11-03, with the requirement to show the `Spec.lean` diff of decision 2 before merge;
the confirmed O12–O17 of PLAN-COMPILER-READY §8 replace decision 3 and the source-ASM design (2026-11-12):

1. Approve address/context/view types and the revised region-producer rule above. Recommendation: scoped
   borrows first, explicit ownership transfer through proved provider contracts; no unrestricted casts.
2. Split `Spec.lean`'s software foreign assumptions into user obligations for software inside the image and
   declared environment contracts for software outside it, with hardware assumptions separately named (A1, O14).
   Derive applicable software `GutO`/`AxVertragO`/`ImBereichO` facts and runtime initialization from proofs;
   extend `NutzerPflicht`/the bridge with their discharge. Show the `Spec.lean` diff to the owner before merge.
   Preserve current theorem users by proving the old-domain corollary, not retaining a second execution path.
3. The first boot boundary is firmware entry in 64-bit mode, on x86-64 first, under `FirmwareHandoff`
   (PLAN-COMPILER-READY §4.2, O13); AArch64 is the second binding running the same kernel sources (K6, O16).
   Further x86-64 cores use the generated binding start item (K4, O17). Other entry modes refuse until modelled.
4. Approve the goal's additional coverage: authority/lifetime/privilege preservation and raw-access traces,
   and the `speicherAdressen` extension relating finite mapped physical bytes to existing carriers. Retain
   existing contract/race/deadlock/budget claims and NOT CLAIMED items; add no general termination, fairness,
   guest correctness or hardware-time promise. Review required changes to `KernPlan` and weak-memory reading
   assumptions where masking, mappings or binding calls expose intermediate architectural steps.

## Future implementation and validation order

1. Freeze the baseline with the userspace integration owner. Inventory actual region and body support then;
   apply the confirmed decisions above with an explicit proposed `Spec.lean` diff. No current lane depends on this work.
2. Canonical Lean grammar/model first: extend source nodes, address/context typing, state/effect semantics,
   normal-RAM authority and boot transition relations. Append constructors where required. Prove generic
   preservation and non-degenerate joint witnesses, including actual writes and privilege handoff. Check the
   goal theorem's exact standard axioms and preserve its old-domain consequence. No front-end-first acceptance.
3. Prove the generic binding-operation and generated-frame connection to G/GX, and the ownership/alias/interleaving
   bridge (L4/L5). Operations mean GIR cells, bytes are target-table rows, and final-byte correspondence follows
   MACHINE-IR-PLAN's generic theorems; there is no source body, per-body certificate or translation validation.
4. Implement parser/exporter/checker, proof obligations and lowering only after their canonical rules exist.
   Update source references and replace assumption-only software acceptance without aliases or silent migration.
   Existing safe userspace forms keep their semantics. Existing `asmT` strings, `prim fn … = asm { … }` and
   software `assume` on `entrust` become explicit refusals and are then removed (L10).
5. Validate positive cases (RAM write/read, context transition, boot-to-root handoff, interrupt entry/return)
   and negative cases (forged authority, wraparound, stale epoch, physical alias, bad stack, undeclared clobber,
   missing barrier, hidden shared write, wrong privilege and MMIO view). This work changes neither Stage 0 nor
   the runner. Future canonical builds use
   the global lock and memory scopes; run full model/axiom/layout and applicable compiler guardians then.

Totality claims must name a domain: parsing/refusal is total over source input; certified lowering covers
only the explicitly modelled architecture, ABI, instructions, contexts and region operations. Unsupported
forms refuse; they are not silently erased. Record both accepted and refused forms and connect generic
correctness through the actual pipeline before claiming any new low-level case complete. This design itself
changes no compiler coverage and authorizes no grammar rebuild, code implementation or push.
