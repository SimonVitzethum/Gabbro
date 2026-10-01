# Target portability: OS-independent and freestanding x86-64 architecture

*Lane 540, 2026-10-01. Status: PROPOSED design, not an implementation and
not a proof. Nothing here claims any OS support is implemented, any image
is emitted, or any source-to-final-byte chain is closed. Central progress
record: [DIRECT-COMPILER.md](../../DIRECT-COMPILER.md). Detailed compiler
design: [DIRECT-COMPILER-DESIGN.md](../../DIRECT-COMPILER-DESIGN.md). This
document is the portability companion to both; it adds no definitions, no
checker rules, and no guarantees beyond those stated in the goal theorem.*

*Claim boundary: every section marked PROPOSED needs Lean modelling,
generic proofs, and independent review before any Rust part is built.
Sections marked ACCEPTED describe only checked-in helpers. All
source-to-executed-final-binary closure remains OPEN. The selected
architecture remains x86-64; other instruction sets need separate target
models and are not covered here.*

## 0. Reading guide

- Section 1 states the one-chain principle and the three separated
  concerns (instruction profile, ABI/image/entry profile, environment
  bindings).
- Sections 2–8 specify the profile contents: modes, outputs, stack/ABI,
  call/gate bindings, entries, relocations, and validation closure.
- Section 9 fixes per-profile acceptance gates (witnesses, probes,
  compatibility, Rust tests).
- Section 10 fixes cache keys and fast compilation with mandatory
  validation.
- Section 11 lists practical dependencies: accepted bounded helpers
  versus missing generic proofs.
- Section 12 is the "add an OS" checklist. Section 13 states the
  refusal rule. Section 14 records guarantee and file-ownership
  boundaries.

Canonical vocabulary throughout: `Gabbro.Grammatik.X86` in
`../../grammatik/Grammatik/X86/Typen.lean`. Image and loader contract:
[IMAGE-ABI](IMAGE-ABI.md). Source bridge: [QUELLBRUECKE](QUELLBRUECKE.md).
IR and certificates: [IR-VALIDIERUNG](IR-VALIDIERUNG.md). Optimiser
specification: `../../grammatik/OPTIMIZER.md`. Active plan:
`../PLAN-UEBERSETZUNGSVALIDIERUNG.md` sections 0–5.

## 1. One chain, three separated concerns (PROPOSED)

There is exactly ONE source model, ONE shared typed IR (lane 287,
PENDING per `../../grammatik/OPTIMIZER.md` section 2), ONE target
executor vocabulary, and ONE validation chain (`valX86 E bild = true`
implies per-access refinement via generic `valX86_sound`, per
[QUELLBRUECKE](QUELLBRUECKE.md) section 4). Target variability is DATA
consumed by that chain, never a fork of it. Three concerns are kept
separate by construction:

1. **Hardware instruction profile.** Which `Befehl` forms the backend
   may emit, with their exact execution semantics, encoding rows,
   atomicity/tearing table, fence semantics, FP control obligations,
   and CPU-feature gates. Decided in Lean, proved per form. No OS
   content lives here.
2. **Declarative ABI/image/entry profile.** Calling convention, stack
   discipline parameters, section kinds, image container description,
   relocation kinds, entry vector shapes, and load-bias mode. This
   profile DESCRIBES a calling convention and an image format; it never
   implements OS functionality and never adds a hardware assumption.
3. **Program-supplied environment bindings.** Gabbro source files with
   declared user-logic contracts (`syscall`/`extern` items, gate
   declarations, entry bodies, runtime support) that supply what the
   environment provides. Their obligations are discharged by proof at
   actual arguments and results, never by trusting a name.

Consequences enforced by review:

- The semantic compiler, checker, and optimiser contain no
  Linux/POSIX/libc/ELF-only assumptions: no implicit hosted entry
  shape, no implicit section base, no implicit stack size, no implicit
  gate numbers, no implicit loader behaviour, no implicit thread
  library.
- OS-specific functionality lives in Gabbro bindings with declared
  user contracts, never as privileged compiler built-ins and never as
  hardware assumptions. The compiler hardcodes no operating system
  (per [IMAGE-ABI](IMAGE-ABI.md) sections 11–12).
- Adding an OS requires its supported profile plus its bindings
  (section 12), never a fork of source semantics, IR, executor, or
  validator.
- Generic lowering for calls and gates stays in Lean against the
  declared gate/binding interface; the program together with its
  environment selects the concrete ABI record and binding
  implementation. A lowering rule quantifies over the declared
  interface, never over one OS name.

## 2. Hosted and freestanding modes (PROPOSED)

Two modes, selected per image by the profile, never mixed silently:

- **Hosted mode.** The image runs under an execution environment that
  provides entry invocation, an initial stack, and the bound services
  (address-space reservation, thread creation, reporting, exit). The
  profile names the entry shape (`main` with `argc/argv/envp` per the
  hosted binding, or the `nolibc` hook pair `gabbro_os_anfang` /
  `gabbro_os_ende(code)` per `bau.rs::nolibc_haken` and template
  `start.nolibc`), the initial-stack guarantees the entry predicate
  may rely on, and which services are bound from the environment
  versus supplied by the program. Hosted does not imply libc: a
  `nolibc` hosted image calls only its declared gates.
- **Freestanding mode.** The image is its own execution environment
  from its listed entry onward (bare-metal `_start`, kernel-module
  init/exit, or an equivalent freestanding entry of the selected
  profile). There is NO implicit libc, NO implicit host allocator, NO
  implicit threading library, and NO implicit dynamic loader. Memory,
  stacks, interrupt wiring, and device access exist only where the
  image and its bindings supply and validate them.

Freestanding does NOT require every program to implement an OS. A
freestanding program supplies what IT uses: its entry body, its stack
and region reservation for its own needs, and bindings only for the
services it calls. An unused service (networking, filesystems,
schedulers the program never touches) is simply absent from the
closure; absence of an unused binding is not a refusal. What IS
refused is a USED service without its supplied body, contract, and
mapping evidence (section 7).

## 3. Executable and relocatable outputs (PROPOSED, none implemented)

The backend interface (`write_image`, per
[IMAGE-ABI](IMAGE-ABI.md) section 13) is container-agnostic: it
produces validated bytes plus sections, relocations, and entries, and
the Lean validator decides them. Planned container descriptions, as
unimplemented examples only, are:

- **ELF executable** (static hosted image, fixed-bias mode).
- **ELF relocatable / position-independent image** (parametric-bias
  mode with checked side conditions).
- **PE-COFF and Mach-O image descriptions** as further parametric
  profile instances, each with its own section/relocation/entry rows.
- **Raw image** (freestanding: flat bytes plus the profile's load
  address, entry, and BSS-zero obligations, e.g. the current
  `metall.ld` layout generalised per
  [IMAGE-ABI](IMAGE-ABI.md) section 1).

No container support is claimed today. Each container description is a
profile DATA instance subject to the same generic obligations
(section 8): decoded-start targets, permission checks, relocation
admissibility classes, entry predicates, and loaded-mapping equality.
Native linker success is never acceptance: whatever a system linker
emits is re-read as bytes and re-validated with no shortcut (per
[IMAGE-ABI](IMAGE-ABI.md) section 13).

## 4. Stack and ABI parameters (PROPOSED)

Per profile, stated as checked data and decided per call/return/entry
by the validator (groundwork: `Stapel.lean` frames, alignment,
spill-slot round-trip; `EntryState.lean` entry predicates):

- **Call-boundary alignment.** 16-byte alignment at every call
  boundary for the System V AMD64 ABI family; any profile with a
  different rule states its rule explicitly with its own entry/call
  checks. The entry predicate includes the alignment the entry
  requires; every call site establishes it for the callee.
- **Red zone.** Whether the 128 bytes below `rsp` are usable by leaf
  functions. The profile states permitted-or-disabled; any image with
  asynchronous entries that may land on a thread stack either proves
  red-zone respect at every interrupted point or compiles with the red
  zone disabled. The choice is recorded per image and checked.
- **Shadow space.** Where the profile's calling convention uses one
  (Windows x64 32-byte home space as the planned example, not
  implemented support): the caller reserves it, the callee may spill
  argument registers into it, and the validator checks reservation plus
  spill privacy. Profiles without shadow space state its absence; the
  backend emits no shadow-space traffic for them.
- **Callee-save discipline.** Stated per image, checked at every
  call/return pair: which registers survive, save/restore on all
  paths, no caller-spilled register clobbered by the callee. Gate
  trampolines carry the analogous obligation (emitter code C187 shape).
- **Thread-local storage (TLS).** Only where the profile and program
  use it: the profile states the TLS model (which segment/base,
  per-thread area extent, alignment, initialisation values), each TLS
  access carries its footprint against the thread-private area, and
  sharing a TLS slot across threads is refused. Profiles without TLS
  emit no TLS forms; a TLS access under such a profile is refused.
- **Unwinding.** Only where the profile requires tables (planned
  `.eh_frame`/equivalent as example, not implemented): the profile
  states which tables the image carries, they are validated data
  (covered bytes with declared widths, never trusted metadata), and
  absence where required is refused. No unwinding requirement is
  silently invented for profiles that do not need it.

## 5. System-call versus ordinary external-call bindings (PROPOSED)

Two binding kinds, both user logic with contracts, never assumptions:

- **System-call gates (`syscall` items).** Declared in Gabbro with the
  machine side (`abi ... number`, `regs in`, `regs out`, `clobbers`),
  the errno table, cost promise, named assumption reference, and
  falsifier (groundwork: `Grammatik/Syscall.lean` `SysAbi`/`sysAbiGutB`,
  `dekodiere`; pairing: `Grammatik/SyscallPaarung.lean`). Generic
  lowering emits the caller-side stub sequence for the DECLARED
  register map; the declared map varies per profile and per target
  (`via V` rebinding per `zielbindung.rs` N562–N567). Region answers
  (`tor.region`, emitter code C186), fallible channels (`tor.fehlbar`),
  top-level gates (`bindAxiom`), trampolines (`tor.trampolin`), and
  the clone handoff (`tor.kind`, N572, C187) each need their proved
  x86 template instance; a C-level template lemma alone does not
  discharge the x86 obligation (per
  [IMAGE-ABI](IMAGE-ABI.md) section 9).
- **Ordinary external calls (`extern fn` items).** Declared prototype,
  outer binding name without mangling, and arity held against the
  callee header by the validator, not the linker (`bindungsregel` /
  `bindungsregel_gehostet`). Variadic markers stand only on `extern`
  declarations (N573); a foreign body takes no parameter whose type
  carries a function pointer (N574). An `extern` declaration alone
  admits nothing: each call site needs the checked declaration, the
  proved caller-side sequence correspondence, and the supplied
  callee-side contract obligation at actual arguments and effects (per
  [IMAGE-ABI](IMAGE-ABI.md) section 11, obligations (a)–(c)).

The kernel/device half of every gate (what the environment does with
the call) is covered solely by the supplied, Lean-proved contract
obligation at the ACTUAL call, with the caller/callee boundary and
the refinement between them explicit. Historical software-behaviour
premises (`os_bindung_*` family, storage/page-return assumptions) are
gap records only and qualify no image (per
[IMAGE-ABI](IMAGE-ABI.md) section 12).

## 6. Entry before a stack exists, interrupts, devices, context (PROPOSED)

- **Entry before a stack exists.** The first instructions of a
  freestanding entry (mode switch, page-table setup, initial stack
  pointer establishment, AP trampoline copy) run before any stack can
  be assumed. This path is inventoried handwritten code with a written
  reason (`start.S` shape per [IMAGE-ABI](IMAGE-ABI.md) section 10),
  and the reason exempts NOTHING from validation: the executed bytes
  still need decoded correspondence and refinement, with entry-state
  predicates that do NOT assume a usable stack on input but ESTABLISH
  one (stack pointer value, alignment, guard, readable/writable word
  below the top per `EntryState.lean` `stapelOk`/`stapelRW`/`guardOk`).
  Until proved, the image using that path is refused.
- **Interrupt and device entries.** Each `entry ... via ...` item,
  timer/wake paths, and error-code twins are listed entries with
  checked save/restore sequences (full general-register plus x87/SSE
  state), declared `preserves` lists, IF discipline, and mask
  behaviour, each checked against the source entry semantics (per
  [IMAGE-ABI](IMAGE-ABI.md) sections 5 and 9). Same-core handler
  progress (`KernHaltE`) is validated under every core assignment of
  the profile's named core schedule, never one convenient assignment.
- **Context state.** General registers, flags (`Flags`, AF undefined),
  MXCSR (RNE, FTZ/DAZ off, masks set, sticky flags reserved per
  `Gleitprofil.lean`), XMM/YMM upper state where the SIMD tier applies,
  and the enabled-feature state (CPUID/XCR0/context proofs per
  DIRECT-COMPILER-DESIGN section 6) are entry-established facts,
  re-checked per image. Setup and context-switch save/restore are
  user/binding logic with contracts, never OS assumptions.

## 7. Closure boundary and final mapping checks (PROPOSED)

Whole-source-to-final-byte validation covers: the emitted unit, the
generated driver, every compiled-in binding body, every runtime body,
and every handwritten entry path — plus the ACTUAL executed mapping
(bytes at final addresses with final permissions). The boundary is
exact (per [IMAGE-ABI](IMAGE-ABI.md) section 11):

- **Inside the domain:** the image's mapped sections, driver-owned
  stacks with guards, reserved arena ranges once reserved, and listed
  entries. Every executed byte inside is validated with per-access
  refinement to W/GX.
- **Outside the domain:** the surrounding kernel, loader mappings,
  and any unrelated process or kernel bytes. These are never assumed
  safe, never implicitly executable, and never required to be
  included: validation does NOT demand every unrelated kernel byte,
  only the contract obligation for each CALLED service at its actual
  call site.
- **Crossing the boundary** is allowed only at listed gate/foreign-call
  sites meeting all three external-body obligations: (a) checked
  declaration, (b) proved caller-side stub correspondence, (c) supplied
  Lean-proved callee contract at actual arguments, results, and
  effects. A site missing any of the three is refused; unlisted foreign
  code is refused unconditionally; unresolved claimed obligations are
  refused, never trusted and never downgraded to warnings.
- **Relocation and load bias** follow the two modes of
  [IMAGE-ABI](IMAGE-ABI.md) section 4 (fixed bias F; parametric bias P
  with checked alignment/range/nonwrap/canonicality side conditions),
  with code-operand versus data-field admissibility classes, patched
  re-decode, and loaded-mapping re-check (groundwork: `Bild.lean`
  sections/mapping/modes, `Relokation.lean` arithmetic/patching,
  `TableLayout.lean` computed layout with recomputed-hint check,
  `Regionen.lean` checked reservation with ceiling and refuse-on-full).
  An OS name, a container name, or a native linker exit code proves
  nothing about any of these checks.

## 8. Per-profile acceptance gates (PROPOSED)

Each selected profile (one hardware instruction profile × one
ABI/image/entry profile × its bindings) is admitted only with ALL of
the following, each generic over all source texts, none per program:

1. **Generic validation obligations.** The validator decides for the
   profile: decode with lengths from decoding; permissions per
   section; relocation admissibility and patched re-decode; entry
   predicates (stack, guard, MXCSR/save, IF); call/return discipline;
   control-target obligations (direct targets are decoded starts or
   listed entries; indirect targets carry jump-table/data-flow
   certificates or are refused); per-access memory correspondence
   (width, alignment, ordering, footprints); template instances for
   every runtime/binding/entry sequence the profile uses.
2. **Memory-changing positive witness.** At least one accepted program
   shape per profile whose execution provably changes memory through
   the profile's own path (a reached run with a memory-changing step:
   a table write through the computed layout, a frame spill round-trip,
   a region reservation plus store, an entry-to-handler store — as the
   profile applies). A witness over an empty run or a declaration with
   no written table does not count.
3. **Negative probes.** Refused shapes the validator MUST reject for
   the profile: wrong container/ABI (e.g. SysV-aligned call checked
   against a shadow-space expectation and vice versa); misaligned or
   non-canonical load bias; relocation site in the wrong
   admissibility class; patched bytes that no longer decode; branch
   into mid-instruction or into data; entry with unusable stack,
   missing guard, wrong IF, or touched-XMM without validated save;
   gate stub moving a parameter into an undeclared register or
   clobbering the out-register; `extern` arity mismatch; forged
   pointer (M140); missing extent (N571 family); TLS access outside
   the thread-private area; unwind-table absence where the profile
   requires it.
4. **Source compatibility.** Budget (declared costs re-summed as a
   mismatch check; exhaustion timing preserved; CAS-retry divergence
   recorded, never bounded by invention), concurrency (per-access
   TSO-to-W/GX refinement for every atomic/shared access the profile
   lowers, no block-atomicity by declaration), and FP (scalar SSE2
   baseline per DIRECT-COMPILER-DESIGN section 4; no reassociation, no
   free FMA, no width change; NaN/±0 witnesses) — each re-established
   for the profile, never inherited by assertion from another profile.
5. **Eventual Rust tests.** Each profile carries end-to-end tests in
   the Rust suite once its Lean interface is reviewed: emit the
   profile's image, run the Lean validator over the final bytes
   (positive plus every negative probe above), and pin the refusal
   behaviour. No Rust test substitutes for the Lean soundness proof.

## 9. Cache keys and fast compilation (PROPOSED)

- **Cache keys** cover the COMPLETE validated configuration: source
  declarations, contracts, effects, callee summaries, hardware
  instruction profile, ABI/image/entry profile, environment bindings
  (sources plus versions), proof-schema version, and compiler version
  (extending the key list of DIRECT-COMPILER-DESIGN section 8).
  Changing the profile or any binding invalidates exactly the
  affected units plus cross-unit and final-image obligations.
- **Caches are untrusted.** A hash hit skips work, never checking: the
  validator still decides `valX86 E bild = true` on the final bytes,
  including fetched-bytes revalidation after every layout change.
- **Fast compilation still includes validation.** Compile-time budgets
  (pass fuel, relaxation rounds, linear-scan allocation, bounded
  improvement, warm Lean batching per DIRECT-COMPILER-DESIGN
  sections 8–9) bound the compiler, never the proof: exhausted
  optional-optimisation fuel yields a certified cheaper route;
  required validation failure refuses. The reported compile figure is
  backend-plus-validator-plus-kernel time for the accepted image,
  never backend-only time.

## 10. Practical dependencies (ACCEPTED helpers versus OPEN proofs)

ACCEPTED bounded helpers this design reuses (each proved over the
canonical vocabulary, none a chain correspondence):

- `Typen.lean` / `Wort.lean` / `Ganzzahl.lean`: registers, words,
  checked arithmetic, flag definitions.
- `Speicher.lean` / `SpeicherKommutation.lean` / `Zugriffe.lean`:
  permission-checked little-endian byte memory, footprints,
  single-owner access extraction, commutation facts.
- `Ausfuehrung.lean` / `Byteschritt.lean`: bounded per-form step
  equations over the pilot vocabulary.
- `Codec.lean`: canonical encode/decode round-trip over the pilot
  subset (non-canonical bytes refused).
- `Bild.lean` / `Relokation.lean`: sections, mapping, bias modes,
  relocation arithmetic and patching checks.
- `TableLayout.lean`: computed table/global extents with
  recomputed-hint acceptance and carrier enumeration.
- `Regionen.lean`: checked regions, bump allocation with ceiling and
  refuse-on-full, opt-in ceiling-free model.
- `Stapel.lean`: frames, 16-alignment, slot save/load round-trip and
  refusals.
- `EntryState.lean`: entry predicates (stack, guard, MXCSR/save, IF,
  listed entries, external-target refusal).
- `TSO.lean`: per-core FIFO buffers, forwarding, flush, local-fence
  readiness, byte-level visibility link.
- `Gleitprofil.lean`: MXCSR checks, per-context FP state, f32/f64
  projection with counterexample, NaN/sticky/SSE gaps.
- `Syscall.lean` / `SyscallPaarung.lean`: gate ABI well-formedness,
  errno decoding, user/kernel contract pairing shape.

OPEN (missing generic proofs; each a wave-B obligation, none claimed):

- Gate-stub correspondence (`GateStub`: pending lane 346 work —
  no such Lean module is accepted today).
- Per-form execution correspondence beyond the pilot step equations;
  per-width atomicity/tearing table; LOCK/RMW and fence semantics.
- Per-access TSO-to-W/GX refinement (`valX86_sound` and the closing
  `schluss_x86` schema per [QUELLBRUECKE](QUELLBRUECKE.md) section 4).
- Full-unit source computation beyond fragment defaults
  (`einheitAllg` limits per [QUELLBRUECKE](QUELLBRUECKE.md) sections
  1–3); lowering certificates; optimisation certificates; budget/work
  and time transfer; FP/hardware correspondence; template x86
  instances for every runtime/binding/entry sequence; linking image
  step (`GabbroZielVerbund` image side).

## 11. Adding an operating system: checklist (PROPOSED)

A new OS (or hypervisor, bootloader environment, or freestanding
platform) is added by supplying DATA plus Gabbro SOURCES, in this
order, with no change to language semantics, IR, executor, or
validator:

1. Hardware instruction profile instance: the subset of forms the new
   target's backend may emit, each with semantics, encoding rows, and
   atomicity/tearing/fence/FP rows. Unmodelled but reachable forms
   refuse.
2. ABI/image/entry profile instance: calling convention (alignment,
   red-zone/shadow-space/callee-save/TLS/unwind rows as used),
   container description with section/relocation/entry rows, entry
   vector shapes with predicates, load-bias mode with side
   conditions, stack sizes, guard pages, page behaviour, core
   schedule for handler progress.
3. Environment bindings in Gabbro: one binding library covering every
   service the programs on this OS use, each item with its declared
   contract (`requires`/`ensures`, extents, errno/reason mapping,
   effects, costs), plus the entry/runtime bodies the image links.
4. Lean-side per-item obligations: G semantics plus checker side for
   every new construct the bindings need (standing rule: modelled in
   Lean before merge, with `gabbro_ziel` still proved and a reviewed
   `Spec.lean` diff if the statement moves); Body model with bridge
   simulation; proved x86 template for every new emitted form.
5. Profile acceptance gates of section 8 (obligations, memory-changing
   witness, negative probes, budget/concurrency/FP compatibility,
   Rust tests), then independent exact-candidate review.

## 12. Capability refusal versus weakening (PROPOSED)

An unsupported profile, a missing binding, an unproved template, or an
unresolved external obligation REFUSES the image. Refusal is a
capability statement ("this profile cannot validate this program
yet"), never a weakened guarantee: no memory-safety, race-freedom,
contract, budget, lock-discipline, FP, or progress obligation is
dropped, widened, or turned into a warning to admit the image. The
validator's conservative routes (keep the check, keep the call, stay
scalar, stay with the wider branch encoding) are themselves validated;
there is no route "emit the fast form without its proof". Caps and
fallbacks from DIRECT-COMPILER-DESIGN sections 2B–2D and 7–8 apply
unchanged to every profile.

## 13. Guarantees and file ownership (ACCEPTED boundary)

- All goal guarantees are preserved for every profile: memory safety,
  race freedom (plus the atomic rely), contracts at their place with
  actual values, lock discipline, quiescent/observer and lock-move
  legs, start/end legs, no deadlock, handler progress under every core
  assignment, progress stop kinds, time bounds via named hardware
  assumptions only, and the call-order leg. No lane weakens any of
  them for portability or speed.
- The friend-reserved optimiser files
  (`grammatik/Grammatik/X86/OptimizationRules.lean`,
  `OptimizationWitnesses.lean`, planned specification in
  `../../grammatik/OPTIMIZER.md`) stay untouched by portability work:
  this document reserves profiles and bindings only and waits on the
  frozen IR interface. No parallel IR, no per-program rule, no
  program-name special case is introduced here.

*CUTS: design-only lane. No Lean definition, lemma, checker Bool,
decoder extension, validator, refinement, cost transfer, template
instance, or acceptance theorem is proved here. No OS support, image
writer, or container implementation is claimed. Every machine-behaviour
claim is tied to the ACCEPTED helpers of section 10 and the plan
sections named beside it; everything else is an explicit OPEN item in
sections 10–11. Hardware assumptions mean silicon-only behaviour; every
software-behaviour premise is named as user logic or a gap record per
[IMAGE-ABI](IMAGE-ABI.md) sections 11–12.*
