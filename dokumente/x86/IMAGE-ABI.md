# Final image ABI and loader contract

*Lane 276, wave A, 2026-10-01. Status: contract specification, not an implementation
or a proof. Nothing here claims a direct-x86 backend, ELF writer, decoder, or
validator exists today. The running compiler still emits C11 plus inline assembly
plus generated C drivers; the selected target is direct x86-64 machine bytes
(`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` secs. 0-5). This document fixes what
a future image backend must produce and what the Lean validator must check, so
wave B can build against a frozen interface.*

*Canonical ground: `grammatik/Grammatik/X86/Typen.lean` (`Gabbro.Grammatik.X86`).
`Byte`/`Wort`/`Adresse` are `BitVec 8/64/64`. The 16 registers are in architectural
encoding order. `Speicher` carries byte contents plus explicit
read/write/execute permissions. `Befehl` is the pilot subset only; displacements
are signed 32-bit; relative control flow is measured from the address AFTER the
decoded instruction; instruction length belongs to validated decoding, never to an
untrusted emitter annotation; loads/stores are base-register plus sign-extended
displacement; `Flags.af = none` is undefined, not false. No lane invents a second
register, instruction, byte-memory, or source-concurrency model.*

## 1. Validated image representation (generic)

A candidate final image is a tuple `(file, sections, relocs, entries)`,
plus a load bias governed by exactly one of the two modes of sec. 4,
all inputs to the Lean validator, all reconstructed or checked by it.
File ranges and virtual address ranges are different things, related by one
checked mapping defined here:

- `file`: the exact byte string produced by the backend. Not an instruction
  listing, not assembly text, not an object file with unresolved fixups.
  Validation input includes these bytes; a proof about a mnemonic list alone is
  insufficient (plan sec. 0-1, T2).
- `sections`: a finite list of disjoint, ordered extents
  `(file_off, filesz, vaddr, memsz, readable, writable, executable)` covering:
  executable code, read-only data, writable data, and BSS (`filesz < memsz`,
  the bytes from `vaddr + filesz` to `vaddr + memsz` are defined zero and have
  no file bytes). The checked mapping is: file byte at `file_off + i`
  (`0 <= i < filesz`) maps to virtual address `vaddr + i`, and to no other
  address; nothing outside a section's file range maps anywhere. Each section
  is checked for: file containment (`file_off + filesz` inside `file`, no
  arithmetic wrap), virtual nonwrap (`vaddr + memsz` wraps nothing),
  canonical form (bits 63:48 are the sign extension of bit 47), `filesz <=
  memsz`, pairwise disjointness in BOTH file space and virtual space, and the
  alignment the target data demands (4096 in the address space for the
  bare-metal layout). The current bare-metal layout that this generalises is
  `laufzeit/metall/metall.ld`: `ENTRY(_start)`, base 1 MiB, `.text`, `.rodata`,
  `.data`, `.bss` each `ALIGN(4096)`, with `.eh_frame`/`.note`/`.comment`
  discarded. A hosted image has the same section kinds; its base and alignment
  come from the target binding, not from this document.
- `base` (load bias): governed by sec. 4 (fixed-bias mode pins absolute
  virtual addresses; parametric-bias mode quantifies `base` with checked
  alignment, range, nonwrap, and canonicality side conditions). No address in
  the validation statement is ever `base + file offset + addend`: file offsets
  become virtual addresses only through the section mapping above, and
  relocation values only through their kind's operand-field semantics below.
- `relocs`: resolved relocations as data `(section, site_off, kind, symbol,
  addend, resolved_value)`. Each relocation kind belongs to exactly one of two
  admissibility classes and declares its site format (width, alignment, addend
  semantics, allowed section kinds):
  - code-operand sites: the site must match the kind's declared operand field
    of one decoded instruction (byte range WITHIN the instruction, never
    overlapping opcode/ModR/M/prefix bytes). A site inside a matching operand
    field is the normal legal case, not a violation. The validator maps the
    site to its virtual address, checks the patched bytes equal the encoding
    of `resolved_value` under the kind, then re-decodes the patched
    instruction and re-checks correspondence.
  - data-field sites: standalone data words the kind defines (function-pointer
    and static-address tables, explicit constant pools declared as data with
    their widths). These are legitimate where the kind defines their width,
    value rule, and target rule; each resolved value must satisfy the kind's
    target rule (code pointers land on decoded instruction starts in
    executable virtual bytes or listed entries; data pointers land on declared
    data addresses with declared widths). Data relocations are NOT broadly
    rejected for sitting "inside data" -- the check is class-specific.
  Refused: a site matching neither class for its kind (wrong byte range,
  wrong width or alignment, a code kind applied to a data field or vice
  versa, a kind applied outside its declared section kinds, a site between
  instructions that is neither a declared operand nor a declared data field),
  a resolved value violating its kind's target rule, and any fixup the loader
  applies that is not listed here. There is no "relocation premise" and no
  loader-only fixup: an unchecked fixup is a refusal, not an assumption.
- `entries`: the machine entry vector (sec. 5). Every address the loader,
  the kernel, or hardware can transfer control to without passing through
  validated code is listed here, with its expected machine state.

Decode boundaries are validated output, not emitter input: the Lean decoder
walks the mapped virtual ranges from each executable section start and each
listed entry/branch target and produces `(virtual address, Befehl, length)`
triples (`Decodiert`: instruction plus length). Relative displacements are
computed from the actual virtual next-RIP: `target = vaddr_after +
sign_extend(disp)`, where `vaddr_after` is the virtual address immediately
past the decoded instruction. Any byte not covered by exactly one
instruction, data object, or explicit padding is refused. Overlapping
decodings, ambiguous prefixes, and unsupported encodings are refused
(plan sec. 2: restrict accepted prefixes, addressing modes, and operand
combinations explicitly).

## 2. Initial data and BSS

- Initialised data (`.rodata`/`.data` contents, static initialisers, string
  literals, jump tables the backend chose to emit as data) is part of `bytes`
  and decoded as data at its declared addresses with its declared widths.
  Widths, layout, and bounds follow the source layouts the Lean front end
  computes (T3), not C `sizeof` facts.
- BSS (`memsz` beyond `filesz`, `*(COMMON)`, zero-initialised `static mut`
  arrays) is defined zero at load. The validator's initial-memory relation
  states this; the loader contract (sec. 11) must establish it. The page-return
  form (`region.leeren` over `gabbro_os_seiten_zurueck`, N569/N570) reads back
  as zero only under the gate's named assumption about kernel zero-fill
  (`bibliothek/linux/linux.gab`, storage assumption): a historical source-level
  gap record (see sec. 12), not hardware and not a loader axiom. It qualifies
  no final image: the zero-fill behaviour needs the supplied proved obligation
  of sec. 11(c), and until supplied, images using the page-return path are
  refused by final validation (OPEN).
- Dynamic arenas have no image bytes: the generated driver reserves their
  ceiling range at startup (`gabbro_arena_reserve` over `gabbro_os_reserve`,
  template `arena.dyn`) and commits pages per grow (`gabbro_os_commit`).
  The image contract covers the driver code that does this; the reserved range
  itself is fresh anonymous mapping, zero-filled, with the driver's checks
  (`arena_spanne_passt`, `arena_commit_bereich`) as validator obligations.

## 3. Section permissions

Permissions are the `Speicher` fields `lesbar/schreibbar/ausfuehrbar` at every
address, checked against `sections`:

- code: readable + executable, never writable (W^X);
- read-only data: readable, neither writable nor executable;
- writable data: readable + writable, never executable;
- BSS: readable + writable, never executable;
- guard pages (lowest page of each thread stack, driver-owned): neither
  readable, writable, nor executable; touching them faults by construction.

Any executed byte must sit in an executable section; any store must target a
writable address; any load must target a readable address. Permission is a
validator decision over the image, not a fact the backend asserts. Self-modifying
code, writable-executable mappings, and execution out of data sections are
refused.

## 4. Relocations and load bias: two modes, no third case

Every image is validated in exactly one of two modes. There is no unchecked
loader-only relocation in either mode: every fixup the loader applies must be
listed in `relocs` with its kind and checked value; a loader applying an
unlisted fixup breaks the mapping-equality obligation of sec. 11 and the image
is refused.

- Mode F (fixed bias): the image is validated at pinned absolute virtual
  addresses. Checked conditions: the base value itself, every section's file
  containment, virtual nonwrap, canonicality, disjointness, and alignment
  (sec. 1 mapping checks), plus re-decoding of every patched site. Loading at
  any other bias without revalidation is refused. Members: hosted static
  images at their link bias; the bare-metal image (loaded at 1 MiB, identity
  mapped -- virtual address equals physical address); a kernel module AFTER
  the kernel's relocation pass, at its loaded addresses.
- Mode P (parametric bias): the image is validated as a function of a
  universally quantified `base` with side conditions that are THEMSELVES
  checked, not assumed: the alignment the target binding demands; the range
  condition (for every section, `base + vaddr + memsz` wraps nothing, stays
  canonical, and all sections stay pairwise disjoint); canonicality of every
  resulting address.   Additionally, every absolute site in the image must be a
  listed relocation of a bias-carrying kind -- no absolute address outside a
  relocation's declared site (operand field or data field) may depend on
  `base`; the validator decides this syntactically over the decoded image. Members: hosted
  position-independent images. The bare-metal image is never mode P; a kernel
  module is never validated pre-relocation (the unlinked `.ko` bytes alone
  prove nothing).

Supported relocation kinds are enumerated per image kind and mode, each in
exactly one admissibility class. A code-operand kind states which decoded
instruction and which operand field it may patch (byte range within the
instruction, width, addend semantics); a site inside a matching operand field
is the normal legal case. A data-field kind states the standalone data format
it patches (table entry width and alignment, value and target rules); entries
of function-pointer and static-address tables and explicitly declared constant
pools are legitimate sites for such kinds -- sitting "inside data" is not
itself a violation. Code-operand and data-field relocations have different
checked admissibility: patched instructions are re-decoded with correspondence
re-checked; patched data fields are checked for width, alignment, and the
kind's target rule (code pointers to decoded instruction starts in executable
virtual bytes or listed entries; data pointers to declared data addresses with
declared widths). Refused: a site matching neither class for its kind, a
resolved value violating its kind's target rule, a kind applied outside its
declared section kinds, and any unresolved or loader-only fixup invisible to
the validator. Patched bytes that no longer decode, or decode to a different
form than the correspondence needs, are refused.

## 5. Entries: every first instruction must be listed

The validator admits control into the image only at listed entries, each with a
checked entry-state predicate (register contents, stack pointer, permissions,
interrupt state where applicable):

- hosted `main`: the generated driver's `main` (`crates/gabbro-cli/src/
  treiber.rs::erzeuge`, `treiber-gen-10`). C ABI entry, called by the C
  runtime with `argc/argv/envp` per the hosted target binding; returns an exit
  status to its caller. Under `nolibc` there is no C runtime: the generated
  entry (`bau.rs::nolibc_haken`, template `start.nolibc`) calls the unit's
  `gabbro_os_anfang()` first, runs `main`, and hands a returned status to the
  unit's `gabbro_os_ende(code)`; a `nolibc main` must end `-> never` or through
  `gabbro_os_ende` (build rule `eintrittsregel`), linked `-nostdlib -static`.
- kernel module init/exit (`treiber.rs::erzeuge_kmod`, manifest `kmod
  <kbuild> <load> <unload>`): the two loader-called symbols; init answers
  non-`void` so a failed load refuses the load; floating-point gates are
  refused in modules; atomics lower through the LKMM mapping table
  (`stdatomic.h` mapping of the nine C11 call forms). That table is a mapping,
  not a proof: its x86-byte correspondence is an unproved wave-B obligation,
  and no C-level argument discharges it.
- bare-metal `_start` (`laufzeit/metall/start.S`, `metall.ld ENTRY(_start)`):
  entered by the Multiboot1 loader in 32-bit protected mode; builds identity
  page tables for the low 4 GiB (2 MiB pages), jumps to 64-bit code, sets the
  BSP stack (`boot_stapel_oben`), and calls `metall_bsp` (`kern.c`). The AP
  trampoline (`tramp_anfang..tramp_ende`, copied to `0x8000` at run time) and
  the BSP/AP stacks are image bytes or BSS covered by this contract.
- thread roots: one thread per declared start occurrence, each entered through
  `gabbro_faden_start(root, stack_top, join_word)` on a driver-owned stack
  (hosted: 8 MiB region `seite + GABBRO_STAPEL` with the lowest page left
  unwritable as guard; bare-metal: 64 KiB driver stacks round-robined from
  core 1). Thread start follows the template path (`faden.laufzeit` /
  `faden.modul`, `tor.trampolin`, `tor.kind`: abstract proofs and C-target
  template instances exist, x86-byte correspondence open -- see sec. 9):
  parent `clone`, child runs the
  root on the handed stack, then the program's `-> never` thread end.
  The stack-gate call hands a `child` region (`klon.uebergabe`, N572).
- interrupt/hardware entries: emitted `entry NAME ... via idt` (or bare
  `entry`), the per-entry three-instruction half (`METALL_EINTRITT`), the
  common entry path, the LAPIC timer entry (vector `0x40`), and the wake entry
  (`0x41`) in `start.S`. These paths are executed bytes under full validation
  with refinement against the source entry model -- not manifest data: the
  validator checks the save sequence (full general-register plus x87/SSE
  state), the call into the entry's declared C half, the restore sequence,
  the declared `preserves` lists, error-code twins (`hat_fehlercode`), IF = 0
  discipline, and mask behaviour, each against the source semantics of the
  declared entry. A manifest row without validated save/restore bytes admits
  nothing.
- the clone child return: the trampoline's child path (`tor.trampolin`,
  `tor.kind`: lowered triple region `gabbro_kind_<nr>(handed)`, no `asm goto`
  into the parent frame) is a listed entry with the child's defined register
  state (kernel software behaviour per the gap record of sec. 12 -- no final
  image is accepted on that premise alone, sec. 11(c) applies: rsp is
  `spitze`, other registers are the caller's except rax, only rcx/r11
  destroyed).

Any machine transition whose target is not a decoded instruction boundary
inside executable bytes, a validated data address for a data access, or a
listed entry for an external transfer is a validator refusal.

## 6. Direct and indirect control targets

- Direct targets (`jump32`/`jumpIf32`/`call32` displacements, per `Typen.lean`):
  the validator computes `target = virtual_next_RIP + sign_extend(disp)`,
  where `virtual_next_RIP` is the virtual address immediately past the decoded
  instruction (never a file offset), and requires the target to be a decoded
  instruction start in executable virtual bytes, or a listed entry. A direct
  branch into the middle of an instruction, into data, or off the image is
  refused.
- Indirect targets (register/memory jumps, returns, function-pointer calls,
  `entry fn` values as parameters (N575-N577), dispatch targets of hardware
  entries): each must carry a validator-checked control-flow obligation --
  either a jump-table/data-flow certificate the backend ships and Lean
  re-checks and proves sound (table bounds, entry alignment, target list all
  inside executable bytes), or refusal. There is no fall-back "the linker got
  it right" premise.
- Returns (`ret`, thread-end `-> never`, `gabbro_os_ende`, module exit) must
  target a live caller frame the validator tracks (call-save discipline,
  sec. 8) or a listed terminal state. A `ret` with no caller, or a fall-off
  the end of a non-`never` function, is refused.

## 7. ABI: arguments, results, aggregates, function pointers

Two ABIs meet in every image; the validator checks both sides of each call:

- Gabbro gate ABI (the `syscall` declaration, `syscall.rs` N063-N066):
  in-registers pairwise distinct, out-register never clobbered, every
  parameter bound to exactly one register, every named register an x86-64
  general register, clobber list explicit. Buffer parameters (pointer at
  numbers) carry `requires x <= lenof(p)` over bytes (N464/N506/N571 family:
  index held against the extent the callee's `requires` names; fixed-size
  buffers bound by constant clauses). The errno table, cost promise, and named
  assumption (`assume`) are part of the gate; the stub the backend emits for
  the gate is checked against the declaration (emitter code C186/C187 refuse
  malformed stubs: region answer without its `or R` channel; stack gate
  without trampoline registers).
- C ABI at foreign boundaries (`extern fn`, `extern ...` variadic N573,
  foreign bodies N574, `bindungsregel`/`bindungsregel_gehostet`): prototype,
  outer binding name (no mangling), and arity are held against the callee's
  header; a wrong arity links yet reads an unset register, so the check is in
  the validator, not the linker. A foreign body takes no parameter whose type
  carries a function pointer (N574); variadic markers stand only on `extern`
  declarations (N573).
- Aggregates: struct/record layout, field offsets, padding, and alignment are
  the Lean front end's computation (T3 layouts), checked per access against
  the image's data addresses and widths. `static.ausrichtung` (`aligned N`,
  N570) constrains placement; `region.leeren` (N569) constrains the give-back
  range. The C `_Static_assert` pins of the old backend have no standing in
  the x86 chain: layout facts are Lean theorems or refusals.
- Function pointers and `entry fn(…) -> R` (N575-N577): where such a value
  stands, no Gabbro caller of a function taking one, and one whole hand-over
  outside every loop. The validator tracks the value from its creation (named
  function designator or gate answer) to each indirect call site; a pointer
  forged from an integer is refused (M140: no number becomes a pointer; no
  int-to-ptr or int-to-fn-ptr conversion enters the language).
- Results: integer/pointer results in the gate's out-register(s) per the
  declaration; fallible gates (`-> T or R`, `tor.fehlbar`, `bindAxiomElse`)
  carry the reason channel, checked at the top-level binding site; region
  answers (`tor.region`) carry the extent (`ensures … <= lenof(result)`) over
  a name bound once. `-> never` gates and bodies (`bindAxiom`, `Endblock`
  arms) never fall off; the validator requires a terminal transfer.

## 8. Stack discipline, spills, and registers

- Stack alignment: 16-byte alignment at every call boundary (System V AMD64
  ABI requirement the backend must meet and the validator must state). The
  entry predicates (sec. 5) include the alignment the entry predicate requires
  (checked at the entry, never trusted from the loader); every `call32` site
  must establish it for the callee; signal/interrupt
  entries state the alignment they provide.
- Red zone: the 128 bytes below rsp are usable by leaf functions only where
  the target binding permits it. Any asynchronous entry that may land on a
  thread stack (timer/interrupt entries, `start.S`) must either be proved to
  respect the red zone at every interrupted point or the backend must compile
  with the red zone disabled for units with such entries; the choice is
  recorded per image and checked, not assumed. (Today's metal entries run on
  the interrupted context's own stack; the declared per-CPU stack switch is
  named open, OFFEN O32 residue.)
- Spills: register allocation spills are ordinary validated stores/loads to
  private frame slots. Spill slots are per-activation, never shared between
  threads; the validator's footprint must show each spill address is
  thread-private (stack or private frame), so spills cannot create new races
  (plan sec. 3, first bullet). A spill of a value wider than its slot, a
  spill slot overlapping a neighbour frame, or a callee clobbering a
  caller-spilled register is refused.
- Call-saved registers: the backend's convention (which registers survive a
  call) is stated per image and checked at every call/return pair. The clone
  trampoline's minimum (C187: a stack gate with fewer than two callee-saved
  registers it neither binds nor destroys has no trampoline) is the shape of
  this rule at gate entries; ordinary calls carry the analogous obligation.
  The `clone` gate's register behaviour (only rcx and r11 destroyed) is a
  historical source-level gap record (sec. 12), not silicon and not a premise
  any final image is accepted on; any backend
  sequence relying on more than the declaration states is refused.

## 9. Threads and interrupt entries

- Thread creation is user logic: `gabbro_os_klon_tor` (stack gate over Linux
  `clone` number 56, flags from `gabbro_os_klon_flaggen`), the futex word wait
  (`gabbro_os_warte_wort`), thread end (`gabbro_os_faden_ende` / `exit`),
  yield (`gabbro_os_nachgeben` over `sched_yield`), and the kernel-thread
  triple (`kthread_create_on_node`, `wake_up_process`, `msleep`,
  `linux-kmod.gab`) are Gabbro functions over gates with checked contracts.
  What is PROVED today, and what is not: the abstract lock and machine
  results (`CTicket.lean` ticket lock over `sperrAbstrakt`) and the
  machine-checked template instances of the C target (template register:
  `tor.trampolin`, `tor.kind`, `faden.laufzeit`, `faden.modul`, `arena.dyn`,
  `sperre.ticket`, `tor.region`, `tor.fehlbar`, `tor.nie`, `start.nolibc`,
  module lifecycle) are proved against the abstract model and the C emission
  respectively. NONE of them has an x86-byte correspondence proof: every
  template's x86-byte instance -- the actual emitted sequences the validator
  will see -- is an unproved wave-B obligation, and no C-level lemma
  discharges it. The kernel-side half of each gate (what the kernel does with
  the call) is covered only by the gap records of sec. 12, which qualify
  nothing: final validation admits it solely through the supplied proved
  obligation of sec. 11(c), else the image is refused (OPEN).
- Join words, ticket locks, and the `madvise` page return are covered code in
  the same sense: abstract proofs plus C-target template instances exist;
  x86-byte correspondence remains open (sec. 17).
- Interrupt entries (`start.S` timer/wake/common paths, IDT bindings,
  `metall_eintritt_*`, core schedule `keinKernHalt` for declared handlers
  under every core assignment) run with IF = 0 on the interrupted stack, save
  the full general-register plus x87/SSE state, and call only the entry's
  declared C half -- and each of those facts is a refinement obligation
  against the source entry semantics (sec. 5), with reentrancy, nesting, and
  same-core interrupt deadlock as validator obligations; the named core
  schedule is target-binding data.

## 10. Coverage: all executed code is validated code

The validated image is the WHOLE executable that runs: the emitted unit, the
generated driver, the binding's Gabbro code compiled in, and the runtime the
image links. Concretely, for each product:

- hosted program: emitted `<unit>.c` bodies + `<unit>.treiber.c`
  (`BINDUNG_KOPF`, `ARENA_LAUFZEIT`, `SPERRE_TICKET`, `FADEN_LAUFZEIT`, roots,
  `main`) + the compiled-in `linux.gab` binding (report/stop, reserve/commit/
  page-size/page-return, yield, clone stack gate, write/exit_group) + the
  `nolibc` entry hooks where applicable. No libc, no pthread, no handwritten
  C remains on this path (`linux.c`, `bindung.h`, `faden.c/h`, `start.c`,
  `start_pool.c`, `arena_dyn.c` all deleted; os-probe report in Gabbro).
- kernel module: emitted bodies + `erzeuge_kmod` driver (init/exit,
  `KMOD_ARENA`, `KMOD_MELDECODES`, `KMOD_STDATOMIC`, note/provision sections)
  + `linux-kmod.gab` (`_printk`, `panic`, atomics mapping, thread
  start/join-sleep) + the two thread helpers still in C today. Every `.c`
  file a module build compiles is listed in the image manifest; unlisted C is
  refused.
- bare-metal image: emitted bodies + `<unit>.metall.c` + `laufzeit/metall/`
  (`start.S`, `kern.c`, `arena.c`, `metall.h`, `metall.ld`) + the unit's
  dispatch/entry halves. The handwritten pieces that remain are inventoried
  with their reason: `start.S` (mode switch before any stack exists; page
  tables; AP trampoline; entry save/restore paths Gabbro cannot express),
  the three-instruction `METALL_EINTRITT` halves, and the timer/wake assembly.
  Each keeps its written reason and stays counted; new handwritten C needs a
  reason why Gabbro cannot do it (standing instruction).

Anything the image executes must be validated bytes with refinement to P/GX:
emitted unit code, generated driver code, compiled-in binding code, runtime
code, and handwritten pieces alike. An inventoried reason exempts NOTHING from
validation: a handwritten path whose executed body bytes lack validated
correspondence and refinement keeps the image refused (OPEN), however well its
reason is written. In particular: unvalidated external calls cannot enter
through a declaration alone (plan sec. 0); a `foreign body` is refused unless
its x86 template correspondence is proved (a C lemma alone does not
discharge it). Transfers leaving the validated domain are allowed only at
listed gate/foreign-call sites meeting the external-body obligations of
sec. 11; arbitrary foreign code is never assumed safe.

## 11. Loader contract

Let `I` be the checked image (file + sections + resolved relocs + entries,
in mode F or P of sec. 4) and `M` the loaded mapping the machine executes.
The validated execution domain is: the image's mapped sections, the
driver-owned stacks and reserved ranges the image declares (thread stacks with
guards, arena ceiling ranges once reserved), and the listed entries. Everything
else in the address space -- the surrounding OS kernel for a module, loader
and runtime mappings for a hosted process -- is OUTSIDE the domain: never
assumed safe, never implicitly executable, reachable only through listed
gate/foreign-call sites.

- segments: every loadable section of `I` is mapped at its checked virtual
  address (mode F) or at `base + vaddr` under the checked side conditions
  (mode P) with exactly its checked bytes (BSS tail zero-filled) and exactly
  its checked permissions. Within the validated domain, no mapping beyond the
  checked set is executable; page granularity is stated: leading/trailing
  partial pages keep the section's permissions for their covered bytes; the
  loader must not widen executability to a neighbouring section through a
  shared page. A kernel module does NOT require the entire address space to
  contain only its text: the kernel's own mappings are outside the module's
  domain, and only the module's sections plus its declared stacks/ranges are
  checked. The boundary is exact: a transfer from inside the domain to outside
  it is allowed only at a listed external-call site meeting the obligations
  below; any other escape from validated bytes is refused.
- relocations: the loader applies exactly the `relocs` the validator checked,
  with the same values at the same virtual sites; after loading, the bytes at
  each site still decode as validated (re-decode obligation on the loaded
  mapping, not only on the file).
- external-body obligations: the intended chain permits USER LOGIC PROOF
  OBLIGATIONS and named HARDWARE behaviour -- nothing else. There is no third
  trust category, and software correctness renamed as an assumption is not
  one. Each listed gate/foreign-call site leaving the domain needs all three:
  (a) a checked declaration (gate register map and
  arity per N063-N066/`bindungsregel`, callee contract with `requires`/
  `ensures`, buffer extents); (b) a proved x86 template correspondence for the
  caller-side stub sequence; (c) a SUPPLIED, Lean-proved contract obligation
  for the callee side at the ACTUAL call: the binding/kernel logic contract
  (`requires`/`ensures`, effects and footprint, errno/reason mapping)
  discharged in Lean at the actual arguments, results, and effects of this
  call site, with the implementation/refinement boundary explicit (which
  caller-side bytes are validated, where the callee logic takes over, and
  what refinement relates the two). A gate name, an `assume` item, or any
  named premise alone discharges NOTHING: the historical `os_bindung_*`-style
  software premises (sec. 12) are gap records only and qualify no image for
  acceptance. Where obligation (c) cannot currently be supplied and proved,
  that path is recorded OPEN and the final validator refuses the image. The
  proof and the contract are binding/user logic in Gabbro and Lean -- a
  generic language compiler hardcodes no operating system and no Linux. A site
  missing any of the three is refused; unlisted foreign code is refused
  unconditionally.
- entries and initial state: the loader transfers control only to a listed
  entry, with that entry's predicate met (stack pointer, alignment, BSS zero,
  arena reservations for the hosted driver before the first root runs,
  single-threaded start shape A4: every thread but 0 idles in the runtime
  root). Declared `concurrent` roots start exactly as generated
  (`gabbro_faden_start` sites match the source sets; the pin probes check
  this today, the validator checks it in the chain).
- NO tool-correctness premise, and NO software booked as hardware: no
  assumption that "the assembler/linker/loader/C compiler/kernel did it
  right" appears in the chain. Software steps (linking, `modpost`, kernel
  load, Multiboot1 handoff, page-table setup) are checked by their outputs
  (file bytes, loaded mapping equality, entry predicates) or by validated code
  plus checked logic -- never by assumption, and never as hardware
  assumptions. Hardware assumptions are silicon-only: execution of the mapped
  bytes per the admitted profile, named device behaviour (MMIO/DMA/cache
  attributes with their own semantics, never ordinary-RAM rules by default),
  and named timing bounds. They are reviewed in `Spec.lean`'s header list.
  OS services, schedulers, lock code, loaders, and runtime routines are
  user/binding logic with contracts, not assumptions
  (plan sec. 3, last paragraph; sec. 5, second paragraph).

## 12. Target-binding data versus generic compiler mechanism

The compiler is not Linux-specific and knows no operating system. What varies
by target is DATA, read from `target … { … }` blocks and per-target gate
bindings (`zielbindung.rs` N562-N567: one `syscall V;` declaration, `via V`
at each gate, every target binds every used variable, one name is one ABI, no
literal gate beside targets, inactive targets held to the gate's shape):

- per-target data: gate numbers, register maps, clobber sets, errno tables,
  cost promises, entry shapes (`_start` vs `main` vs module init/exit),
  section bases/alignments, stack sizes, page behaviour, availability of SIMD/
  BMI profiles, interrupt wiring. Plus the named software-behaviour premises
  (`os_bindung_*`, `os_bindung_faden`, `os_bindung_klon`, storage/page-return
  assumptions in `linux.gab`): these state what the KERNEL's software does
  (clone/futex/mmap/madvise/join-word/zero-fill behaviour). They are
  historical source-level gaps and are documented as gaps ONLY: no final image
  is accepted on their basis, and they do not satisfy obligation (c) of
  sec. 11. Hardware assumptions are silicon-only
  (sec. 11). The direction of travel is replacement with supplied, Lean-proved
  binding/kernel logic contracts at actual arguments/results/effects plus the
  explicit entry and external-body obligations of secs. 5 and
  11; until supplied, images exercising those gates are refused by final
  validation (OPEN). Source-level checker acceptance is a different chain with
  a different claim and is unaffected by this statement.
- generic mechanism: decoding, permission checking, relocation checking, entry
  predicates, call-save/stack/spill discipline, control-target obligations,
  certificate soundness, refinement to P/GX, cost transfer. These stay generic,
  parameterised by the target data above -- and each of them is a wave-B proof
  obligation, none of which is claimed to exist today (secs. 14, 17).

A new target (another kernel, another loader, another interrupt controller)
adds a binding library in Gabbro plus target data; it does not fork the
validator, the decoder, or any proof.

## 13. Minimal image-backend interface (interface only)

No code below is claimed to exist. The first backend that writes bytes answers
this interface; until it does, the interface is the review surface:

- `write_image(unit, target_data) -> (bytes, sections, relocs, entries,
  cert_hints)`: pure function of the checked unit (parser/elaborator output,
  layouts, duties) plus the target data of sec. 12. It may carry hints and
  certificates; the validator trusts none of them without re-checking.
- the backend is untrusted: optimiser passes, register allocator, encoder,
  and layout choices stay outside the trust base (plan sec. 0). Incorrect
  output causes refusal once the checker is complete; that completeness is a
  target, not today's claim.
- the hosted path links with the system linker today; the metal path links
  with `metall.ld`; the module path builds against the kernel tree. In the
  x86 chain the LINKER is untrusted too: whatever it emits is re-read as
  `bytes` and re-validated. A minimal ELF writer (or equivalent) that bypasses
  the system linker is permitted as an implementation choice, not required by
  this contract; if built, its output passes through the same validator with
  no shortcut.

## 14. Certificate checking obligations (generic)

For every accepted image the Lean checker decides, statement by statement and
access by access, that the bytes are the emitted form of the source program P
(T2 sound validator; reuse the `korrOk` architecture, not its C conclusions):

- source fidelity: Lean parser/elaborator compute P, layouts, and duties from
  the source text (T3); no name, example number, or per-program model
  determines acceptance; per-program instances are witnesses only.
- per-instruction correspondence: each decoded instruction is the lowering of
  a source operation at its place, with widths, bounds, overflow/division/stop
  behaviour, and fault preservation proved per form admitted.
- per-access memory correspondence: every load/store/RMW maps to a model
  footprint with its width, alignment, and ordering; ordinary accesses,
  atomics, fences, and `pause`/retry loops each carry their lowering proof;
  no block executes atomically by declaration -- grouping needs a commutation
  or linearisation proof over real interleavings.
- duties: typing/safety certificates (T1), user-logic duties through the
  GabbroV bridge (computed in Lean from the source), runtime/entry/lock/call/
  hardware templates bound to the target semantics (T5), cost transfer with
  validated machine costs and named silicon-only timing bounds (sec. 11).
- concurrency: per-access x86-TSO executions refine to W then GX (or directly
  to GX with every goal property preserved); the bridge covers byte memory,
  widths, overlap, tearing, store buffers, forwarding, coherence,
  acquire/release, locked RMW success/failure, locks, start/join,
  publication, interrupts, call boundaries, finite and infinite executions
  with proved stutter, and progress/cost preservation (plan sec. 3).

## 15. Rejection cases (concrete, non-exhaustive)

Each is a validator refusal with a witness shape; none is a new diagnostic
code (wave A mints none) -- they pin the contract's teeth:

- altered byte: flip one opcode byte in validated `.text`; the decoder
  produces a different `Befehl`, a different length (shifting every following
  boundary), or no instruction; correspondence fails at that virtual address.
- relocation with an invalid site: a site matching neither admissibility
  class for its kind -- neither a declared code-operand field (wrong byte
  range inside the instruction, overlapping opcode/ModR/M/prefix bytes, wrong
  width) nor a declared data field of a data-field kind (wrong width or
  alignment, undeclared table format), a resolved value violating its kind's
  target rule, or a kind applied outside its declared section kinds; refused
  even if the pre-patch bytes decoded cleanly. Sites in a MATCHING operand
  field and declared data-table entries are the legal cases (sec. 4).
- wrong ABI: gate stub moves a parameter into a register the declaration does
  not bind, clobbers the out-register, or answers the wrong width; call site
  passes six integer arguments while the callee reads a seventh off the
  stack; callee cleans a caller-cleaned stack or vice versa.
- unchecked foreign body: an `extern fn` call site whose callee has no proved
  x86 template correspondence; the declaration alone admits nothing.
- forged pointer: integer-to-pointer or integer-to-function-pointer
  conversion at any site (M140); `entry fn` value created anywhere but a
 whole hand-over outside loops (N575-N577).
- missing extent: pointer index with no `requires` extent naming it (N571);
  length claim past the gate's region extent (N463/N506); double-bound name
  carrying no extent.
- entry violation: branch to a non-entry from outside the image; interrupt
  firing into a function that disabled the red zone without declaring it;
  thread started on a stack without a guard page where the image promises one.
- permission violation: store to `.rodata`, execution from `.data`/BSS,
  writable-executable mapping anywhere.
- BSS/data mismatch: loaded BSS nonzero at entry; initialised data differing
  from the validated bytes; loader-applied relocation differing from the
  checked `resolved_value`.
- unchecked tool output: image bytes that changed after validation (relink,
  restrip, post-pass) without revalidation; an executable mapping inside the
  validated domain (sec. 11) that the image does not list; any transfer
  leaving the domain outside a listed gate site meeting all three
  external-body obligations.

## 16. Architectural hazards (must be addressed, not assumed away)

- Variable-length decoding with overlapping candidates: boundaries are proved
  from the bytes, never trusted from hints; data-in-code (jump tables,
  constant pools) needs explicit data ranges so decoding stays disjoint.
- Overlapping/unaligned accesses, tearing, and atomicity limits of the
  admitted profile; private spill/frame slots proved disjoint from shared
  footprints.
- Store buffers, forwarding, and coherence: the TSO bridge is per access,
  with `seq_cst`-as-release/acquire documented as an abstraction with limits,
  not a proved total SC order.
- MMIO, DMA, cache attributes, and device observations: separate named
  hardware semantics; never inherit ordinary-RAM rules silently.
- Floating point: SSE/SSE2 scalar only, with rounding, exceptions, NaNs,
  and control state bound to the IEEE model (lane 278 owns the mapping);
  kernel-module and interrupt paths that must not touch SSE state are
  refused if their lowering does.
- Timing and progress: instruction counts are not time bounds; spinning or
  diverging implementations cannot vanish in projection; costs transfer only
  through validated machine costs plus named hardware bounds.
- Finite machine, unbounded-region programs: physical memory is finite; the
  opt-in region without a ceiling loses the static whole-program bound by
  design and must handle every allocation failure.

## 17. Gaps and wave-B handoffs

Not proved here; each names its owner:

- Decoder and round-trip (encoder/decoder, length theorems): wave B,
  needs pilot instruction semantics (lane 272) and memory model (lane 271).
- Per-access TSO refinement to W/GX: lane 274 owns the bridge obligations;
  this contract states what it must cover (sec. 14), not that it holds.
- Source lowering and certificates: lanes 275/277 (SSA/certificate
  architecture, source-computed duties, closing interface).
- Machine semantics of each admitted form: lanes 270-272 (word/flags,
  memory, execution witnesses).
- Float/time mapping: lane 278.
- Template correspondence for every runtime/binding sequence named in
  sec. 10 (`arena.dyn`, `sperre.ticket`, `faden.laufzeit`, `faden.modul`,
  `tor.trampolin`, `tor.kind`, `tor.region`, `tor.fehlbar`, `tor.nie`,
  `start.nolibc`, module lifecycle): abstract proofs and C-target template
  instances exist; each needs its x86-byte instance with refinement;
  the C-level proofs do not transfer silently.
- Handwritten runtime/entry bytes (`start.S` paths, `METALL_EINTRITT` halves,
  remaining module C helpers): validation plus refinement per executed body;
  until then those paths stay OPEN and refuse the image (sec. 10).
- Kernel-side gate premises (`os_bindung_*` family, storage/page-return
  assumptions): gap records only (sec. 12); replacement with supplied,
  Lean-proved binding/kernel logic contracts per sec. 11(c), else the using
  images stay OPEN and refused by final validation.
- The image writer itself: unbuilt; sec. 13 is its interface, not its
  existence proof.

*CUTS: no decoder, encoder, validator, refinement, cost-transfer, or
final-image acceptance theorem is proved here. No new Lean file is added by
this lane; the contract above is prose reviewed against the cited sources,
including the file/virtual mapping, the two bias modes, the loader domain,
and the external-body rules. Every machine-behaviour claim is tied to
`Typen.lean` and the plan sections named beside it; anything beyond the pilot
`Befehl` subset, beyond ordinary coherent RAM, or beyond the listed entries
is an explicit gap in sec. 17. Hardware assumptions in this document mean
silicon-only behaviour (sec. 11); every software-behaviour premise is named
as such (sec. 12).*
