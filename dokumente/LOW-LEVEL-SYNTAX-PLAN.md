# Low-level syntax: one neutral language from the reset vector to the kernel

> Since 2026-11-23 the forms of this plan are built as steps S1b (reference AST) and S6L of
> [PERFECT-MODEL.md](PERFECT-MODEL.md) §8, on the same level as every other form; the goal theorem they serve is
> PERFECT-MODEL §2. Where this plan speaks of the goal or of `Spec.lean`, PERFECT-MODEL decides.

Status: design. Ordered for complete implementation by the owner on 2026-11-03; **redesigned by the owner's
decision O23 of 2026-11-23** (PLAN-COMPILER-READY §8): "context ist auch nur iasm, und GIR soll Compiler- und
Modellsache sein, nicht Nutzersache, deshalb Syntax für alles, auch von 16-Bit-Boot an, also auch schon Long Jump
oder Jump; Ziel: der Kernel kompiliert fast gleich für alle Architekturen, abgesehen von Registern oder Adressen."
The compile-time selection `if (…) then { … } else { … }` (§4.10) is the owner's addition O24 of the same day.
O26 (same day) adds devices found at run time, wide and enqueued device stores (§4.6) and hard timing (§4.18);
CPU code that the compiler did not emit stays refused.
O25 (same day) adds hardware virtualisation, IOMMU spaces, suspend/resume, debug and performance units,
backtraces, guest grants and secure worlds (§4.11–§4.17); JIT and kernel modules get no syntax.

O23 replaces the earlier design of this plan, in which privileged operations were calls of target-binding
functions over a linear `context<P>` (one contracted function per machine operation). Such an interface is inline
assembly with types: the user still picks machine operations one by one and in architecture order, and every
kernel source names its architecture's operation set. It is removed before it is built. The syntax below is not
accepted until its canonical Lean rules exist (AGENTS.md §2: the model comes first). Its implementation targets are
the Lean model, the parser/exporter and the checker (rows L0–L17 of PLAN-COMPILER-READY §3), then the compiler on
GIR (C, K); Stage 0, the runner and today's GabbroV keep refusing these forms (their duty rules come with C1).
A review of 2026-11-23 (GPT Sol 6.1, 25 findings, each checked by the lead) is folded into this text.

## 1. The rule

1. **Every machine-level concept a kernel needs is a statement or declaration of the language** with a rule of
   machine G over the neutral architectural state (§3). Concepts, not instructions: "activate this address space",
   not "write CR3"; "jump into the 64-bit kernel state", not "set EFER.LME, set CR0.PG, far jump".
2. **GIR, its cells and the target table are the compiler's and the model's business.** No user source names an
   instruction, a GIR cell, a target row or a function standing for one instruction. The compiler lowers each
   construct to GIR cells, the table gives the bytes, and one generic theorem per construct covers every program.
3. **What a source may name that is specific to a platform** is exactly three kinds of data, all in a *platform
   unit* (§6): **registers** (system/model-specific registers and device registers, by number or name, width, field
   layout and access), **addresses** (device windows, I/O ports, fixed physical places such as the reset vector or
   a low-memory window) and **environment interfaces** (firmware services such as UEFI, PSCI or SBI, with declared
   contracts). The kernel proper — boot path, memory management, translation, interrupts, cores, threads, guests,
   system calls — is the same source text on x86-64, AArch64 and RISC-V 64. Device protocols are not registers:
   drivers stay per device behind a common driver interface and are chosen by compile-time selection (§4.10).
   **Registers that a construct manages are reserved** (translation roots, protection and memory-type controls,
   vector bases, privilege and interrupt state, virtualisation and IOMMU controls): the platform unit cannot declare
   them. Any other system register needs a modelled effect on the neutral state and the ledger; a register whose
   effect is not modelled is refused, and a hardware contract never stands in for the missing language rule.
4. **No assembly, no `unsafe`, no number as authority** (AGENTS.md §2). There is no assembly text, no instruction
   string, no `asm` block and no per-body certificate anywhere. A number never grants memory, a device or code.
5. **Boot starts wherever the chosen boundary is, down to the reset vector.** Code can be written for any execution
   state the hardware has, 16-bit real mode included; a transfer between states is one statement.

## 2. Why the earlier design is replaced

| Earlier design (2026-11-03/12) | Problem | O23 |
|---|---|---|
| `cpu::install_root(c, root)`, `cpu::set_mask(c, m)` … over linear `context<P>` | one function per instruction: inline assembly with types; the kernel source is architecture-shaped | `activate space s`, `interrupts off { … }` … with model rules; the compiler chooses instructions |
| binding library per target with descriptor tables, paging format, vector layout | user-visible per-target code that a kernel calls | the compiler generates descriptor tables, page-table entries and vector tables from neutral declarations (§4); only registers, addresses and environment interfaces stay in the platform unit |
| first boundary only at 64-bit firmware entry; 16/32-bit only as an opaque generated start item for further cores | boot from 16 bit impossible in source; the start item was a hidden blob | execution states of every width are declared states; `jump long` transfers between them; the start code of further cores is Gabbro source |
| `ram_view(c, a, n)` looked up authority by address in a context ledger | address → authority lookup; the context had to be threaded everywhere | raw memory is owned as regions from the start (§4.2); addresses are inert data used for tables and devices only |

The authority ledger (live spans, spaces, permissions, memory class, owner, epoch, per-core execution state) stays
— as part of machine state in the model, tracked statically by the checker as a typestate of each code point. It is
no longer a value the user passes around.

## 3. The neutral architectural state (model)

Per core: execution state (§4.1: width, privilege, translation on/off and active space, guards), interrupt mask and
priority, installed vector table (generated), per-core base, the extended register state (float and vector
registers), the core's identity and run status (parked, started, stopped). Global: physical memory with its
ownership ledger and epochs, translation tables, device register state (A2: history-dependent), the environment
services still alive. Every construct below is one rule over this state in machine G (and GX/W for its
interleavings); every intermediate observable step stays visible to the rely. Architectural nondeterminism is
covered universally, never resolved to an observed result.

## 4. The constructs

Final spelling follows the canonical Lean grammar review. Each construct lists its x86-64, AArch64 and RISC-V 64
lowering to show that the source is neutral (the lowering column is compiler work, never user code).

### 4.1 Execution states and transfers

```gabbro
// Declared once per kernel (neutral); a platform names its arrival states (reset, firmware, further core).
state kernel  { width 64, privilege kernel, translation on, guards { no_execute, user_access, user_exec } }
state flat64  { width 64, privilege kernel, translation off }

// A code item declares the state it runs in; the checker refuses a call or jump from any other state.
code reset_entry in platform.reset {            // x86: 16-bit real mode; AArch64: EL3/EL2; RISC-V: M-mode
    let ram   = platform.reset_ram();            // the RAM region the reset contract names (§4.2)
    let (boot_tables, rest) = ram.split_pages(16);
    let space = boot_space(boot_tables, image);  // identity map of the image, built with `map` (§4.3)
    jump long kernel_main(rest) into kernel with space;
}

code kernel_main(ram: region<normal, rw>) in kernel -> never { … }
```

- `state S { … }` names an execution state: operand width (16, 32, 64), privilege (`machine`, `hypervisor`, `kernel`,
  `user`), translation (`off`, `on`), guards (no-execute, kernel access to user memory only through §4.7, kernel
  execution of user pages forbidden). A platform declares which states exist and which are arrival states; a
  state a target lacks is refused by name for that target.
- `code f(…) in S { … }` compiles `f` for state `S`. Every ordinary language form is allowed in every width; the
  table's rows for that width tile it (performance in 16/32-bit code is irrelevant, correctness is not).
- `jump f(args);` transfers to a named code item in the SAME state without return (a tail transfer; the type of the
  current item is `never` there). No address becomes a destination.
- `jump long f(args) into S [with space s] [stack t];` transfers to a named code item in ANOTHER state. The
  compiler generates the complete sequence: x86-64 16→32→64 (generated descriptor table, protection enable, far
  jump, PAE, long-mode enable, translation root, paging enable, far jump), AArch64 EL3/EL2→EL1 (generated system
  register setup, exception return), RISC-V M→S (status, trap delegation, translation register, `mret`). Model
  rule: preconditions (the target code is mapped executable at its address in `s` AND in every intermediate
  translation regime the sequence passes, the stack is owned and mapped, the arguments fit the target state, the
  tables the sequence loads are owned and unchanged by other cores) and an abstract state change. That abstraction is
  admitted only through a **proved transition protocol per target**: a lowering invariant over every intermediate
  architectural state (continuity of the executing code, temporary mappings, descriptor and table accesses, stack
  establishment) and over every event the manual allows in it — maskable interrupts are masked, an NMI, fault or
  machine check in an intermediate state reaches a defined generated handler or is a named terminal outcome of the
  model, never an undefined state. Other cores observe only the declared table writes. The arguments arrive as
  ordinary parameters. Lowering to user privilege is not a `jump long`: it is `enter guest` (§4.7).
- `wait for interrupt;` and `stop core;` (`never`) are statements; `cpu.cycles()` reads the cycle counter.
- **Capabilities** come from a compiler-managed descriptor, not from a raw query: `cpu.caps` is filled by generated
  discovery code through the privileged or environment mechanism each target has (x86-64 CPUID including the
  XSAVE component enumeration; AArch64 ID registers readable at EL1; RISC-V the ISA string of devicetree or ACPI
  RHCT and SBI probing, since `misa` is readable only in M-mode). `cpu.has(f)` reads it; the extended-state
  layout and size of §4.5 are derived from it and from the enabled component set.

### 4.2 Memory authority without contexts

- `address<S>` is inert data with a space (`physical`, `virtual`, `port`, `guest_physical`, `io_virtual`) and the
  width of that SPACE, never the operand width of the state: physical addresses have the target's physical width
  even in 16-bit code (the x86-64 reset fetch at `0xFFFFFFF0` uses a hidden segment base; segmented and reset
  address formation stay inside the target model and the lowering, proved against region extents); arithmetic
  needs non-wrapping bounds or a failure channel; equal numbers do not imply authority; a physical and a virtual
  address are different types; no address becomes a reference or a code destination (`M140` stays).
- **Raw memory is owned as regions from the first instruction.** An arrival state's contract hands the code its
  initial regions: `platform.reset_ram()` (the reset contract: hardware), the UEFI memory map (`FirmwareHandoff`),
  the loader's memory description (`BiosHandoff`). A region `region<normal, rw>` knows its physical extent.
- `r.split_at(a)`, `r.split_pages(n)`, `merge(r1, r2)` move authority by proved partition; `r.view as T` gives a
  typed view (representation, endianness and layout proofs; uninitialised bytes are written before read, L3);
  `r.address()` reads the inert start address for tables and devices. There is no way from a number to a region.
- Reuse and revocation follow the epochs of L1 and the quiescence rules of §4.3.

### 4.3 Address spaces and translation

```gabbro
let s = space.new(tables);                  // tables: an owned region; format is the compiler's
map(s, virt, frames, rights { read, write }) else full;
protect(s, virt, n, rights { read });
let pending = unmap(s, virt, n);            // a revocation token, not yet the frames
let frames  = flush(pending);               // generated shootdown to every possible user; then the frames
activate s;                                 // installs the root on this core
```

- The table format (x86-64 4/5-level entries, AArch64 descriptors with granule, RISC-V Sv39/48/57) is target
  knowledge in the compiler; the user maps regions, never writes an entry. Large pages are chosen by the compiler
  where extent and alignment allow; a kernel never writes a page size as a literal but uses `target.page_size`
  (4 KiB, or 16/64 KiB granules).
- **Memory kinds are defined by observable properties**, not by one target's attribute names: cacheable or not,
  idempotent or not (may a load be repeated or done speculatively), gathering and reordering allowed or not,
  write combining allowed or not. `normal` = cacheable, idempotent; `uncached` = non-cacheable but idempotent
  memory; `device` = non-idempotent, no gathering, ordered; `write_combining` = non-cacheable, idempotent,
  gathering allowed. The compiler lowers them to PAT/MTRR, MAIR or Svpbmt (`NC` for `uncached`, `IO` for
  `device`). A device region can only be mapped as `device`; a kind the target or the region cannot realise is
  refused, and a fallback is written explicitly through compile-time selection (§4.10), never chosen silently.
- **Shootdown and reuse.** A space records its possible users (cores that have it active or may activate it) and a
  mapping generation. `unmap` makes the entries invalid and returns a revocation token; `flush(token)` emits the
  inter-processor interrupts, the generated flush handler and the acknowledgement wait to EVERY possible user, or
  bars a core from activating the space until it has synchronised with the new generation; only then does it
  return the frames (x86-64 IPI + `invlpg`/`invpcid` with PCID handling, AArch64 broadcast `tlbi … is` + `dsb ish`
  + `isb`, RISC-V SBI remote fence or IPI + `sfence.vma` with ASID; global mappings are flushed without ASID
  restriction because ASID-selective fences exclude them). Concurrent `map`s of the same range are serialised by the
  space's lock discipline, so no old entry can be reinstalled. Theorem: after `flush` no core translates the range
  by an entry of an earlier generation, so the frames may be reused. ASID/PCID reuse goes through the same protocol.
- Two virtual aliases share one physical identity (L6); `Mmu` (hardware) says the unit translates by the installed
  tables and caches as the architecture manual says.

### 4.4 Interrupts, exceptions and entries

```gabbro
entry timer interrupt priority 2 stack per core { … }
entry page_fault exception (f: fault_info) { … }
entry nmi nonmaskable stack own { … }            // lock-free code only, own stack
entry machine_check stack own -> never { … }
entry double_fault fatal stack own -> never { … }
interrupts off { … }                               // scoped per-core mask, restored on every exit
priority at least 3 { … }
send interrupt timer to core k;                    // inter-processor interrupt
```

- The compiler generates the vector table (IDT with gates and IST stacks, VBAR table, `stvec` table) and every
  entry/exit frame from the declarations (L5, one generic theorem per frame kind). Interrupt numbers that differ
  per platform are platform register/address data (§6), bound to the neutral names.
- The interrupt controller's architectural part and the per-core timer are constructs, not drivers, because every
  target has a different one: `route line l to core k priority p`, end-of-interrupt generated in the entry frame,
  `timer.at(t)` / `timer.after(d)` per core (x86-64 local APIC with TSC deadline, AArch64 GIC CPU interface and
  generic timer, RISC-V AIA/PLIC with Sstc or the SBI timer). The platform unit names the controller kind and its
  addresses; external interrupt sources behind it are ordinary devices.
- `nonmaskable`, `machine_check` and `fatal` entries are not blocked by the ordinary interrupt mask; their delivery
  is exactly what the manual specifies, including its blocking rules (x86-64 blocks further NMIs until the NMI
  handler's return; a machine check during a machine check shuts the processor down), which the model states as
  named terminal outcomes. The checker allows only lock-free code there (no lock, no wait, no allocation), on a
  declared own stack. A platform that lacks an event kind refuses an entry declared for it; a portable kernel
  declares such an entry under compile-time selection (§4.10).

### 4.5 Cores, per-core data, threads

- `per core` storage: the compiler keeps the per-core base in the target's register (x86 GS base with generated
  `swapgs` in entry frames, `tpidr_el1`, `tp`/`sscratch`); `core.id()` reads the identity.
- `start core k at f(args) stack t else failed;` starts a parked core in the kernel state at code item `f`. On
  every target the core arrives in a platform arrival state and runs **arrival code that is Gabbro source** in
  that state, ending in `jump long f(args) into kernel with s stack t`; the compiler generates an arrival frame (the
  arguments, the stack, the space and the per-core base, published by the starting core before the start and
  acknowledged by the new core). x86-64: INIT–SIPI through the local interrupt controller, arrival in 16-bit real
  mode at a page below 1 MiB. AArch64: PSCI `CPU_ON` with a physical entry point and a context identifier,
  arrival with translation off. RISC-V: SBI HSM `hart_start` with `satp = 0`, only `a0` (hart id) and `a1` (opaque)
  defined and no stack. A failed start (an error answer, or no acknowledgement within the declared bound) takes
  the `else` channel and the stack and arguments stay with the caller; ownership of `t` and of the arguments moves
  to the new core at its acknowledgement. The kernel's statement is the same on all three.
- Thread switch (`switch to t`) saves and restores the full extended state as part of the generated frame, with the
  layout from `cpu.caps` and the enabled component set (x86 XSAVE/XRSTOR over the enumerated components, AArch64
  FP/SIMD and SVE with its vector length, RISC-V F/D/V with `vlenb`). A thread migrates only to cores with a
  compatible component set; lazy schemes are compiler optimisations under the same theorem.

### 4.6 Devices (L2)

```gabbro
// platform unit: addresses and registers
device com1 at port 0x3F8 registers { thr: u8 @0 w, lsr: u8 @5 r { thr_empty: bit 5 } }          // 16550, x86 PC
device uart0 at 0x0900_0000 registers { dr: u32 @0x00 w, fr: u32 @0x18 r { tx_full: bit 5 } }   // PL011, virt
// drivers (one per DEVICE, the same source on every architecture), chosen by compile-time selection:
fn ns16550::put(d: com1, b: u8) else timeout { while !d.lsr.thr_empty bounded 1_000_000 ops on_exceeded timeout { } d.thr.write(b); }
fn pl011::put(d: uart0, b: u8) else timeout { while d.fr.tx_full bounded 1_000_000 ops on_exceeded timeout { } d.dr.write(b as u32); }
// kernel (identical): the common interface
console.put(byte) else timeout;
```

- Registers and addresses do not normalise device protocols: the 16550 signals "room" with a set bit, the PL011
  with a clear `TXFF`. The kernel proper calls a common driver interface; the drivers live beside the platform unit.
- MMIO and I/O ports are one syntax; the compiler emits `in`/`out` or ordered device loads/stores with the barriers
  the device class requires. Device authority is a linear value handed out once by the platform unit at start.
- Buffers lent to a device (`lend r to d` / `take back r`) get the generated cache maintenance of the device's
  declared coherence (none on coherent x86 DMA; clean/invalidate by range on non-coherent AArch64/RISC-V devices).
- **Memory shared with a running device** (descriptor rings, completion queues) is not lent: the device may write
  it at any time. It is read only through `copy from shared (ring, slot) into r` with the same rule as guest memory
  (B23 T2): each slot at most once per handling, validation and use on the private copy. Writing the kernel's own
  entries uses `copy to shared`. On a platform with an IOMMU a device's DMA (bus mastering) can be enabled only
  after its isolation group is attached (§4.12).
- That a driver follows its device's protocol is program logic (GabbroProve); the device's answers are its
  declared contract (hardware, named in (c)).

**Devices found at run time (O26).** Most devices are not at a fixed address: PCIe BARs, devicetree and ACPI nodes,
hot-plugged functions. Their window comes from a discovery answer, and that answer being true is a hardware or
environment assumption either way — the compiler does not care where the number came from.

```gabbro
layout nvme_regs { cap: u64 @0x00 r, cc: u32 @0x14 rw, csts: u32 @0x1C r { rdy: bit 0 }, … }
let bar = pci.config(fn).bar(0) else absent;                 // a discovery answer: an address and a size
let nvme = device at bar as nvme_regs else overlaps;          // a device value from that answer
```

- `device at w as L` builds a device value from a window `w` that is a **discovery answer** (a PCI configuration
  read, an ACPI or devicetree node from the handoff regions, a bus enumeration) with the register layout `L`.
  The provenance is checked: the window must come from such an answer, not from arithmetic on arbitrary numbers.
  That the answer is true (the device decodes exactly that window, with that layout) is part of the device
  contracts (named in (c)); for windows from firmware tables it is part of the firmware handoff.
- The checker and the generated code keep memory safety independent of that assumption: the window is checked at
  run time against the ledger, and one that overlaps RAM, the image or another live device value takes the `else`
  channel (`overlaps`). A wrong answer can therefore make a driver talk to the wrong device, never corrupt
  memory the program owns.
- Assigning BARs (writing the window into the configuration space inside a bridge window the kernel owns) is
  driver logic over the same construct; the bridge window itself is a device region of the platform unit or of
  the firmware handoff. AML `OperationRegion`s use the same construct.

**Wide and enqueued device stores (O26).**

```gabbro
layout dsa_portal { submit: [u8; 64] @0x0 w store64 }        // one 64-byte store, never torn
dsa.portal.submit.write(descriptor) else unsupported;        // MOVDIR64B / ST64B
let r = dsa.portal.submit.enqueue(descriptor) else unsupported;   // ENQCMD / ST64BV0: accepted or retry
let v = gpu.ring.head.read128() else unsupported;            // 16-byte single-copy access
```

- A register field may declare an access shape: `store64` (one 64-byte store), `enqueue64` (a 64-byte store whose
  device answers accepted or retry), `atomic128` (a 16-byte single-copy read or write), and exact widths 8–64 as
  today. The compiler lowers them to `MOVDIR64B`, `ENQCMD`/`ENQCMDS`, AArch64 `ST64B`/`ST64BV`/`ST64BV0`, and to
  16-byte accesses only where the manual gives single-copy atomicity for that width and memory kind.
- Whether a core has the instruction is decided by `cpu.caps` at run time; without it the operation takes its
  `else` channel (`unsupported`), never a torn fallback. A target that never has it refuses the shape unless the
  driver selects another path through compile-time selection (§4.10).

### 4.7 Guests and system calls (L8)

- `enter guest g` leaves to user privilege with the guest's saved frame (generated `iretq`/`sysretq`, `eret`,
  `sret`); `entry syscall (args) { … }` is the generated system-call entry.
- Guest memory is reached only through `copy from guest (a, n) into r else fault(k)` and `copy to guest … else
  fault(k)`. **No TOCTOU over guest memory (B23 T2):** each syscall argument and each guest range handed to an
  entry is an affine read capability — every guest byte can be copied at most once per entry invocation, a second
  copy of overlapping bytes is refused by the checker, and validation and use operate only on the private copy in
  kernel memory. A torn structure (other guest threads changing bytes during the copy) is then harmless: the
  kernel validates exactly what it uses. A fault returns through the `else` channel with the number `k` of bytes
  copied; the first `k` destination bytes are initialised, the rest are not. The user-access guard is opened only
  inside the copy (x86 `stac`/`clac`, AArch64 PAN, RISC-V `SUM`); the fault-recovery table is generated.
- The isolation theorem of L8 protects every retained carrier against everything the guest may do; no guest
  contract, cost or termination is claimed for an unverified guest.

### 4.8 Environment interfaces (firmware services)

```gabbro
// platform unit
environment uefi abi uefi_x64 {
    fn get_memory_map(buf: region<normal, rw>) -> memory_map or uefi_error requires … ensures …;
    fn exit_boot_services(key: map_key) consumes uefi or uefi_error;
}
code efi_main(fw: uefi, image: image_handle) in platform.uefi_arrival { … }
```

- An environment interface lists services with contracts; their software runs outside the verified image (named
  environment assumption in the conditional form of A1: the caller proves `pre`, `pre → post` is named in (c)).
- A service value comes only from an arrival contract (the UEFI system table at entry, the PSCI/SBI conduit of the
  platform); it is never built from an address. The compiler generates the foreign calling convention (`abi`).
- A service value is linear where the firmware ends it: `exit_boot_services` consumes `uefi`, after which no boot
  service can be called and the boot-services memory becomes ordinary RAM regions of the kernel.
- The 16-bit loader boundary needs the BIOS services from the start (a boot sector has 510 bytes and must load the
  rest): `environment bios abi bios_int { fn read_sectors(…); fn memory_map(…); fn enable_a20(); }`, lowered to
  software interrupts in state `real16`. The service value is alive only in real mode and is consumed by the
  `jump long` that leaves it; enabling A20 without the service is device logic (port `0x92`) in the platform unit.
- **Resident firmware** — firmware that keeps running after the handoff (SMM handlers under UEFI or BIOS, UEFI
  runtime services, EL3 secure firmware, RISC-V M-mode firmware) — is not covered by a per-call contract: it can
  run asynchronously between calls. Each platform declares it with a rely contract (`resident firmware smm
  touches reserved(smram) …`): which entries are asynchronous, the memory it may touch (its reserved regions
  only) and the time it may take; this is the environment assumption "resident firmware" of the Spec list. An
  image that provides that firmware itself (§4.17) proves it instead.

### 4.9 Images, placement and code from data

```gabbro
image pc_uefi format uefi { entry efi_main }
image pc_bios format boot_sector { entry boot16 at 0x7C00 }       // 16-bit loader boundary
image virt_flash format flash { entry reset_entry at platform.reset_vector }
place platform.core_arrival below 0x10_0000 aligned 4096;
```

- The compiler writes the image format and its headers (PE/COFF for UEFI, a boot sector, a flash image with the
  reset vector, ELF later); `LayoutOk` and the loader statement are proved from the declaration (K1). A format
  with a size limit refuses an item that does not fit (a boot sector beyond 510 bytes plus signature); a 16-bit
  boot is therefore two items: the sector loads the second stage through `bios.read_sectors` and jumps to it.
- `make executable r as code_item on cores K` turns a written region into code authority. Preconditions: the bytes
  equal the item the compiler emitted for this image, with its relocations applied as declared (byte and provenance
  correspondence, checked against the image's own record); every writable alias of `r`, by a CPU mapping or a DMA
  space, is revoked first. The generated publication: the region becomes read-only and executable in every space
  that maps it, with the permission change flushed like §4.3; AArch64 cleans the data cache to the point of
  unification (`dc cvau`), invalidates the instruction cache (`ic ivau`), `dsb ish`, and every core of `K` executes
  `isb` before it runs the item; RISC-V executes `fence.i` on every hart of `K` (remote harts through IPI or the SBI
  remote fence); x86-64 executes a serialising instruction on every core of `K` that may hold stale instructions
  of the reused memory. There is no other way to code (O25: JIT and modules get no syntax).

### 4.10 Compile-time selection: `if (…) then { … } else { … }` (O24)

```gabbro
// main unit: flags with types and defaults; configurations the checker must accept
flag smp: bool = true;
flag trace: bool = false;
configurations { pc_uefi: target x86_64, platform pc, image pc_uefi;
                 pc_bios: target x86_64, platform pc, image pc_bios;
                 arm_virt: target aarch64, platform virt; rv_virt: target riscv64, platform virt, smp = false; }

if (smp) then { start core 1 at core_main() stack s1; }
if (target.arch == x86_64) then { use driver::i8042; } else { use driver::pl050; }
let n = if (trace) then { 4096 } else { 0 };
```

- **Form.** `if ( flagcond ) then { … } [ else { … } ]`, at item level (declarations, `use`, devices, entries),
  statement level and expression level (both branches of one type). `else if (…) then` chains. The parentheses
  and `then` mark the compile-time form; the run-time `if c { … }` never takes `then`.
- **Conditions are flags only.** Atoms are declared flags (`bool` or a closed enum) and the built-in flags
  `target.arch`, `target.width`, `target.page_size`, `platform`, `image` and the profile entries; operators `!`,
  `&&`, `||`, `==`, `!=`. A run-time value, a function call or an undeclared flag in the condition is refused, and a
  flag inside a run-time `if` is refused with the hint to use the compile-time form, so the two never mix.
- **Values**, highest precedence first: `--flag name=value` on the command line, then the selected configuration,
  then the flag's default; a flag without a value is refused. There is no implicit environment variable and no flag
  that a library sets for its user.
- **Meaning.** Per configuration, the elaborator turns the unit into an ordinary unit without flags: unselected
  branches are dropped before name resolution, so an x86-only declaration in an x86 branch never has to resolve in
  an AArch64 configuration. Machine G and the goal theorem see only that unit; the theorem holds per configuration.
  Lean: selection as a total function on parsed units with the lemma that it commutes with elaboration of the
  remaining forms, and `ct_select_erfuellbar`.
- **Checking.** Every branch is PARSED. Each branch is resolved and checked in every declared configuration that
  selects it; `gabbro check` checks the unit under EVERY declared configuration (not under all flag combinations,
  which is exponential), and a branch that no declared configuration selects is refused as dead. A build checks
  the configuration it actually builds, including `--flag` overrides: a build outside the declared set is checked
  in full before it is compiled, so no unchecked configuration is ever compiled.
- **Neutrality.** The language allows a `target.arch` condition anywhere; K6's measure counts it: the kernel proper
  carries feature flags (`smp`, `trace`) only, and architecture conditions live in the platform unit and the driver
  selection.

### 4.11 Hardware virtualisation (L15, O25)

```gabbro
state hyp { width 64, privilege hypervisor, translation on }           // VMX root / SVM host, EL2, HS-mode

let gpa  = space.new_guest(tables);                                    // stage 2: EPT/NPT, ARM stage 2, RISC-V G-stage
map(gpa, 0x0, guest_ram, rights { read, write, execute }, kind normal) else full;
let v    = vm.new(gpa, intercept { ports 0x0 .. 0x1_0000, system_registers all, halt, hypercall })
           else unsupported;
let c    = v.vcpu(0, entry_pc = 0xFFF0, width 16);                      // the guest may start at its own reset
loop {
    match enter vm v vcpu c {
        memory_fault(addr, access) => emulate_mmio(v, c, addr, access),
        io(port, size, dir)        => emulate_port(v, c, port, size, dir),
        system_register(r, dir)    => emulate_sysreg(v, c, r, dir),
        hypercall(args)            => hypercall(v, c, args),
        external_interrupt         => { },                                // the host's own entry already ran
        halt                       => wait for interrupt,
        shutdown                   => break,
    }
}
inject interrupt 32 into vm v vcpu c;
copy from vm v (guest_addr, n) into buf else fault;                    // through stage 2, single fetch
```

- `state … privilege hypervisor` is the host state (x86-64 VMX root or SVM host in ring 0, AArch64 EL2 with or
  without VHE, RISC-V HS-mode). Enabling the unit (VMXON with its region, EFER.SVME, HCR_EL2, `hstatus`) is
  generated at the first `vm.new`; a target or core without the unit fails into the `else` channel.
- A guest-physical space is a `space` like §4.3: `map`, `unmap`, `flush(token)`, `protect`, with the same
  revocation token, generation, shootdown and quiescence rules. The generated invalidation is the complete
  protocol of each backend, applied on every core that may run a vCPU of the VM: Intel `INVEPT` (single-context);
  AMD flushing the guest's ASID through the VMCB TLB control on the next VMRUN (or assigning a fresh ASID) — not
  `INVLPGA`, which addresses guest-virtual pages; AArch64 `tlbi ipas2e1is` followed by `tlbi vmalle1is` for the
  VMID, because IPA invalidation alone need not remove combined stage-1/stage-2 entries; RISC-V `hfence.gvma` on
  every relevant hart. VMID/ASID reuse and vCPU migration to another core go through the same protocol. Memory
  kinds and execute rights apply.
- `vm.new(space, intercept { … })` builds the control structure (VMCS, VMCB, EL2 trap configuration, `hedeleg`/
  `hideleg`/`henvcfg`); its format is compiler knowledge like page tables. **Mandatory isolation controls are not
  part of the intercept set**: every access to state that the host owns or that would bypass stage-2 translation
  (translation and virtualisation controls, the host's interrupt controller, physical memory outside the space,
  ports and registers not granted) always exits or is architecturally confined; the intercept set only adds
  optional exits the hypervisor wants to see. A configuration on which the unit cannot enforce the mandatory set
  is refused by `vm.new`. `v.vcpu(i, …)` gives a vCPU whose
  register file is a value: the neutral part (pc, sp, flags, width, privilege) plus the target's registers by name
  (the register exception of O23).
- `enter vm v vcpu c` runs the guest until an exit and returns a neutral `vm_exit` value; the compiler generates
  entry and exit (VMLAUNCH/VMRESUME, VMRUN, `eret` to EL1 under HCR, `sret` with `hstatus.SPV`) with the saved host
  state, extended state and per-core base. On x86-64 both VMX (Intel) and SVM (AMD) are lowered; which one runs is
  chosen once at `vm.new` from the feature set, so one image runs on both (vendor neutrality, AGENTS.md §4).
- `inject interrupt` and the virtual interrupt controller (posted interrupts/APICv/AVIC, vGIC with list registers,
  AIA guest interrupt files) are constructs; exits for interrupt windows are part of `vm_exit`.
- The hypervisor reaches guest memory only through `copy from vm`/`copy to vm` (stage-2 translation, single fetch,
  fault channel). A device is handed to a VM only through its IOMMU space (§4.12): `assign device d to vm v`.
- Nested virtualisation: a vCPU created with `privilege hypervisor` runs a guest hypervisor (VMCS shadowing, AMD
  nested, ARM NV2, RISC-V nested H) after the single-level case is complete; until then it is refused by name.
- Isolation theorem (extends L8), with an explicit frame: whatever an unverified guest does, it changes only its
  vCPU values, the regions mapped into its guest-physical space with the granted rights, the devices assigned to it
  (within their IOMMU space), and the generated control state the model lists as guest-changeable (accessed and
  dirty bits of its stage-2 entries, its virtual interrupt state, exit information); every exit returns to the
  declared host code; every other program carrier of the host stays intact. No guest correctness, cost or
  termination is claimed. The unit itself is the named hardware assumption `VirtUnit` (entry, exit, mandatory
  controls, requested intercepts and stage-2 translation as the architecture manual says).

### 4.12 IOMMU: device address spaces (L16, O25)

```gabbro
let io  = platform.iommu(0);                                          // VT-d, AMD-Vi, SMMUv3 or RISC-V IOMMU
let grp = io.group_of(nic) else not_isolated;                          // the isolation group, from discovery
let ds  = io.space.new(tables);
attach group grp to ds ats off;                                        // every requester id / stream id of the group
map(ds, 0x1000_0000, rx_ring, rights { read, write }, kind normal) else full;
lend rx_ring to nic;
…
take back rx_ring from nic else stuck;                                 // revoke, invalidate, drain; then the region
entry dma_fault (f: dma_fault_info) { … }
```

- **The configuration is logic, the unit is the hardware:** which group is attached to which space and which regions are mapped there is the image's program logic (b) under the language's checks (only owned regions can be mapped, every lent region is mapped, DMA is enabled only after attachment); the assumption `Iommu` covers only what the hardware does with that configuration.
- **The unit of attachment is an isolation group**, never a single device: all functions and devices that share a
  requester identity, sit behind a bridge without access control, or can reach each other peer-to-peer without
  passing the IOMMU. Discovery (DMAR, IVRS, IORT, devicetree, and the PCIe access-control capabilities) yields the
  groups; a device whose group cannot be established is `not_isolated`. Attaching a group consumes it: its
  requester and PASID identities are owned by one space. Before attachment every new device starts in a blocking
  domain (DMA refused), so there is no window of untranslated DMA.
- **ATS** (device-side translation caches) is off by default; `ats on` is allowed only for a group whose endpoint
  is declared trusted in the platform unit (its ATS behaviour then becomes part of the `Iommu` envelope).
  Page-request (PRI) answers carry the mapping generation, so a request of a revoked generation is answered with
  failure and never resurrects a mapping.
- A DMA space is a `space` whose users are a group: `map`/`unmap`/`protect`/`flush(token)`. The invalidation waits
  for completion (VT-d invalidation queue with a wait descriptor, AMD-Vi completion wait, SMMU `CMD_TLBI_*` +
  `CMD_SYNC`, RISC-V IOMMU `IOTINVAL` + `IOFENCE.C` with `PR`/`PW` set), device-side caches included where ATS is on.
- `take back r from d else stuck` is the full protocol: the device's driver stops it from issuing new requests for
  `r` (program logic, proved), the mapping is revoked and made visible, the IOMMU and device-side caches are
  invalidated with completion, in-flight requests are drained (the completion ordering of the IOMMU plus the
  interconnect fence the platform declares), and only then is `r` returned. On a timeout or an error `r` stays
  revoked and is NOT returned (`stuck`): no memory is reused while a DMA may still reach it.
- The table and queue formats are compiler knowledge; the platform unit names the IOMMU kind, its registers and
  addresses; discovery chooses at run time between the lowerings of one target (VT-d or AMD-Vi on x86-64).
- Theorem: a request of an attached group reads or writes memory only inside the regions mapped in its space with
  their rights, for every DMA path covered by the `Iommu` envelope (IOMMU, interconnect and endpoints of the group).
  For those requests the DMA part of the device contract (today `ImBereichO`) is PROVED; devices not covered keep it
  as a declared assumption. A DMA-capable device reaches an untrusted guest or VM only behind an attached group;
  otherwise the assignment is refused.

### 4.13 Suspend and resume (L4)

- `suspend system resume at f(args) else failed;` is a system protocol, not a local statement: it first quiesces
  every other core (parked through the same mechanism as `stop core`) and every DMA (`take back` of every lent
  region or a declared device stop), requires that every live device value is held by the suspending code, then
  enters the sleep state; RAM keeps its contents. Execution resumes in the platform's resume arrival at code item
  `f`: x86-64 the ACPI waking vector in real mode, or the negotiated 64-bit waking vector where the firmware offers
  it (a profile choice); AArch64 the PSCI `SYSTEM_SUSPEND` arrival with translation off; RISC-V the SBI `SUSP`
  arrival. `suspend core resume at f` is the per-core deep idle state with the same rules for that core.
- A global resume generation advances. Regions and the ownership ledger survive. Each device declares in the
  platform unit whether its state is retained, lost or unknown across suspend; a device value of a lost or unknown
  device is in the `reset` typestate after resume and its driver must reinitialise it before use (checked). Since
  all device values are held by the suspending code, no other thread can hold a stale one. Generated state (vector
  tables, per-core base, translation) is re-established by the generated resume path before `f` runs.
- The resume arrival state is established by firmware, so it is part of the firmware service contract (an
  environment assumption), not of `ResetState`; the sleep request itself is a device (ACPI PM1 control) or an
  environment call (PSCI, SBI).

### 4.14 Debug and performance units (L7)

```gabbro
watch(addr, 8, on write) else no_slot;                                  // DR0–3/DR7, DBGWVR/WCR, Sdtrig
entry watchpoint (w: watch_info) { … }
entry breakpoint (b: break_info) { … }                                 // from a declared code point
step thread t;                                                         // single step: TF, MDSCR.SS, Sdtrig icount
let k = counter.start(event cycles) else no_counter;                   // cycles, instructions, cache_misses, branch_misses
entry perf_overflow (o: overflow_info) { … }
```

- Watchpoints, breakpoints on named code points, single step of a thread, a guest or a vCPU, and performance
  counters are constructs. Neutral events cover the common set; raw events are platform registers by number.
- Counters and watch slots belong to a thread or a core as declared; generated frames save and restore them.
- Their trap entries are delivered as `IrqDelivery` states (non-maskable when the architecture says so).

### 4.15 Backtraces (L5)

- `backtrace(into buf) -> n` fills `buf` with the code items and offsets of the current frames. The compiler emits
  frame descriptors as data and a generated walker; the walker reads only the current stack region and is proved
  to terminate on it. It is allowed in every entry kind, `fatal` included. Gabbro has no exceptions, so there is no
  unwinding; a panic is a `fatal` path that may print the backtrace and stop.

### 4.16 Rights granted to guests (L8)

- `grant ports p .. q to guest g` (generated I/O permission bitmap on x86-64; refused by name on targets without
  ports), `grant device d to guest g` (its window mapped with kind `device`; a DMA-capable device only together
  with an IOMMU attachment to the guest's space), `grant cycles to guest g` and `grant register r to guest g read`
  for registers the architecture allows user access to (counter, timer and feature registers).
- For VMs the optional intercept set of §4.11 decides which granted registers and ports are passed through; the
  mandatory isolation controls of §4.11 can never be passed through.

### 4.17 Secure worlds and the monitor (L17, O25)

```gabbro
state monitor { width 64, privilege machine, translation off }          // EL3, RISC-V M-mode
entry monitor_call (call: monitor_args) in monitor { … }                // SMC, ecall from S
return to world normal at kernel_entry(args);                           // first entry into the normal world
resume world normal with call.saved;                                    // return to the caller's saved context
provide environment psci abi smc64 { fn cpu_on(…) requires … ensures …; … }   // firmware written in Gabbro
protect physical secure_ram for world secure;                           // PMP/ePMP, TZASC device, SMRAM lock
```

- `privilege machine` with a `world` attribute (`secure`, `normal`; Realm later) models EL3 with TrustZone and
  RISC-V M-mode. `return to world w at f(args)` is the generated FIRST entry into a world (ERET with `SCR_EL3.NS`,
  `mret` with PMP reconfiguration); `resume world w with saved` returns from a monitor call into the caller's saved
  context, after a checked transformation of that context (return values, advanced pc), never to an arbitrary code
  item.
- **x86 SMM is a state of its own**, `platform.smm_arrival`: an SMI enters it with 16-bit default operand size and
  the state saved in the SMRAM save area; the generated SMI entry may `jump long` to a 64-bit monitor state, and
  the only way out is `resume world normal with saved` (lowered to `RSM`), which restores the saved context after
  the same checked transformation.
- `protect physical r for world w` partitions physical memory. PMP protects only accesses of the hart (M versus
  S/U); DMA masters need the IOMMU of §4.12 or an IOPMP/TZASC/WorldGuard controller of the platform, programmed by
  its driver with a proved configuration. Isolation between several secure domains beyond M versus S/U needs such a
  controller too; PMP alone is refused for it.
- `provide environment E` is the other side of §4.8: a firmware written in Gabbro implements PSCI, SBI or a UEFI
  subset, and as software inside the image it proves `pre → post` of every service (A1). The boundary moves back:
  a kernel booted by such a firmware has no environment assumption for those services left.
- SMM handlers need the reset boundary (SMBASE relocation and SMRAM locking happen in firmware), so they are
  written on platforms whose reset path the image owns; the emulator platform comes first.
- Named hardware assumption `SecureUnit`: a PLATFORM envelope (processors, memory controllers, interconnect, DMA
  masters) that enforces the configured world partition and enters the monitor only through its declared entry;
  the configuration of the platform controllers is the image driver's proved work, not part of the assumption.

### 4.18 Hard timing: bit-banging and timed device protocols (L18, O26)

```gabbro
timed core within 5 us else late {                  // this core: interrupts and preemption off for the block
    pin.data.write(1);
    wait at least 1_200 ns;                         // lower bound from the clock
    pin.data.write(0);
    wait until t0 + 2_500 ns;                       // absolute point on the per-core clock
    let ack = pin.input.read();
}
```

- `wait at least d` and `wait until t` give LOWER bounds: they read the cycle counter or the per-core timer and
  spin or idle until the point has passed. Their guarantee rests on the named hardware assumption `ClockRate`
  (the counter's frequency and monotonicity as the platform declares and `cpu.caps` reports).
- `timed core within d else late { … }` gives an UPPER bound: the block runs with the core's ordinary interrupts
  masked and without preemption, contains no lock wait, allocation or unbounded loop, and the compiler proves
  from the emitted code that it takes at most `d` under the named hardware assumption `RowTiming` (per target
  row: an upper bound of cycles in the declared state; per memory kind and per device register: an upper bound
  of access latency, declared in the platform unit and measured by M). Events the mask cannot stop — an NMI, a
  machine check, a resident-firmware SMI within its declared time — are counted in the bound where the platform
  declares their worst case, and otherwise detected: the generated code reads the clock at the end of the block
  and takes the `else late` channel when `d` was exceeded, so no contract and no memory guarantee depends on
  the timing assumption; only the promise "on time" does.
- A timed block that the compiler cannot bound (an unbounded loop, a call without a cost bound, a device without
  a declared latency) is refused. Bounds are per configuration; a different target or core type needs its own
  rows and is checked by compile-time selection like everything else.
- This lifts the earlier exclusion of hardware time bounds for exactly these blocks (O26): `ClockRate` and
  `RowTiming` are named per platform and per row, and everything outside a timed block keeps counting G steps
  only (`ZeitAb`), with no time claim.

### 4.19 Inventory: the constructs and their rows

The count that the estimate of PLAN-COMPILER-READY §7 uses (92 constructs; each gets a G rule, an `Akzeptiert`
rule, a parser/exporter form, an `_erfuellbar` lemma, and on the compiler side a GIR cell with its lowering theorem):

| Row | Constructs | Count |
|---|---|---|
| L1 | `split_at`, `split_pages`, `merge`, `view as`, `address()` | 5 |
| L2 | device declaration, `device at w as L` from a discovery answer, wide and enqueued stores (`store64`, `enqueue64`, `atomic128`), `lend`, `take back`, `copy from/to shared`, device coherence and suspend-state declaration | 7 |
| L4 | `state`, `code … in`, `jump`, `jump long`, `wait for interrupt`, `stop core`, `cpu.caps`/`cpu.has`, `cpu.cycles`, `suspend system`, `suspend core`, resume arrival | 11 |
| L5 | interrupt, exception, thread-switch and first-entry frames, `per core`, `core.id`, `switch to`, `backtrace` | 8 |
| L6 | `space.new`, `map` with kinds, `unmap` (token), `protect`, `flush(token)`, `activate` | 6 |
| L7 | `nonmaskable`, `machine_check`, `fatal` entries, `interrupts off`, `priority at least`, `send interrupt`, `route line`, `timer.at`/`after`, `watch`, watch/break entries, `step`, `counter.start`, `perf_overflow` entry | 13 |
| L8 | `enter guest`, `entry syscall`, `copy from guest`, `copy to guest`, `grant ports`, `grant device`, `grant cycles`, `grant register` | 8 |
| L9 | `start core` with its arrival frame | 1 |
| L12 | environment declaration, service call, consuming service, resident firmware declaration | 4 |
| L13 | `image`, `place`, `make executable` | 3 |
| L14 | `flag`, `configurations`, `if … then` at item/statement level, at expression level | 4 |
| L15 | `space.new_guest`, `vm.new` with mandatory controls and intercepts, `vcpu`, `enter vm`, `vm_exit`, `inject interrupt`, `copy from/to vm`, `assign device`, nested vCPU | 9 |
| L16 | `io.space.new`, `group_of`, `attach group` (PASID, ATS policy), `dma_fault` entry | 4 |
| L17 | monitor state with worlds, `monitor_call` entry, `return to world`, `resume world`, `protect physical`, `provide environment` | 6 |
| L18 | `wait at least`, `wait until`, `timed core within … else late` | 3 |
| **sum** | | **92** |

## 5. Typing, acceptance and the trust boundary

- The checker tracks the execution state, held regions, device values, environment services and mask/priority
  facts at every code point (a typestate). It refuses: a construct in a state that lacks it, a jump into another
  state without `jump long`, a `jump long` whose target code or stack is not mapped in the target space, a region
  used after it was moved, a lock or wait in a nonmaskable entry, a guest access outside §4.7, a service used after
  it was consumed, a device through a RAM view, an unmapped or unflushed reuse, a device lent or assigned without
  its IOMMU mapping where the platform has an IOMMU, a DMA-capable device granted to an untrusted guest or VM
  without an attached isolation group, a device value used after resume before reinitialisation, a world switch
  with memory not partitioned, a declared register that a construct manages, a memory kind the region or target
  cannot realise, an entry kind the platform lacks, a device window that is not a discovery answer, a store shape the target never has (outside compile-time selection), CPU code that the compiler did not emit (option ROMs, binary drivers) at any privilege of the image, a timed block whose bound is not proved, a second copy of guest or shared-device bytes within one invocation, a fact about shared state used after a release point without re-establishing it (B23), DMA enabling before the group is attached, unsupported targets by name.
- Every construct and generated frame accounts for all architectural effects: register and flag state, hidden stack
  traffic, privilege, translation, masks, faults and their exits, interleavings and the atomic rely. A generated
  construct is not implicitly atomic; masking is not a multicore lock.
- Trusted base: Lean's kernel and `propext`, `Classical.choice`, `Quot.sound`. Below the model: `Hardware T` (every
  row computes its cell — now including the 16- and 32-bit rows and the privileged rows), the hardware frame,
  `Mmu`, `IrqDelivery` (non-maskable, debug and performance events as the manual specifies, blocking rules and
  terminal outcomes included), `VirtUnit`, `Iommu` (an envelope of IOMMU, interconnect and endpoints), `SecureUnit`
  (a platform envelope), `ResetState` (per processor: the state at the reset vector and at the arrival of a further
  core), device contracts (including the truth of discovery answers; their DMA part only for requests outside the `Iommu` envelope), the memory-model reading.
  Environment: `FirmwareHandoff` (UEFI), `BiosHandoff` (16-bit loader), the firmware services of §4.8 including
  the resume arrivals they establish, resident firmware with its rely contract. For timed blocks only: `ClockRate` and `RowTiming` (§4.18). Everything else — boot, allocators,
  page-table code, schedulers, drivers, hypervisors, monitors and provided firmware services — is software inside
  the image and the user's logic (b).

## 6. The platform unit

A platform unit contains data and the arrival code of its arrival states, and it is the only per-target source; the drivers of
the devices a platform has are chosen by compile-time selection (§4.10), and a driver for the same device is the
same source on every architecture:

| Kind | x86-64 PC | AArch64 virt/board | RISC-V 64 virt/board |
|---|---|---|---|
| registers | MSRs by number (PAT, …), device registers | system registers by name, device registers | CSRs by number, device registers |
| addresses | device windows, I/O ports, reset vector, the < 1 MiB arrival page, interrupt vector numbers | device windows, interrupt IDs | device windows, interrupt IDs |
| arrival states | reset (16-bit), BIOS loader (16-bit), UEFI (64-bit), further core (16-bit) | reset (EL3/EL2), UEFI (EL2/EL1), PSCI core start | reset (M), SBI (S), SBI hart start |
| environment interfaces | UEFI, BIOS | UEFI, PSCI | SBI, UEFI |
| arrival code (Gabbro) | 16-bit further-core arrival (and resume from the real-mode waking vector) ending in `jump long` | PSCI arrival with translation off, from the context identifier to `jump long` | SBI arrival with `satp = 0`, from `a0`/`a1` to `jump long` |
| interrupt controller, timer | local APIC + I/O APIC, TSC deadline | GICv3, generic timer | AIA or PLIC, Sstc or SBI timer |
| page size, discovery | 4 KiB; ACPI | 4/16/64 KiB granule; devicetree or ACPI | 4 KiB; devicetree |
| virtualisation, IOMMU | VMX and SVM; VT-d and AMD-Vi | EL2 (VHE); SMMUv3 | H extension; RISC-V IOMMU |
| secure world, monitor | SMM as its own arrival state, SMRAM locking | EL3, TrustZone (TZASC a device) | M-mode, PMP/ePMP, IOPMP or WorldGuard for DMA |
| resident firmware | SMM, UEFI runtime services | EL3 firmware, UEFI runtime services | M-mode SBI firmware |
| driver selection | `if (platform == pc) then { use … }` (§4.10) | same form | same form |

The arrival code is ordinary Gabbro in a declared state; it uses only the constructs of §4. The kernel proper
does not change between targets; K6 measures that its diff between the three targets is zero lines. Drivers are
per device (the same 16550 driver on every architecture), selected per platform behind common driver interfaces;
they are not part of that measure, and neither is the choice of the discovery parser (ACPI or devicetree).

## 7. Implementation and validation order

1. Model first (PLAN-COMPILER-READY L0–L17): the neutral state of §3 and one G rule per construct, typestate
   acceptance in `Akzeptiert`, generic preservation and an `_erfuellbar` lemma per construct (AGENTS.md §3).
   `gabbro_ziel` stays on the standard axioms; the new assumptions (`ResetState`, `BiosHandoff`, `VirtUnit`,
   `Iommu`, `SecureUnit`, the firmware services, resident firmware, non-maskable delivery) are the closed LOW-LEVEL
   ASSUMPTION LIST of the `Spec.lean` header (owner, 2026-11-23); each enters premise (c) with its construct.
2. Connection to G/GX and the no-bypass theorem: no path reaches privileged state except through these constructs.
3. Parser/exporter/checker (L10): the constructs above; refusals by name for everything unmodelled. Assembly bodies, `prim fn`, `raw fn` and
   `entrust` are deleted (2026-11-23), with the reserved-word refusals `N594`–`N597`. The `context<P>` surface
   and target-binding operation functions remain excluded (no legacy). The duty rules of every construct and their
   generic bridge come with GabbroV in Gabbro (C1), complete before the duty proofs of K5 and K8.
4. Compiler (C6, K2, K3): GIR cells and rows per construct, width-16/32 rows on x86-64, generic lowering theorems.
5. Validation (L11): positive — reset to kernel through `jump long`, BIOS and UEFI boundaries, RAM write/read,
   activate/flush, interrupt entry/return, NMI, second core, guest copy, environment exit; negative — forged region,
   wraparound, stale epoch, alias, wrong state, `jump long` to unmapped code, bad stack, lock in NMI, double guest
   fetch, service after exit, missing flush, device through RAM view, undeclared register. Virtualisation: a VM
   booting from its own 16-bit reset with stage 2, every exit kind, interrupt injection, a passed-through device
   behind the IOMMU; negative: guest-physical alias into host memory, device DMA outside its space, unflushed IOTLB
   on take back, untrusted guest with a DMA device and no IOMMU, nested guest before it is modelled. Further:
   suspend/resume with device reinitialisation, a watchpoint, a counter overflow, a backtrace from a fatal entry,
   a port grant, a world switch to a normal-world kernel by a Gabbro PSCI/SBI monitor. Negative from the review:
   NMI or fault in an intermediate state of `jump long` without a handler, reuse of frames before `flush(token)`, a
   core outside the flushed set activating a revoked space, a group with a peer-to-peer path attached as isolated,
   `take back` on timeout returning the region, `make executable` with a remaining writable alias, an intercept
   set that drops a mandatory control, a stale device value after resume, a managed register declared in a
   platform unit, `resume world` to an arbitrary code item, a `--flag` build outside the checked configurations.

Totality claims name their domain: parsing/refusal is total over source input; certified lowering covers the
modelled states, constructs and targets. Unsupported forms refuse; they are never silently erased.

## 8. Coverage and what has no construct (2026-11-23)

Checked against what a general-purpose kernel, a hypervisor and a firmware do. Writable with §4: boot from reset,
BIOS loader or UEFI; memory management, demand paging, copy-on-write; translation with shootdown; interrupts, NMI,
timers, IPIs; SMP start and stop; threads, extended state, async; user processes, system calls, signals; drivers
for MMIO, ports and DMA; PCIe through ECAM or ports; ACPI tables and devicetree as data (an AML interpreter is
program logic); reboot and power-off; hardware virtualisation with stage-2 translation, virtual interrupts and
nested guests (§4.11); IOMMU spaces with PASID and interrupt remapping (§4.12); suspend and resume (§4.13); debug
and performance units (§4.14); backtraces (§4.15); rights granted to guests (§4.16); secure worlds, the monitor
and firmware services provided in Gabbro (§4.17); devices found at run time and wide or enqueued device stores (§4.6); bit-banging and other hard timing with proved lower and upper bounds (§4.18).

Deliberately without a construct:

| Item | Status |
|---|---|
| JIT compilers, loadable kernel modules written in Gabbro | no new syntax (owner, 2026-11-23); CPU code the compiler did not emit is refused (O26). `make executable` stays the only way to code: modules are compiled with the kernel and chosen by compile-time selection, or loaded as items the same compiler emitted for this image. Code generated at run time does not become executable |
| CPU code the compiler did not emit (option ROMs, binary-only drivers) | refused at every privilege of the image (owner O26). A guest or VM runs whatever code it contains anyway (that is what a guest is), so an option ROM can run inside a VM like any guest code, without support or trust from the language |
| DRAM initialisation on real boards | not a language gap (driver logic under the reset boundary); vendor details are not public on most platforms, so the reset gate runs on emulator platforms |
| speculation mitigations, retpolines, fences | compiler work under B17, never a user construct |
