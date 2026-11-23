# Low-level syntax: one neutral language from the reset vector to the kernel

Status: design. Ordered for complete implementation by the owner on 2026-11-03; **redesigned by the owner's
decision O23 of 2026-11-23** (PLAN-COMPILER-READY §8): "context ist auch nur iasm, und GIR soll Compiler- und
Modellsache sein, nicht Nutzersache, deshalb Syntax für alles, auch von 16-Bit-Boot an, also auch schon Long Jump
oder Jump; Ziel: der Kernel kompiliert fast gleich für alle Architekturen, abgesehen von Registern oder Adressen."
The compile-time selection `if (…) then { … } else { … }` (§4.10) is the owner's addition O24 of the same day.

O23 replaces the earlier design of this plan, in which privileged operations were calls of target-binding
functions over a linear `context<P>` (one contracted function per machine operation). Such an interface is inline
assembly with types: the user still picks machine operations one by one and in architecture order, and every
kernel source names its architecture's operation set. It is removed before it is built. The syntax below is not
accepted until its canonical Lean rules exist (AGENTS.md §2: the model comes first). Its implementation targets are
the Lean model, the parser/exporter and the checker (rows L0–L14 of PLAN-COMPILER-READY §3), then the compiler on
GIR (C, K); Stage 0, the runner and GabbroV keep refusing these forms.

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
   system calls — is the same source text on x86-64, AArch64 and RISC-V 64.
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

- `state S { … }` names an execution state: width (16, 32, 64), privilege (`machine`, `hypervisor`, `kernel`,
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
  rule: preconditions (the target code is mapped executable at its address in `s`, the stack is owned and mapped,
  the arguments fit the target state's width, interrupts are masked across the transfer) and one atomic state
  change; the arguments arrive as ordinary parameters. Lowering to user privilege is not a `jump long`: it is
  `enter guest` (§4.7).
- `wait for interrupt;` and `stop core;` (`never`) are statements; `cpu.has(feature)` reads the neutral feature
  set (the compiler lowers it to CPUID, ID registers or `misa`); `cpu.cycles()` reads the cycle counter.

### 4.2 Memory authority without contexts

- `address<S>` is inert data with a space (`physical`, `virtual`, `port`) and the width of the state; arithmetic
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
let frames = unmap(s, virt, n);             // returns the region only after the flush below
flush(s, virt, n) on cores all;             // generated shootdown; quiescence of the range proved
activate s;                                 // installs the root on this core
```

- The table format (x86-64 4/5-level entries, AArch64 descriptors with granule, RISC-V Sv39/48/57) is target
  knowledge in the compiler; the user maps regions, never writes an entry. `map` takes a memory kind
  (`normal`, `device`, `write_combining`, `uncached`), lowered to PAT/MAIR/Svpbmt attributes; a device region can
  only be mapped as `device` or `uncached`. Large pages are chosen by the compiler where extent and alignment
  allow; a kernel never writes a page size as a literal but uses `target.page_size` (4 KiB, or 16/64 KiB granules).
- `flush … on cores K` is the TLB shootdown: the compiler emits the inter-processor interrupt, the generated flush
  handler and the acknowledgement wait (x86 IPI + `invlpg`/`invpcid`, AArch64 broadcast `tlbi … is` + `dsb`,
  RISC-V SBI remote fence or IPI + `sfence.vma`); one generic theorem says that after the statement no core of
  `K` translates the range by the old entries. `unmap` returns the frames only after such a flush.
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
- `nonmaskable`, `machine_check` and `fatal` entries are delivered regardless of the mask: the checker allows only
  lock-free code there (no lock, no wait, no allocation), on a declared own stack; `IrqDelivery` (hardware) states
  their delivery including non-maskability. A platform without NMI maps `nonmaskable` to none and refuses nothing.

### 4.5 Cores, per-core data, threads

- `per core` storage: the compiler keeps the per-core base in the target's register (x86 GS base with generated
  `swapgs` in entry frames, `tpidr_el1`, `tp`/`sscratch`); `core.id()` reads the identity.
- `start core k at f(args) stack t;` starts a parked core in the kernel state at code item `f`. Lowering: x86-64
  INIT–SIPI through the local interrupt controller (platform address), the core arrives in 16-bit real mode at a
  page below 1 MiB and runs the platform's **arrival code, which is Gabbro source** in state `platform.core_arrival`
  ending in `jump long f(args) into kernel with s stack t` (§6); AArch64 PSCI `CPU_ON` and RISC-V SBI HSM
  `hart_start` are environment calls (§4.8). The kernel's statement is the same on all three.
- Thread switch (`switch to t`) saves and restores the full extended state (x86 XSAVE/XRSTOR with the size from
  `cpu.has`, AArch64 FP/SIMD and SVE, RISC-V F/D/V) as part of the generated frame; lazy schemes are compiler
  optimisations under the same theorem.

### 4.6 Devices (L2)

```gabbro
// platform unit: addresses and registers only
device uart at port 0x3F8 registers { data: u8 @0 rw, status: u8 @5 r { ready: bit 5 } }      // x86 PC
device uart at 0x0900_0000 registers { data: u32 @0x00 rw, status: u32 @0x18 r { ready: bit 5 } } // virt board
// kernel (identical):
while !uart.status.ready bounded 1_000_000 ops on_exceeded timeout { }
uart.data.write(byte);
```

- MMIO and I/O ports are one syntax; the compiler emits `in`/`out` or ordered device loads/stores with the barriers
  the device class requires. Device authority is a linear value handed out once by the platform unit at start.
- Buffers lent to a device (`lend r to d` / `take back r`) get the generated cache maintenance of the device's
  declared coherence (none on coherent x86 DMA; clean/invalidate by range on non-coherent AArch64/RISC-V devices).
- That a driver follows its device's protocol is program logic (GabbroProve); the device's answers are its
  declared contract (hardware, named in (c)).

### 4.7 Guests and system calls (L8)

- `enter guest g` leaves to user privilege with the guest's saved frame (generated `iretq`/`sysretq`, `eret`,
  `sret`); `entry syscall (args) { … }` is the generated system-call entry.
- Guest memory is reached only through `copy from guest (a, n) into r else fault` and `copy to guest … else fault`:
  each byte is fetched exactly once into kernel memory (no double fetch, so no TOCTOU over guest memory by
  construction), a fault on a guest address returns through the `else` channel (generated fault-recovery table),
  and the user-access guard is opened only inside the copy (x86 `stac`/`clac`, AArch64 PAN, RISC-V `SUM`).
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
- `make executable r as code_item` turns a written region into code authority: the region becomes read-only and
  executable, the instruction caches are synchronised (generated `ic ivau`/`dsb`/`isb`, `fence.i`, nothing on
  x86), and the code item must be one the compiler emitted (copying the arrival code below 1 MiB when the loader
  placed the image elsewhere); there is no other way to code.

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
- **Values** come from the selected configuration, then from `--flag name=value`, then from the default; a flag
  without a value is refused. There is no implicit environment variable and no flag that a library sets for its
  user.
- **Meaning.** Selection happens before name resolution of the unselected branch's effects and before
  `Akzeptiert`: the elaborator turns a unit and a configuration into an ordinary unit without flags. Machine G and
  the goal theorem see only that unit; the theorem holds per configuration. Lean: selection as a total function
  with the lemma that it commutes with elaboration of the remaining forms, and `ct_select_erfuellbar`.
- **Checking.** Every branch is parsed and name-resolved. `gabbro check` checks the unit under EVERY declared
  configuration (not under all flag combinations, which is exponential); a build compiles one. A branch that no
  declared configuration selects is refused as dead, so nothing rots unchecked.
- **Neutrality.** The language allows a `target.arch` condition anywhere; K6's measure counts it: the kernel proper
  carries feature flags (`smp`, `trace`) only, and architecture conditions live in the platform unit and the driver
  selection.

## 5. Typing, acceptance and the trust boundary

- The checker tracks the execution state, held regions, device values, environment services and mask/priority
  facts at every code point (a typestate). It refuses: a construct in a state that lacks it, a jump into another
  state without `jump long`, a `jump long` whose target code or stack is not mapped in the target space, a region
  used after it was moved, a lock or wait in a nonmaskable entry, a guest access outside §4.7, a service used after
  it was consumed, a device through a RAM view, an unmapped or unflushed reuse, unsupported targets by name.
- Every construct and generated frame accounts for all architectural effects: register and flag state, hidden stack
  traffic, privilege, translation, masks, faults and their exits, interleavings and the atomic rely. A generated
  construct is not implicitly atomic; masking is not a multicore lock.
- Trusted base: Lean's kernel and `propext`, `Classical.choice`, `Quot.sound`. Below the model: `Hardware T` (every
  row computes its cell — now including the 16- and 32-bit rows and the privileged rows), the hardware frame,
  `Mmu`, `IrqDelivery` (with non-maskable delivery), `ResetState` (per platform: the state at the reset vector and
  at the arrival of a further core), device contracts, the memory-model reading. Environment: `FirmwareHandoff`
  (UEFI), `BiosHandoff` (16-bit loader), the environment interfaces of §4.8. Everything else — boot, allocators,
  page-table code, schedulers, drivers — is software inside the image and the user's logic (b).

## 6. The platform unit

A platform unit contains data (and on x86-64 the arrival code) and is the only per-target source; the drivers of
the devices a platform has are chosen by compile-time selection (§4.10), and a driver for the same device is the
same source on every architecture:

| Kind | x86-64 PC | AArch64 virt/board | RISC-V 64 virt/board |
|---|---|---|---|
| registers | MSRs by number (PAT, …), device registers | system registers by name, device registers | CSRs by number, device registers |
| addresses | device windows, I/O ports, reset vector, the < 1 MiB arrival page, interrupt vector numbers | device windows, interrupt IDs | device windows, interrupt IDs |
| arrival states | reset (16-bit), BIOS loader (16-bit), UEFI (64-bit), further core (16-bit) | reset (EL3/EL2), UEFI (EL2/EL1), PSCI core start | reset (M), SBI (S), SBI hart start |
| environment interfaces | UEFI, BIOS | UEFI, PSCI | SBI, UEFI |
| arrival code (Gabbro) | 16-bit further-core arrival ending in `jump long` | none | none |
| interrupt controller, timer | local APIC + I/O APIC, TSC deadline | GICv3, generic timer | AIA or PLIC, Sstc or SBI timer |
| page size, discovery | 4 KiB; ACPI | 4/16/64 KiB granule; devicetree or ACPI | 4 KiB; devicetree |
| driver selection | `if (platform == pc) then { use … }` (§4.10) | same form | same form |

The arrival code is ordinary Gabbro in a declared state; it uses only the constructs of §4. The kernel proper
does not change between targets; K6 measures that its diff between the three targets is zero lines.

## 7. Implementation and validation order

1. Model first (PLAN-COMPILER-READY L0–L14): the neutral state of §3 and one G rule per construct, typestate
   acceptance in `Akzeptiert`, generic preservation and an `_erfuellbar` lemma per construct (AGENTS.md §3).
   `gabbro_ziel` stays on the standard axioms; the new assumptions (`ResetState`, `BiosHandoff`, the environment
   interfaces, non-maskable delivery) are a `Spec.lean` diff shown to the owner before merge.
2. Connection to G/GX and the no-bypass theorem: no path reaches privileged state except through these constructs.
3. Parser/exporter/checker (L10): the constructs above; refusals by name for everything unmodelled. The `asmT`
   string form, `prim fn … = asm { … }`, the `context<P>` surface, target-binding operation functions and software
   `assume` on `entrust` are refused and then removed (no legacy).
4. Compiler (C6, K2, K3): GIR cells and rows per construct, width-16/32 rows on x86-64, generic lowering theorems.
5. Validation (L11): positive — reset to kernel through `jump long`, BIOS and UEFI boundaries, RAM write/read,
   activate/flush, interrupt entry/return, NMI, second core, guest copy, environment exit; negative — forged region,
   wraparound, stale epoch, alias, wrong state, `jump long` to unmapped code, bad stack, lock in NMI, double guest
   fetch, service after exit, missing flush, device through RAM view, undeclared register.

Totality claims name their domain: parsing/refusal is total over source input; certified lowering covers the
modelled states, constructs and targets. Unsupported forms refuse; they are never silently erased.

## 8. What is still not writable (2026-11-23)

Checked against what a general-purpose kernel does. Writable with §4: boot from reset, BIOS loader or UEFI;
memory management, demand paging, copy-on-write; translation with shootdown; interrupts, NMI, timers, IPIs; SMP
start and stop; threads, extended state, async; user processes, system calls, signals (guest frames are values
`enter guest` takes); drivers for MMIO, ports and DMA; PCIe through ECAM or ports; ACPI tables and devicetree as
data from the handoff regions (an AML interpreter is ordinary program logic); reboot and power-off through devices,
PSCI or SBI. Not writable yet, each a construct still to be designed (model first) or deliberately refused:

| Gap | Why it is not writable today | Proposed |
|---|---|---|
| hardware virtualisation (VMX/SVM, EL2 guests, RISC-V H) | no construct for a virtual machine, its entry/exit and stage-2 translation | `vm` spaces and `enter vm` beside `enter guest`; later item |
| IOMMU (VT-d, SMMU, RISC-V IOMMU) | DMA safety rests on the device contract (named assumption); no device address space | `space` for devices with the same `map`/`flush`; turns the DMA assumption into a proof |
| runtime code: JIT, loadable kernel modules | `make executable` accepts only items the compiler emitted | a verified emitter in the image whose output is proved to compute its cells, or refuse for good |
| suspend to RAM and resume | the resume vector is an arrival state not yet declared | `ResetState` gets a resume arrival; resume code is Gabbro like the reset path |
| performance counters, debug breakpoints, single step | registers are writable through the platform unit, but no entry kinds for their traps | `entry debug`/`entry perf` kinds |
| backtraces and unwinding for panics | no construct reads the frame chain | generated frame descriptors and `backtrace()`; low priority |
| port-I/O rights for guests (x86 I/O bitmap), per-guest MSR access | no grant from kernel authority to a guest beyond memory | `grant d to guest g` for devices and ports |
| secure monitor / TEE (EL3, TrustZone, SMM, M-mode firmware runtime) | privilege `machine` exists, but no secure/normal world split and no world switch | a later boundary; SMM stays outside (firmware) |
| DRAM initialisation on real boards | writable as driver logic, but vendor details are not public on most platforms | not a language gap; reset boot stays on emulator platforms |

Speculation mitigations, retpolines and fences are not user constructs: they are compiler work under B17.
