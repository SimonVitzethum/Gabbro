# C3 -- what the bare-metal runtime still needs before it can be Gabbro

*Slice 2 (session 14, same day) took the Gabbro-facing locks and rcu read sides out of
`metall.h`: **1734 lines, 4 files** (`metall.h` 227). The rest of this map stands.*

*C-free lane, session 13, 2026-10-05. A map, not a result: every line of handwritten C/asm the
bare-metal image still links (`instrumente/zaehle-c.py`: **1879 lines, 4 files** -- `kern.c` 952,
`start.S` 427, `metall.h` 372, `eintritt_asm.h` 128), the piece of the machine it serves, and
what moving it into Gabbro needs. Slice 1 (`36973950`) took the arena, the memory functions and
the two headers out; what is below is what that slice could NOT take without a language step or
a decision.*

## The four walls

| wall | what Gabbro cannot say today | where it bites | proposal |
|---|---|---|---|
| **A -- a device at a FIXED hardware address** | A device handle (`ptr<port, rw> Com1`, `ptr<mmio, rw> Lapic`) reaches a Gabbro function only as a PARAMETER; nothing in the language constructs one. Every example takes it from its caller (`beispiele/02`, `65`). On bare metal there is no caller below the program: the 16550 sits at port `0x3F8`, the PICs at `0x20`/`0xA0`, the LAPIC at `0xFEE00000`, QEMU's exit device at `0xF4` -- facts about the MACHINE. | serial (report channel), PIC masking, LAPIC (timer, EOI, IPIs, ICR), `isa-debug-exit` | a device declaration that NAMES its location as a hardware assumption, e.g. `device Com1 at port 0x3F8 assume com1_ist_da falsifier …;` -- one constant handle per declaration, no arithmetic on it. Port space is not memory (a port number is no address), so this is no int->ptr; for `mmio` it is "memory from outside as a REGION" (Simon, 2026-09-30) whose origin is the hardware instead of a gate. Lean: `D.Reg` exists; the handle's existence is the assumption, named in the manifest like every `geraet` premise. |
| **B -- physical memory read by an address the machine hands over** | ACPI: the RSDP is FOUND by scanning `0xE0000..0xFFFFF` and the EBDA, and its RSDT holds physical ADDRESSES of the next tables -- numbers that must become places. Simon's rule: no int->ptr. | `madt_lies` (which cores exist), `rsdp_suche`, `phys()` | the boot hands ONE region: the identity-mapped low 4 GiB as `ptr<normal, r> u8` with its extent (a hardware assumption of the boot protocol, like `lader`). A table address read from memory is then an INDEX into that region, held by `N571` like any other index -- no number ever becomes a pointer. Needs: the boot form handing that region (Lean: the generic region form of `tor.region`, its origin the loader). |
| **C -- a thread as saved machine state** | A Gabbro thread is a declared root started by a generated driver; the scheduler underneath (run queues, a saved `rsp` per thread, the switch, per-core state through `IA32_GS_BASE`, preemption by the LAPIC timer) is code over raw stacks and registers. | `faden_anlegen`, `kern_schleife`, `abgeben`, `metall_takt`, `begrabe`, `metall_schalte` (asm), the per-core `struct kern` | the hosted twin's route: the thread runtime as a GENERATED template with an abstract-core proof (`faden.laufzeit` did it for `clone`/`futex`): FIFO queue per core, round robin, join word, idle `hlt`. The switch itself (`metall_schalte`: push callee-saved, swap `rsp`, pop) is a machine fact -- a proved template over a named register-file assumption, or asm by Simon's decision. |
| **D -- code before any Gabbro can run** | The Multiboot entry runs in 32-bit protected mode with paging off and no stack; it builds page tables, enters long mode and jumps. The AP trampoline runs in 16-bit REAL mode at physical `0x8000`. No C and no Gabbro can run there. | `start.S` §2 (`_start`, page tables, GDT, long-mode switch), §5 (the trampoline), the Multiboot header | asm by Simon's decision, each piece with its written reason (AUFTRAG-C acceptance 4: "asm only where a Gabbro asm form is not possible, each with Simon's decision recorded"). The same holds for the common entry stub (`eintritt_asm.h`: save every register, call, `iretq`) unless it becomes a proved template. |

## Piece by piece

| piece | lines (about) | file | needs |
|---|---|---|---|
| port/MSR/flag helpers (`outb`, `inb`, `outl`, `wrmsr`, `cli`/`sti`, `pause`) | 30 | kern.c | expressible NOW: `device … at port` lowers to `in`/`out`, the rest are Gabbro `asm` bodies with `arch x86_64` -- but their callers are behind walls A-C |
| serial + report (`seriell_*`, `metall_schreibe`, `metall_zahl`, `hex_roh`) | 90 | kern.c | wall A (the port); the decimal/hex formatting and the bounded wait (`retry … until THRE`, the device assumption `uart_leert_sich` of `beispiele/65`) are Gabbro today |
| `metall_ende` (report + `isa-debug-exit` + `cli; hlt`) | 20 | kern.c | wall A; a `-> never` Gabbro function after it |
| exceptions report + IDT (`idt_setze`, `idt_bau`, `idt_lade`, `metall_idt_setze*`) | 90 | kern.c | the IDT's CONTENT is fully determined by the unit's `entry … vector N` declarations and the runtime's own vectors: a GENERATED table (template, the gate encoding proved) + `lidt` as `asm`; no language step |
| LAPIC (timer, EOI, IPIs, `ipi`, `icr_warte`, `metall_ipi_*`) | 80 | kern.c | wall A (`mmio` at `0xFEE00000`) |
| cores, threads, scheduler, preemption, join, idle | 260 | kern.c | wall C |
| ACPI / MADT | 90 | kern.c | wall B |
| SMP bring-up (INIT-SIPI-SIPI, AP entry) | 70 | kern.c | wall A (ICR) + wall D (the trampoline it copies) |
| BSP main (`metall_bsp`, the order of the above) | 40 | kern.c | Gabbro's `boot` form (`bootdecl`: steps, then dispatch) once the steps exist |
| ticket lock for the runtime's own queues | 25 | metall.h | goes with wall C |
| Gabbro-facing locks (`METALL_SPERRE*`, masked, shared), `METALL_RCU` | ~~140~~ 0 | ~~metall.h~~ | **DONE in slice 2 (2026-10-05)**: the generated `<metall_sperren.h>`, templates `sperre.metall` (the yield a stutter of `CTicket.lean`), `sperre.maskiert` (IF = 0 from before the draw until the restore), `rcu.metall` (the count is the readers' total depth), `SchablonenMetallSperre.lean`. A Gabbro spelling would still need lock OBJECTS: `laufzeit/sperre.gab` is one module-level lock, and module statics are singletons (network lane, wall 10) |
| entry stubs (`METALL_EINTRITT*`, `eintritt_asm.h`) | 200 | metall.h, eintritt_asm.h | wall D, or a proved template over a named register-file assumption |
| boot, page tables, GDT, long mode, context switch, entries, trampoline | 427 | start.S | wall D (and C for the switch) |

## What this asks of Simon

1. **Wall A**: may a `device` declaration name its fixed location as a hardware assumption
   (`at port 0x3F8 assume …`, `at mmio 0xFEE00000 assume …`)? It is the one thing between the
   serial, PIC, LAPIC and exit-device code and Gabbro.
2. **Wall B**: may the boot hand the identity-mapped low physical memory as ONE region with an
   extent, so that ACPI's table addresses become indices into it?
3. **Wall D**: which asm stays asm -- the 32-bit entry and long-mode switch, the 16-bit AP
   trampoline, the register save/restore of the entry stubs, the context switch -- each with its
   reason written beside it?

Wall C needs no decision: it is the hosted route (generated template, abstract-core proof), and
it can start once A gives the timer and the IPIs a Gabbro spelling.
