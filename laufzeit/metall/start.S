/* laufzeit/metall/start.S -- the bare-metal entry of the Gabbro thread runtime
 * (Opus agent I, 2026-09-26).
 *
 * WHAT THIS FILE HOLDS, IN ORDER.
 *   1. The Multiboot1 header (the boot protocol: named assumption A21 of
 *      SPRACHE.md; the loader enters `_start` in 32-bit protected mode,
 *      paging off, `eax` = 0x2BADB002, `ebx` = the info pointer).
 *   2. `_start` (32-bit): identity page tables for the low 4 GiB (2 MiB pages;
 *      the LAPIC at 0xFEE00000 lies inside), PAE + long mode, SSE on, a far
 *      jump into 64-bit code, the BSP stack, then `metall_bsp` (kern.c).
 *   3. `metall_schalte` -- THE context switch (cooperative half; the timer
 *      half is `metall_takt_eintritt` below).
 *   4. The exception and timer entries.
 *   5. The AP trampoline, copied to physical 0x8000 by the BSP before each
 *      INIT-SIPI-SIPI (the SIPI vector 0x08 names page 0x8000).
 *
 * NO LIBC, NO LOADER BEYOND MULTIBOOT. Everything below is the machine's.
 */

#define MB_MAGIC    0x1BADB002
#define MB_FLAGS    0x00000000
#define LAPIC_EOI   0xFEE000B0

/* GDT selectors (one table, used by the BSP and, copied, by every AP). */
#define SEL_CODE32  0x08
#define SEL_DATA    0x10
#define SEL_CODE64  0x18

        .section .multiboot, "a"
        .align 4
        .long MB_MAGIC
        .long MB_FLAGS
        .long -(MB_MAGIC + MB_FLAGS)

/* -------------------------------------------------------------------------
 * 2. The BSP entry, 32-bit.
 * ------------------------------------------------------------------------- */
        .section .text
        .code32
        .global _start
_start:
        cli
        cld
        movl    $boot_stapel_oben, %esp
        movl    %ebx, metall_mb_info       /* kept for a later reader; unused today */

        /* Clear the four table pages the entry fills (PML4, PDPT) -- the PDs
         * below are written entry by entry, so only these need zeroes. */
        movl    $pml4, %edi
        xorl    %eax, %eax
        movl    $(4096 * 2 / 4), %ecx
        rep stosl

        /* PML4[0] -> PDPT, PDPT[0..3] -> PD0..PD3 (present | writable). */
        movl    $pdpt, %eax
        orl     $0x3, %eax
        movl    %eax, pml4
        movl    $pd, %eax
        orl     $0x3, %eax
        movl    %eax, pdpt
        addl    $4096, %eax
        movl    %eax, pdpt + 8
        addl    $4096, %eax
        movl    %eax, pdpt + 16
        addl    $4096, %eax
        movl    %eax, pdpt + 24

        /* 2048 PD entries, 2 MiB each: 4 GiB identity. Present | writable |
         * page size (0x83). The LAPIC page and the ACPI tables are inside. */
        movl    $pd, %edi
        xorl    %ecx, %ecx
1:      movl    %ecx, %eax
        shll    $21, %eax
        orl     $0x83, %eax
        movl    %eax, (%edi)
        movl    %ecx, %eax
        shrl    $11, %eax                  /* high dword: bits 32.. of i * 2 MiB */
        movl    %eax, 4(%edi)
        addl    $8, %edi
        incl    %ecx
        cmpl    $2048, %ecx
        jne     1b

        call    lang_modus_32             /* shared with the AP trampoline's copy */
        lgdt    gdt_zeiger
        ljmp    $SEL_CODE64, $bsp_64

/* Enter long mode with the tables above: PAE + SSE bits in CR4, CR3, EFER.LME,
 * then paging + protection, MP set, EM clear. Called by the BSP only; the AP
 * trampoline carries the same sequence inline (it runs from its copy). */
lang_modus_32:
        movl    %cr4, %eax
        orl     $0x620, %eax               /* PAE | OSFXSR | OSXMMEXCPT */
        movl    %eax, %cr4
        movl    $pml4, %eax
        movl    %eax, %cr3
        movl    $0xC0000080, %ecx          /* IA32_EFER */
        rdmsr
        orl     $0x100, %eax               /* LME */
        wrmsr
        movl    %cr0, %eax
        andl    $0xFFFFFFFB, %eax          /* EM off: x87/SSE execute */
        orl     $0x80000003, %eax          /* PG | MP | PE */
        movl    %eax, %cr0
        ret

        .code64
bsp_64:
        movw    $SEL_DATA, %ax
        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %ss
        xorw    %ax, %ax
        movw    %ax, %fs
        movw    %ax, %gs
        movabsq $boot_stapel_oben, %rsp
        fninit
        call    metall_bsp                 /* kern.c; never returns */
2:      hlt
        jmp     2b

/* -------------------------------------------------------------------------
 * 3. The context switch.
 *
 *   void metall_schalte(uint64_t *alt_rsp, uint64_t neu_rsp);
 *
 * A CALL BOUNDARY, so the SysV ABI says what must survive: rbx, rbp, r12-r15,
 * the MXCSR control bits and the x87 control word. Everything else is
 * caller-saved and the caller has already given it up. The switch pushes the
 * callee-saved set onto the OLD stack, stores the old rsp, loads the new one,
 * pops the same set in reverse and returns on the new stack -- the frame
 * layout is the one `metall_rahmen_neu` (kern.c) writes for a thread that has
 * never run. Interrupts: the caller runs with IF = 0 (kern.c disables them
 * around every switch), so no timer entry can land between the store and the
 * load.
 * ------------------------------------------------------------------------- */
        .global metall_schalte
metall_schalte:
        pushq   %rbp
        pushq   %rbx
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        subq    $8, %rsp
        stmxcsr (%rsp)
        fnstcw  4(%rsp)
        movq    %rsp, (%rdi)
        movq    %rsi, %rsp
        ldmxcsr (%rsp)
        fldcw   4(%rsp)
        addq    $8, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbx
        popq    %rbp
        ret

/* -------------------------------------------------------------------------
 * 4. Exception and timer entries.
 *
 * EXCEPTIONS (0..31): the runtime does not recover from a CPU exception; it
 * reports the vector, the error code and the faulting rip on the serial line
 * and ends the machine with the failure code (kern.c `metall_ausnahme`). A
 * trap is loud, never a reset loop -- `__builtin_trap` (the emitter's `ud2`
 * after a refused start) lands here as vector 6.
 * ------------------------------------------------------------------------- */
        .macro AUSNAHME_OHNE nr
        .global metall_ausnahme_\nr
metall_ausnahme_\nr:
        pushq   $0
        pushq   $\nr
        jmp     ausnahme_gemeinsam
        .endm
        .macro AUSNAHME_MIT nr
        .global metall_ausnahme_\nr
metall_ausnahme_\nr:
        pushq   $\nr
        jmp     ausnahme_gemeinsam
        .endm

        AUSNAHME_OHNE 0
        AUSNAHME_OHNE 1
        AUSNAHME_OHNE 2
        AUSNAHME_OHNE 3
        AUSNAHME_OHNE 4
        AUSNAHME_OHNE 5
        AUSNAHME_OHNE 6
        AUSNAHME_OHNE 7
        AUSNAHME_MIT  8
        AUSNAHME_OHNE 9
        AUSNAHME_MIT  10
        AUSNAHME_MIT  11
        AUSNAHME_MIT  12
        AUSNAHME_MIT  13
        AUSNAHME_MIT  14
        AUSNAHME_OHNE 15
        AUSNAHME_OHNE 16
        AUSNAHME_MIT  17
        AUSNAHME_OHNE 18
        AUSNAHME_OHNE 19
        AUSNAHME_OHNE 20
        AUSNAHME_MIT  21
        AUSNAHME_OHNE 22
        AUSNAHME_OHNE 23
        AUSNAHME_OHNE 24
        AUSNAHME_OHNE 25
        AUSNAHME_OHNE 26
        AUSNAHME_OHNE 27
        AUSNAHME_OHNE 28
        AUSNAHME_MIT  29
        AUSNAHME_MIT  30
        AUSNAHME_OHNE 31
        /* 0xFF: the spurious-interrupt vector of the LAPIC (SVR). No EOI. */
        .global metall_unecht
metall_unecht:
        iretq

ausnahme_gemeinsam:
        /* Stack: vector, error code, rip, cs, rflags, rsp, ss. */
        movq    (%rsp), %rdi
        movq    8(%rsp), %rsi
        movq    16(%rsp), %rdx
        andq    $-16, %rsp
        call    metall_ausnahme            /* kern.c; never returns */
3:      hlt
        jmp     3b

/* THE TIMER ENTRY (LAPIC timer, vector 0x40): preemption.
 *
 * The interrupted thread may be ANYWHERE -- mid-expression, mid-float -- so
 * unlike the call-boundary switch above, EVERY register it owns is saved:
 * the fifteen general registers on its own stack, and the full x87/SSE state
 * with `fxsave` into a 512-byte, 16-aligned area below them. Then the C half
 * (`metall_takt`) acknowledges the LAPIC and yields through the SAME
 * `metall_schalte` as a cooperative switch -- from the thread's own stack,
 * with IF = 0 (an interrupt gate cleared it). When the scheduler resumes the
 * thread, `metall_schalte` returns here, the state is restored in reverse and
 * `iretq` puts IF back to what the thread had. The red zone: every file of the
 * image is built with `-mno-red-zone`, so the push below never lands on a
 * leaf function's live locals.
 */
        .global metall_takt_eintritt
metall_takt_eintritt:
        pushq   %rax
        pushq   %rbx
        pushq   %rcx
        pushq   %rdx
        pushq   %rsi
        pushq   %rdi
        pushq   %rbp
        pushq   %r8
        pushq   %r9
        pushq   %r10
        pushq   %r11
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        movq    %rsp, %rbx                 /* rbx is callee-saved: survives the call */
        subq    $512, %rsp
        andq    $-16, %rsp
        fxsave  (%rsp)
        call    metall_takt                /* kern.c: EOI, then maybe yield */
        fxrstor (%rsp)
        movq    %rbx, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %r11
        popq    %r10
        popq    %r9
        popq    %r8
        popq    %rbp
        popq    %rdi
        popq    %rsi
        popq    %rdx
        popq    %rcx
        popq    %rbx
        popq    %rax
        iretq

/* THE PROGRAM'S OWN ENTRIES (Opus agent J, 2026-09-26; OFFEN O32 residue).
 *
 * An emitted `entry NAME ... via idt` (or an `entry` without `via`, entered
 * by `int`) names `void gabbro_eintritt_NAME(void)` and says in its own
 * comment: "THE STUB IS NOT A C FUNCTION ... the emitter names the primitive
 * and does not define it". This is where it is defined on bare metal. The
 * per-entry half is three instructions (`METALL_EINTRITT` in metall.h): save
 * rax, load the address of the entry's C half into rax, jump here. The common
 * half saves every OTHER general register and the full x87/SSE state, exactly
 * as the timer entry above does -- a thrown interrupt lands anywhere, so the
 * interrupted code's registers are all preserved, which is stronger than the
 * entry's declared `preserves` list and never weaker -- calls the C half
 * (which runs the unit's `dispatch` target and, for a THROWN entry, writes
 * the LAPIC EOI), restores, `iretq`.
 *
 * IF on entry: 0 (interrupt gate, `idt_setze`). The C half runs with IF = 0;
 * `nested never` holds on the core because nothing in it sets IF (the lock a
 * `via idt` dispatch may take is a `masks irqs` lock, `METALL_SPERRE_MASKIERT`,
 * whose spin never yields with IF = 0). The stack is the interrupted
 * context's own (a thread's, or the core's scheduler stack when it was idle):
 * the declared `stack NAME per cpu` is NOT switched to -- named in OFFEN O32.
 */
        .global metall_eintritt_gemeinsam
metall_eintritt_gemeinsam:
        /* rax is already on the stack (pushed by the per-entry half) and
         * holds the C half's address. */
        pushq   %rbx
        pushq   %rcx
        pushq   %rdx
        pushq   %rsi
        pushq   %rdi
        pushq   %rbp
        pushq   %r8
        pushq   %r9
        pushq   %r10
        pushq   %r11
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        movq    %rsp, %rbx
        subq    $512, %rsp
        andq    $-16, %rsp
        fxsave  (%rsp)
        movq    %rbx, %rdi                 /* struct metall_rahmen * (metall.h) */
        call    *%rax
        fxrstor (%rsp)
        movq    %rbx, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %r11
        popq    %r10
        popq    %r9
        popq    %r8
        popq    %rbp
        popq    %rdi
        popq    %rsi
        popq    %rdx
        popq    %rcx
        popq    %rbx
        popq    %rax
        iretq

/* THE WAKE ENTRY (vector 0x41): an idle core sleeps in `hlt` (kern.c,
 * `kern_schleife`); a start that places a thread on it sends this IPI. The C
 * half only acknowledges -- the wake-up IS the effect. */
        .global metall_wecken_eintritt
metall_wecken_eintritt:
        pushq   %rax
        movq    $metall_wecken, %rax
        jmp     metall_eintritt_gemeinsam

/* -------------------------------------------------------------------------
 * 5. The AP trampoline. Copied byte for byte to physical 0x8000; every
 * absolute reference inside it is written `T(label)` = its offset from
 * `tramp_anfang` plus 0x8000, which the assembler resolves as a constant
 * because both labels stand in this one section. The BSP fills the three
 * parameter words at the end of the copy before each SIPI.
 * ------------------------------------------------------------------------- */
#define TRAMP_BASIS 0x8000
#define T(x) ((x) - tramp_anfang + TRAMP_BASIS)

        .global tramp_anfang, tramp_ende
        .global tramp_cr3, tramp_stapel, tramp_ziel
        .code16
tramp_anfang:
        cli
        cld
        xorw    %ax, %ax
        movw    %ax, %ds
        lgdtl   T(tramp_gdt_zeiger)
        movl    %cr0, %eax
        orl     $1, %eax
        movl    %eax, %cr0
        ljmpl   $SEL_CODE32, $T(tramp_32)

        .code32
tramp_32:
        movw    $SEL_DATA, %ax
        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %ss
        movl    %cr4, %eax
        orl     $0x620, %eax               /* PAE | OSFXSR | OSXMMEXCPT */
        movl    %eax, %cr4
        movl    T(tramp_cr3), %eax
        movl    %eax, %cr3
        movl    $0xC0000080, %ecx
        rdmsr
        orl     $0x100, %eax
        wrmsr
        movl    %cr0, %eax
        andl    $0xFFFFFFFB, %eax
        orl     $0x80000003, %eax
        movl    %eax, %cr0
        ljmp    $SEL_CODE64, $T(tramp_64)

        .code64
tramp_64:
        movw    $SEL_DATA, %ax
        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %ss
        xorw    %ax, %ax
        movw    %ax, %fs
        movw    %ax, %gs
        movq    T(tramp_stapel), %rsp
        fninit
        movq    T(tramp_ziel), %rax
        call    *%rax                      /* kern.c `metall_ap`; never returns */
4:      hlt
        jmp     4b

        .align 8
tramp_gdt:
        .quad   0
        .quad   0x00CF9A000000FFFF         /* 0x08 code32 */
        .quad   0x00CF92000000FFFF         /* 0x10 data   */
        .quad   0x00AF9A000000FFFF         /* 0x18 code64 (L = 1) */
tramp_gdt_zeiger:
        .word   tramp_gdt_zeiger - tramp_gdt - 1
        .long   T(tramp_gdt)
        .align 8
tramp_cr3:      .quad 0
tramp_stapel:   .quad 0
tramp_ziel:     .quad 0
tramp_ende:

/* -------------------------------------------------------------------------
 * The BSP's GDT (same layout as the trampoline's) and the boot data.
 * ------------------------------------------------------------------------- */
        .section .rodata
        .align 8
gdt:
        .quad   0
        .quad   0x00CF9A000000FFFF
        .quad   0x00CF92000000FFFF
        .quad   0x00AF9A000000FFFF
gdt_zeiger:
        .word   gdt_zeiger - gdt - 1
        .quad   gdt

        .section .bss
        .align 4096
        .global pml4
pml4:   .skip 4096
pdpt:   .skip 4096
pd:     .skip 4096 * 4
        .align 16
boot_stapel:
        .skip 16384
boot_stapel_oben:
        .global metall_mb_info
        .align 8
metall_mb_info: .skip 8

        .section .note.GNU-stack, "", @progbits
