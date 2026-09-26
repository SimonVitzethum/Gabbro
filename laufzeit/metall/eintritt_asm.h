/* laufzeit/metall/eintritt_asm.h -- the common entry stub, as ONE text
 * (Opus agent L, OFFEN O31; the stub itself is Opus agent J's, moved here
 * unchanged from start.S).
 *
 * `metall_eintritt_gemeinsam` is where every program entry (`METALL_EINTRITT`
 * in metall.h), the wake entry (vector 0x41) and the kernel service entry
 * (vector 0x80) land: the per-entry half has pushed rax and loaded the address
 * of its C half into rax; the common half saves every OTHER general register
 * and the full x87/SSE state, calls the C half with the saved frame
 * (`struct metall_rahmen *`, metall.h), restores, `iretq`. What the C half
 * writes into the frame is what the interrupted code finds after `iretq`; every
 * register it leaves alone comes back as it was.
 *
 * WHY A HEADER AND NOT start.S: the kernel service entry carries a named
 * assumption (`metal_kernel_contract`: the Linux x86_64 convention -- the
 * answer in rax, nothing else destroyed), and its falsifier
 * `sonden/sonde_metall_systemruf.c` is a userland program. It includes this
 * header and assembles the SAME instructions (an `iretq` from ring 3 to ring 3
 * is legal), so the probe runs what the image runs -- a copy would be a probe
 * of the copy. kern.c assembles it into the image (`__asm__` below).
 *
 * `leaq sym(%rip)` and not `movq $sym`: the same text links into the non-PIE
 * image and into the probe's PIE executable.
 *
 * IF on entry (in the image): 0 -- interrupt gates (`idt_setze`). The stack is
 * the interrupted context's own: the declared `stack NAME per cpu` / `ist` of an
 * entry is NOT switched to (OFFEN O32 (8)). */
#ifndef METALL_EINTRITT_ASM_H
#define METALL_EINTRITT_ASM_H

#define METALL_EINTRITT_GEMEINSAM_ASM                                   \
    "\t.text\n"                                                         \
    "\t.global metall_eintritt_gemeinsam\n"                             \
    "metall_eintritt_gemeinsam:\n"                                      \
    "\tpushq %rbx\n"                                                    \
    "\tpushq %rcx\n"                                                    \
    "\tpushq %rdx\n"                                                    \
    "\tpushq %rsi\n"                                                    \
    "\tpushq %rdi\n"                                                    \
    "\tpushq %rbp\n"                                                    \
    "\tpushq %r8\n"                                                     \
    "\tpushq %r9\n"                                                     \
    "\tpushq %r10\n"                                                    \
    "\tpushq %r11\n"                                                    \
    "\tpushq %r12\n"                                                    \
    "\tpushq %r13\n"                                                    \
    "\tpushq %r14\n"                                                    \
    "\tpushq %r15\n"                                                    \
    "\tmovq %rsp, %rbx\n"                                               \
    "\tsubq $512, %rsp\n"                                               \
    "\tandq $-16, %rsp\n"                                               \
    "\tfxsave (%rsp)\n"                                                 \
    "\tmovq %rbx, %rdi\n"                                               \
    "\tcall *%rax\n"                                                    \
    "\tfxrstor (%rsp)\n"                                                \
    "\tmovq %rbx, %rsp\n"                                               \
    "\tpopq %r15\n"                                                     \
    "\tpopq %r14\n"                                                     \
    "\tpopq %r13\n"                                                     \
    "\tpopq %r12\n"                                                     \
    "\tpopq %r11\n"                                                     \
    "\tpopq %r10\n"                                                     \
    "\tpopq %r9\n"                                                      \
    "\tpopq %r8\n"                                                      \
    "\tpopq %rbp\n"                                                     \
    "\tpopq %rdi\n"                                                     \
    "\tpopq %rsi\n"                                                     \
    "\tpopq %rdx\n"                                                     \
    "\tpopq %rcx\n"                                                     \
    "\tpopq %rbx\n"                                                     \
    "\tpopq %rax\n"                                                     \
    "\tiretq\n"                                                         \
    /* THE KERNEL SERVICE ENTRY (vector 0x80, OFFEN O31): a gate bound  \
     * by `target … abi metal` executes `int $0x80`; the C half         \
     * `metall_systemruf_c` hands the frame to the image's kernel. */   \
    "\t.global metall_systemruf_eintritt\n"                             \
    "metall_systemruf_eintritt:\n"                                      \
    "\tpushq %rax\n"                                                    \
    "\tleaq metall_systemruf_c(%rip), %rax\n"                           \
    "\tjmp metall_eintritt_gemeinsam\n"                                 \
    /* THE ERROR-CODE TWIN (OFFEN O32 (9), Opus agent L): the CPU      \
     * pushes an error code for vectors 8, 10..14, 17, 21, 29, 30, so   \
     * the frame holds it between the saved rax and rip. The twin saves \
     * and restores exactly as above, then drops the code before        \
     * `iretq`. The C half sees `struct metall_rahmen_fc` (metall.h). */ \
    "\t.global metall_eintritt_gemeinsam_fc\n"                          \
    "metall_eintritt_gemeinsam_fc:\n"                                   \
    "\tpushq %rbx\n"                                                    \
    "\tpushq %rcx\n"                                                    \
    "\tpushq %rdx\n"                                                    \
    "\tpushq %rsi\n"                                                    \
    "\tpushq %rdi\n"                                                    \
    "\tpushq %rbp\n"                                                    \
    "\tpushq %r8\n"                                                     \
    "\tpushq %r9\n"                                                     \
    "\tpushq %r10\n"                                                    \
    "\tpushq %r11\n"                                                    \
    "\tpushq %r12\n"                                                    \
    "\tpushq %r13\n"                                                    \
    "\tpushq %r14\n"                                                    \
    "\tpushq %r15\n"                                                    \
    "\tmovq %rsp, %rbx\n"                                               \
    "\tsubq $512, %rsp\n"                                               \
    "\tandq $-16, %rsp\n"                                               \
    "\tfxsave (%rsp)\n"                                                 \
    "\tmovq %rbx, %rdi\n"                                               \
    "\tcall *%rax\n"                                                    \
    "\tfxrstor (%rsp)\n"                                                \
    "\tmovq %rbx, %rsp\n"                                               \
    "\tpopq %r15\n"                                                     \
    "\tpopq %r14\n"                                                     \
    "\tpopq %r13\n"                                                     \
    "\tpopq %r12\n"                                                     \
    "\tpopq %r11\n"                                                     \
    "\tpopq %r10\n"                                                     \
    "\tpopq %r9\n"                                                      \
    "\tpopq %r8\n"                                                      \
    "\tpopq %rbp\n"                                                     \
    "\tpopq %rdi\n"                                                     \
    "\tpopq %rsi\n"                                                     \
    "\tpopq %rdx\n"                                                     \
    "\tpopq %rcx\n"                                                     \
    "\tpopq %rbx\n"                                                     \
    "\tpopq %rax\n"                                                     \
    "\taddq $8, %rsp\n"                                                 \
    "\tiretq\n"

#endif
