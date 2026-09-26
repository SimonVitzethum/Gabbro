/* sonde_metall_systemruf -- the falsifier for `metal_kernel_contract`.
 *
 * THE OBLIGATION, as it stands in the source (every gate unit with a `target … abi metal`
 * block, e.g. `beispiele/74-syscall-schreiben.gab`):
 *
 *     assume metal_kernel_contract
 *         "The image's kernel entry keeps the Linux x86_64 convention …"
 *         falsifier sonde_metall_systemruf;
 *
 * and at every metal binding resting on it (`target metal abi metal arch x86_64 { … }`):
 *
 *     assume metal_kernel_contract falsifier sonde_metall_systemruf;
 *
 * This probe belongs to EXACTLY this one obligation (N024).
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * A gate bound by `abi metal` lowers to `int $0x80` with the number in rax, its parameters
 * in the bound registers, and it tells the compiler that ONLY rax and memory change
 * (`syscall_befehl` in `emit.rs`: no `rcx`/`r11` clobber, unlike Linux `syscall`). That
 * register half of the assumption is carried by the runtime's entry: `metall_eintritt_gemeinsam`
 * and `metall_systemruf_eintritt` in `laufzeit/metall/eintritt_asm.h`. This probe INCLUDES
 * that header and assembles the very same instructions into a userland program (an `iretq`
 * from ring 3 to ring 3 is legal), enters them through a hand-built interrupt frame exactly
 * as `int $0x80` would leave it, with a service (`metall_systemruf`) that answers number 1
 * with the sum of its six arguments and number 2 with `-EBADF` (-9), and holds:
 *
 *   1. the answer arrives in rax (the sum; then -9 for the error leg, inside -4095..-1);
 *   2. EVERY other general register -- rbx rcx rdx rsi rdi rbp r8..r15 -- comes back with
 *      the value it went in with, and the stack pointer too;
 *   3. the x87/SSE state survives (xmm0 through the service, which writes xmm0 itself).
 *
 * What it does NOT assert: what the image's kernel does for a number (Caprock's or a
 * program's services are the per-gate half of the assumption -- this probe's service is its
 * own); interrupt-gate behaviour (IF, the IDT) -- ring 3 has none; timing.
 *
 * POSITIVE CONTROL (R14)
 * ----------------------
 * `--kaputt` makes the service write the frame's rbx -- the same shape as a stub whose
 * restore dropped a register -- and the probe must exit 1. The default run must pass.
 *
 * Documented runs (cc -std=c11 -O2 -Wall -Wextra -Werror -pthread, x86_64 Linux):
 *   $ ./sonde_metall_systemruf
 *     -> exit 0, answer and 15 registers + xmm0 held over 1000 entries (PASSES)
 *   $ ./sonde_metall_systemruf --kaputt
 *     -> exit 1, rbx came back changed (control FALLS)
 *
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- not x86_64
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if defined(__x86_64__)
#include "../laufzeit/metall/eintritt_asm.h"

/* The frame layout of `laufzeit/metall/metall.h` (not included: it pulls the runtime's
 * freestanding declarations). The probe checks the order itself below (leg 2 would fall on
 * any permutation the service reads). */
struct metall_rahmen {
    uint64_t r15, r14, r13, r12, r11, r10, r9, r8, rbp, rdi, rsi, rdx, rcx, rbx, rax;
    uint64_t rip, cs, rflags, rsp, ss;
};

static int kaputt;

/* The image's kernel, as the probe plays it. */
void metall_systemruf_c(struct metall_rahmen *r);
void metall_systemruf_c(struct metall_rahmen *r)
{
    /* The service clobbers every caller-saved register and xmm0 on its own -- the stub, not
     * the service, owes the interrupted code its registers. */
    __asm__ __volatile__("xorps %%xmm0, %%xmm0\n\t"
                         "movq $0x5a5a, %%rcx\n\tmovq $0x5a5a, %%rdx\n\tmovq $0x5a5a, %%r8\n\t"
                         "movq $0x5a5a, %%r9\n\tmovq $0x5a5a, %%r10\n\tmovq $0x5a5a, %%r11\n\t"
                         ::: "xmm0", "rcx", "rdx", "r8", "r9", "r10", "r11");
    if (r->rax == 1u) {
        r->rax = r->rdi + r->rsi + r->rdx + r->r10 + r->r8 + r->r9;
    } else if (r->rax == 2u) {
        r->rax = (uint64_t)(int64_t)-9;
    } else {
        r->rax = (uint64_t)(int64_t)-38;
    }
    if (kaputt) {
        r->rbx ^= 1u;
    }
}

__asm__(METALL_EINTRITT_GEMEINSAM_ASM);

/* in[0..15]: rax rbx rcx rdx rsi rdi rbp r8 .. r15 before; out[0..15] after; out[16] the
 * stack pointer after, in[16] before. xmm: in[17] before (low quadword), out[17] after. */
void sonde_rufe(uint64_t *in, uint64_t *out);
__asm__(
    "\t.text\n"
    "\t.global sonde_rufe\n"
    "sonde_rufe:\n"
    "\tpushq %rbx\n\tpushq %rbp\n\tpushq %r12\n\tpushq %r13\n\tpushq %r14\n\tpushq %r15\n"
    "\tpushq %rsi\n"                    /* out */
    "\tpushq %rdi\n"                    /* in */
    "\tmovq %rsp, 128(%rdi)\n"          /* in[16] = rsp before the frame */
    "\tmovq 136(%rdi), %xmm0\n"         /* in[17] -> xmm0 */
    "\tmovq %rsp, %rax\n"
    "\tmovq %ss, %rcx\n\tpushq %rcx\n"  /* ss */
    "\tpushq %rax\n"                    /* rsp: the value before these pushes */
    "\tpushfq\n"                        /* rflags */
    "\tmovq %cs, %rcx\n\tpushq %rcx\n"  /* cs */
    "\tleaq 1f(%rip), %rcx\n\tpushq %rcx\n" /* rip */
    "\tmovq 8(%rdi), %rbx\n\tmovq 16(%rdi), %rcx\n\tmovq 24(%rdi), %rdx\n"
    "\tmovq 32(%rdi), %rsi\n\tmovq 48(%rdi), %rbp\n\tmovq 56(%rdi), %r8\n"
    "\tmovq 64(%rdi), %r9\n\tmovq 72(%rdi), %r10\n\tmovq 80(%rdi), %r11\n"
    "\tmovq 88(%rdi), %r12\n\tmovq 96(%rdi), %r13\n\tmovq 104(%rdi), %r14\n"
    "\tmovq 112(%rdi), %r15\n\tmovq 0(%rdi), %rax\n\tmovq 40(%rdi), %rdi\n"
    "\tjmp metall_systemruf_eintritt\n" /* what `int $0x80` does, less the IDT */
    "1:\n"
    "\tpushq %rax\n"                    /* free one register */
    "\tmovq 16(%rsp), %rax\n"           /* out */
    "\tpopq 0(%rax)\n"                  /* out[0] = rax after */
    "\tmovq %rbx, 8(%rax)\n\tmovq %rcx, 16(%rax)\n\tmovq %rdx, 24(%rax)\n"
    "\tmovq %rsi, 32(%rax)\n\tmovq %rdi, 40(%rax)\n\tmovq %rbp, 48(%rax)\n"
    "\tmovq %r8, 56(%rax)\n\tmovq %r9, 64(%rax)\n\tmovq %r10, 72(%rax)\n"
    "\tmovq %r11, 80(%rax)\n\tmovq %r12, 88(%rax)\n\tmovq %r13, 96(%rax)\n"
    "\tmovq %r14, 104(%rax)\n\tmovq %r15, 112(%rax)\n"
    "\tmovq %rsp, 128(%rax)\n"          /* out[16] = rsp after: the depth in[16] recorded */
    "\tpopq %rcx\n"                     /* in */
    "\tmovq %xmm0, 136(%rax)\n"
    "\tpopq %rsi\n"
    "\tpopq %r15\n\tpopq %r14\n\tpopq %r13\n\tpopq %r12\n\tpopq %rbp\n\tpopq %rbx\n"
    "\tret\n");

static const char *const NAME[18] = { "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8",
                                      "r9", "r10", "r11", "r12", "r13", "r14", "r15", "-",
                                      "rsp", "xmm0" };

int main(int argc, char **argv)
{
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--kaputt") == 0) {
            kaputt = 1;
        }
    }
    uint64_t x = 0x9e3779b97f4a7c15u;
    for (int runde = 0; runde < 1000; runde++) {
        uint64_t in[18], out[18];
        for (int i = 0; i < 18; i++) {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            in[i] = x & 0x0000ffffffffffffu;
        }
        in[0] = (runde % 2 == 0) ? 1u : 2u;           /* the number */
        in[15] = 0;
        out[15] = 0;
        sonde_rufe(in, out);
        uint64_t soll = in[0] == 1u ? in[5] + in[4] + in[3] + in[9] + in[7] + in[8]
                                    : (uint64_t)(int64_t)-9;
        if (out[0] != soll) {
            printf("REFUTED: number %llu answered %lld in rax, owed %lld\n",
                   (unsigned long long)in[0], (long long)out[0], (long long)soll);
            return 1;
        }
        if (in[0] == 2u && !((int64_t)out[0] < 0 && (int64_t)out[0] >= -4095)) {
            printf("REFUTED: the error leg answered outside -4095..-1\n");
            return 1;
        }
        for (int i = 1; i < 18; i++) {
            if (i == 15) {
                continue;
            }
            if (out[i] != in[i]) {
                printf("REFUTED: %s went in as %#llx and came back as %#llx (round %d)\n",
                       NAME[i], (unsigned long long)in[i], (unsigned long long)out[i], runde);
                return 1;
            }
        }
    }
    printf("not refuted: answer in rax, 15 registers, rsp and xmm0 held over 1000 entries "
           "through metall_eintritt_gemeinsam (the image's own text)\n");
    return 0;
}
#else
int main(void)
{
    printf("not runnable here: the entry is x86_64\n");
    return 77;
}
#endif
