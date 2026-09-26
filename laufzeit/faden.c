/* laufzeit/faden.c -- raw-clone threads for runtime `start` (lane 260).
 *
 * SIMON'S RULE, AS CODE. Threads at run time are made by OUR OWN code issuing
 * the kernel system call -- not by libc (`pthread_create`, the glibc `clone()`
 * wrapper, `fork`). This file issues `clone` itself (x86_64 Linux: the
 * `syscall` instruction, number 56), on a stack WE allocate (the unit's own
 * static region, handed in as `spitze`), and waits with our own `futex`
 * syscall (number 202). No libc threading stands on these paths: no header
 * beyond `<stdint.h>` is included, and `nm` on the object names no
 * `pthread_*`, no `clone`, no `__errno_location`.
 *
 * REGISTERS, ONE BY ONE. The `syscall` instruction itself destroys `rcx`
 * (it holds the return address) and `r11` (it holds the flags) -- both stand
 * in every clobber list below, the same two the syscall stub destroys
 * (`emit.rs`, `syscall_stumpf`). The kernel calling convention takes number
 * in `rax`, arguments in `rdi rsi rdx r10 r8 r9`, answer in `rax`. `r10`
 * has no constraint letter, so it travels in a pinned register variable
 * (the musl idiom the stub already uses).
 *
 * FLAGS, ONE BY ONE. The clone set is
 *
 *   CLONE_VM         0x00000100  one address space: the threads share the
 *                                tables, which is what makes them threads.
 *   CLONE_FS         0x00000200  one filesystem view (like the glibc wrapper).
 *   CLONE_FILES      0x00000400  one file table (like the glibc wrapper).
 *   CLONE_SIGHAND    0x00000800  one signal-handler table (like the wrapper).
 *   CLONE_THREAD     0x00010000  one thread group: signals address the group,
 *                                and `exit` below ends THIS thread, not the
 *                                process (that is why it must not be
 *                                `exit_group`).
 *   CLONE_SYSVSEM    0x00040000  one SysV semaphore undo list (wrapper parity;
 *                                Gabbro's own locks are futexes, never SysV).
 *   CLONE_CHILD_CLEARTID 0x00200000  the join: the kernel clears the word at
 *                                `ctid` on thread exit and wakes one futex
 *                                waiter, so the join is a wait loop, not a
 *                                guess about scheduling.
 *
 * What is NOT set, and why:
 *
 *   CLONE_SETTLS is absent: no TLS is used anywhere on these paths. The
 *   threads run nullary roots over shared tables plus their own stack; they
 *   touch no `errno` (raw answers stay in locals), no thread-local, nothing
 *   that would need a segment base. Setting it would promise a facility
 *   nobody reads.
 *
 *   CLONE_PARENT_SETTID is absent: the parent learns the TID as the return
 *   value and stores it into the join word itself.
 *
 * THE CHILD NEVER EXECUTES A C FRAME ON THE NEW STACK. `clone` returns
 * twice -- once in the parent (the TID), once in the child (zero) -- but the
 * kernel puts the handed stack under the child AT the return: the very next
 * C instruction (`pop %rbp; ret` of a helper call) would pop words off the
 * NEW stack and return into whatever they hold (a zeroed static stack holds
 * zero -- measured 2026-09-26 as a jump to NULL). So the `syscall` is issued
 * from inline asm that branches BEFORE any C stack operation: the child
 * moves the handed top into `rsp` (already there -- the move states the
 * ownership), CALLS the root on it, and when the root returns exits the
 * THREAD with `SYS_exit` (60), never `exit_group` (231). A `call` pushes its
 * return address onto the NEW stack, so that push is the first word the new
 * stack carries and the whole root runs where the unit said it would. `ud2`
 * stands behind the exit the way the stub's hardware outcome stands behind
 * its decoding: under the kernel contract that point is not reached, and the
 * instruction says so loudly instead of falling through.
 *
 * THE JOIN. `gabbro_faden_warte` reloads the word with acquire semantics
 * until it reads zero, waiting in `FUTEX_WAIT` on the last-seen nonzero
 * value in between. A clear concurrent with the load fails the wait with
 * EAGAIN, a spurious wake re-loops: every path re-reads. The kernel's clear
 * is the release half, so everything the thread wrote is visible when the
 * wait returns -- that edge is the TSan-free design argument for the join
 * word (the unit's own carriers rest on `N462`: guarded, atomic or
 * per-core, decided by the checker, not here).
 *
 * NO `errno`. Raw answers stay negative in locals and come back positive;
 * nothing here names the thread-local error cell, which is exactly the TLS
 * the flags above declined.
 */

#include "faden.h"

/* -- The kernel numbers (x86_64 Linux; the ABI, not libc). ------------------ */

#define GABBRO_SYS_CLONE 56L
#define GABBRO_SYS_FUTEX 202L
#define GABBRO_SYS_EXIT 60L

#define GABBRO_FUTEX_WAIT 0L

/* -- The clone set, justified above. ---------------------------------------- */

#define GABBRO_CLONE_VM 0x00000100L
#define GABBRO_CLONE_FS 0x00000200L
#define GABBRO_CLONE_FILES 0x00000400L
#define GABBRO_CLONE_SIGHAND 0x00000800L
#define GABBRO_CLONE_THREAD 0x00010000L
#define GABBRO_CLONE_SYSVSEM 0x00040000L
#define GABBRO_CLONE_CHILD_CLEARTID 0x00200000L

#define GABBRO_CLONE_FLAGS \
    (GABBRO_CLONE_VM | GABBRO_CLONE_FS | GABBRO_CLONE_FILES | GABBRO_CLONE_SIGHAND | \
     GABBRO_CLONE_THREAD | GABBRO_CLONE_SYSVSEM | GABBRO_CLONE_CHILD_CLEARTID)

/* -- One raw system call. ----------------------------------------------------
 *
 * WHY SIX ARGUMENTS ALWAYS. The sites below pass at most four; spelling all
 * six keeps ONE helper with one clobber list instead of four shapes that
 * drift apart (the same reason the stub template is one template).
 */

static long roh_aufruf(long nr, long a1, long a2, long a3, long a4, long a5, long a6)
{
    register long r10 __asm__("r10") = a4;
    register long r8 __asm__("r8") = a5;
    register long r9 __asm__("r9") = a6;
    register long rax __asm__("rax") = nr;
    __asm__ __volatile__(
        "syscall"
        : "+a"(rax)
        : "D"(a1), "S"(a2), "d"(a3), "r"(r10), "r"(r8), "r"(r9)
        : "memory", "rcx", "r11", "cc");
    return rax;
}

int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort)
{
    long r;
    /* rdi = flags, rsi = handed stack, rdx = ptid (none), r10 = ctid (the
     * join word the kernel clears), r8 = tls (none: no CLONE_SETTLS). The
     * pins are the musl idiom the syscall stub uses (`r10` has no
     * constraint letter); `rax` is in-out (`+a`): the number going in, the
     * raw answer coming out. */
    register long r_rax __asm__("rax") = GABBRO_SYS_CLONE;
    register long r_rdi __asm__("rdi") = GABBRO_CLONE_FLAGS;
    register long r_rsi __asm__("rsi") = (long)spitze;
    register long r_rdx __asm__("rdx") = 0;
    register long r_r10 __asm__("r10") = (long)wort;
    register long r_r8 __asm__("r8") = 0;
    if (fn == 0 || spitze == 0 || wort == 0) {
        return 22; /* EINVAL: a null root, stack or word starts nothing. */
    }
    if (((uintptr_t)spitze & 15u) != 0u) {
        return 22; /* EINVAL: the SysV ABI wants rsp 16-aligned before a
                    * call, and the child below calls the root. */
    }
    /* THE SYSCALL AND THE FIRST BRANCH ARE ONE ASM: the child is already on
     * the handed stack when `syscall` returns, so no C stack operation --
     * no pop, no ret, no spill -- may stand between the return and the
     * child's own path. `testq` splits: nonzero (a TID, or a negative errno)
     * falls to `1` and back into C; zero is the child, which never comes
     * back. The numeric label is asm-local: every expansion carries its own.
     * `cc` is clobbered (`testq`, `xorl`); `rcx`/`r11` are the syscall's
     * own, like in every stub. */
    __asm__ __volatile__(
        "syscall\n\t"
        "testq %%rax, %%rax\n\t"
        "jnz 1f\n\t"
        "movq %[spitze], %%rsp\n\t"
        "call *%[fn]\n\t"
        "movl $60, %%eax\n\t"
        "xorl %%edi, %%edi\n\t"
        "syscall\n\t"
        "ud2\n\t"
        "1:\n\t"
        : "+a"(r_rax)
        : "r"(r_rdi), "r"(r_rsi), "r"(r_rdx), "r"(r_r10), "r"(r_r8),
          [spitze] "r"((long)spitze), [fn] "r"(fn)
        : "memory", "rcx", "r11", "cc");
    r = r_rax;
    if (r < 0) {
        long e = -r;
        return e > 4095 ? 12 : (int)e; /* ENOMEM where the number is wild. */
    }
    *wort = (uint32_t)r;
    return 0;
}

void gabbro_faden_warte(uint32_t *wort)
{
    for (;;) {
        uint32_t v = __atomic_load_n(wort, __ATOMIC_ACQUIRE);
        long r;
        if (v == 0u) {
            return;
        }
        /* FUTEX_WAIT blocks only while the word still holds the seen value:
         * a clear racing the load fails with EAGAIN, a spurious wake simply
         * re-loops. Both paths re-read -- the loop never trusts the wait. */
        r = roh_aufruf(GABBRO_SYS_FUTEX, (long)wort, GABBRO_FUTEX_WAIT, v, 0, 0, 0);
        (void)r;
    }
}
