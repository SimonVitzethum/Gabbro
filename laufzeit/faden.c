/* laufzeit/faden.c -- threads for a run-time `start` (lane 260; the OS half
 * moved out to the program on 2026-09-28, TODO section 0e K8).
 *
 * SIMON'S RULE, AS CODE. Threads at run time are made by the PROGRAM'S OWN code
 * -- not by libc (`pthread_create`, the glibc `clone()` wrapper, `fork`), and
 * since K8 not by this file either. What stood here until then was the kernel
 * system call itself, in inline assembly: `clone` (56) on a stack the unit owns,
 * the child's `exit` (60), and `futex` (202) for the wait. **Three `syscall`
 * instructions, and they left no undefined symbol at all** -- which is why the
 * measurement counts SITES for them (`instrumente/pruefe-os-bindung.sh`,
 * `MARKE_ROHRUF`): a runtime that had merely hidden its Linux dependency in asm
 * would pass a symbol stage untouched.
 *
 * They are the program's now (`laufzeit/bindung.h`: `gabbro_os_klon`,
 * `gabbro_os_wort_warte`; `bibliothek/linux/linux.c` carries the Linux bodies
 * with the whole of the reckoning that used to stand in this header -- the clone
 * flags one by one, the register convention, and why the child must not execute
 * a C frame on the new stack). **What is left here is what is the RUNTIME's, and
 * it is not nothing:**
 *
 *   * WHAT A JOIN WORD MEANS, which is the contract the emitter's C rests on:
 *     zero before the start, nonzero while the root runs, zero again when it has
 *     ended. The binding promises the ORDER (`bindung.h`); this file is what
 *     reads it;
 *   * THE VALIDITY CHECKS a start must pass before any primitive is asked: no
 *     null root, stack or word, and a stack top that is 16-byte aligned --
 *     because the SysV ABI wants `rsp` 16-aligned before a call and the thread
 *     CALLS the root on it. A binding cannot be asked to check this: by the time
 *     it has the number, a misaligned stack is already its caller's mistake;
 *   * THE JOIN ITSELF, which is a LOOP and not a wait: the word is re-read with
 *     acquire semantics until it is zero, and the wait in between is allowed to
 *     return at any time. A clear racing the load, a spurious wake, a wait that
 *     refuses -- every path re-reads. *The loop never trusts the wake*, and that
 *     is the runtime's reasoning about a primitive whose promise is deliberately
 *     weak.
 *
 * THE ACQUIRE EDGE. The binding's clear is the release half, so everything the
 * thread wrote is visible when this loop reads zero -- that edge is the TSan-free
 * design argument for the join word (the unit's own carriers rest on `N462`:
 * guarded, atomic or per-core, decided by the checker, not here).
 *
 * NO `errno`, and no libc header: this file includes `faden.h` and
 * `bindung.h` and nothing else. `nm` on the object names no `pthread_*`, no
 * `clone`, no `__errno_location` -- and since K8 no `syscall` instruction either.
 */

#include "faden.h"

/* The names this file calls and does not define. `bibliothek/linux/linux.c` is
 * the binding a hosted program takes off the shelf; a different operating system
 * gets a different body, not a different runtime. */
#include "bindung.h"

int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort)
{
    if (fn == 0 || spitze == 0 || wort == 0) {
        return 22; /* EINVAL: a null root, stack or word starts nothing. */
    }
    if (((uintptr_t)spitze & 15u) != 0u) {
        return 22; /* EINVAL: the SysV ABI wants rsp 16-aligned before a
                    * call, and the thread below calls the root. */
    }
    /* NO store into `*wort` here, and that absence is load-bearing: the binding
     * writes the id BEFORE the thread can run (`bindung.h`, the first of the
     * three promises), and the thread may already have ended and had the word
     * cleared by the time this returns -- a store now would resurrect a dead
     * one. *Measured on Linux in 2026-09-26, when the store stood here: 200000
     * start/join rounds hung before round 20000.* */
    return (int)gabbro_os_klon((uint64_t)(uintptr_t)fn,
                               (uint64_t)(uintptr_t)spitze,
                               (uint64_t)(uintptr_t)wort);
}

void gabbro_faden_warte(uint32_t *wort)
{
    for (;;) {
        uint32_t v = __atomic_load_n(wort, __ATOMIC_ACQUIRE);
        if (v == 0u) {
            return;
        }
        /* The wait is allowed to return at any time -- because it did not
         * block, because the word changed, or for no reason at all. The loop
         * re-reads either way, so the only thing this call buys is that a long
         * wait does not spin. An atomic load is not an operating-system call
         * and stays here; the wait is one and does not. */
        gabbro_os_wort_warte((uint64_t)(uintptr_t)wort, v);
    }
}
