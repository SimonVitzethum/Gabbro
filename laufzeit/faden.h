/* laufzeit/faden.h -- raw-clone threads for runtime `start` (lane 260).
 *
 * WHAT THIS IS. The thread half of `start { f, g };` that the emitter calls
 * into: one raw `clone` per root on a stack the UNIT owns, and a join of all
 * of them. The C the emitter writes never names `pthread_create`, the glibc
 * `clone()` wrapper or `fork` on these paths -- Simon's rule: threads at run
 * time are made by OUR OWN code issuing the kernel system call.
 *
 * WHAT IT IS NOT. Boot-declared `concurrent` starts keep their hosted driver
 * (`laufzeit/start_pool.c`, pthreads): that is not "at run time", it is the
 * machine coming up. This file is only ever entered from a running Gabbro
 * function, through the `start` statement the emitter lowered.
 *
 * MACHINE. x86_64 Linux only, like the syscall stub (`emit.rs`,
 * `syscall_stumpf`). Every number below is the kernel's, read from the
 * architecture's ABI, never from libc headers: the point is that no libc
 * threading symbol stands between this file and the kernel (measured with
 * `nm`: no `pthread_*`, no `clone`, no `__errno_location` in the object).
 */
#ifndef GABBRO_FADEN_H
#define GABBRO_FADEN_H

#include <stdint.h>

/* One raw-clone thread per call.
 *
 * `fn` is a nullary root (what `N458` admits: no parameters, no result).
 * `spitze` is the TOP of a stack the unit owns -- emitter static, 16-byte
 * aligned, 64 KiB by default -- and `wort` is the join word: zero before the
 * call, the child's TID while it runs, zero again once it has exited (the
 * kernel clears it for `CLONE_CHILD_CLEARTID` and wakes the waiter).
 *
 * Returns 0 when the thread runs, a positive errno number when `clone`
 * refused (ENOMEM when the kernel is out of tasks, ENOSYS where there is no
 * kernel behind the instruction). There is no error CHANNEL here -- the
 * `start` statement carries none -- so the emitter turns a nonzero answer
 * into a trap, loudly, instead of running on with unstarted roots.
 */
int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort);

/* Wait until the thread behind `wort` has exited. Returns only then; every
 * write the thread made is visible afterwards (the wait loads the cleared
 * word with acquire semantics -- the synchronizes-with edge of the join).
 */
void gabbro_faden_warte(uint32_t *wort);

#endif
