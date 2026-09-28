/* laufzeit/start_pool.c -- the hosted runtime driver for a symmetric pool.
 *
 * WHAT THIS IS. One routine on N threads: the C half of `concurrent { f, f }`
 * (lane 245). The emitter translates each `concurrent` member to a plain
 * `static` function and emits NO caller and NO `main` -- and for a duplicate
 * member it still emits exactly ONE definition (measured on the lane's demo
 * unit: a single `static void arbeiter(void)` for `concurrent
 * { arbeiter, arbeiter }`). This file is the missing half: it starts the one
 * declared routine on N threads and parks everything else in the idle root.
 * Together with the emitted unit it is a runnable program.
 *
 * WHY A .c FILE AND NOT EMITTED C. Thread creation is the runtime's, not the
 * program's: the goal theorem books it as assumption (d) `Laufzeit`
 * (`grammatik/Grammatik/Zielsatz/Spec.lean`), and `E.P.mitRuhe` is the model
 * of exactly this split -- the declared starts on their threads, the idle
 * root `none` on every other thread. A generator that printed `main` into the
 * unit would move a runtime fact into the program text.
 *
 * PARAMETERIZATION (no hardcoded unit names). Everything unit-specific
 * arrives as `-D` flags; this file names no table, no lock, and no routine:
 *
 *   cc -std=c11 -O0 -Wall -Wextra -Werror -pthread -I .tmp \
 *      -DEINHEIT_INCLUDE='"poolunit.c"' \
 *      -DPOOL_FN=arbeiter -DPOOL_N=4 -DPOOL_SPERRE=L \
 *      -DPOOL_PRUEFE=pruefe -DPOOL_ERWARTET=30 \
 *      -o .tmp/startpool laufzeit/start_pool.c
 *   .tmp/startpool            # exit 0 on a clean run
 *
 *   EINHEIT_INCLUDE -- the emitted unit (see `laufzeit/start.c` for why a
 *     `#include` and not a second translation unit: the emitted roots are
 *     `static`).
 *   POOL_FN -- the one routine to run on every thread.
 *   POOL_N -- the thread count (at least 1). It MUST equal the number of
 *     times the unit's `concurrent` sets name POOL_FN: assumption (d)
 *     (`Laufzeit`) is the DECLARED start list, and the checker judged exactly
 *     that many starts. N is not a runtime choice -- a run with more threads
 *     than declared is outside what was checked (review G06 F6; the lane-245
 *     report's "N is a runtime choice" is corrected in its erratum). The
 *     generated driver of `gabbro build` starts one thread per declared
 *     occurrence since fix lane F4 and needs no such flag.
 *   POOL_SPERRE -- the unit's lock: provides `POOL_SPERRE_nimm/gib`, the two
 *     symbols the emitter declares per lock. One lock is the shape every
 *     measured pool unit has; a unit with several locks extends the SPERRE
 *     block below line by line, the same way `start.c` grows its ROOTS.
 *   POOL_PRUEFE (optional) -- a nullary unit function returning `unsigned`;
 *     after the join the driver calls it and expects POOL_ERWARTET. It is
 *     how a unit reports its own result without the driver naming a table:
 *     the value check stays in the program, the thread management here.
 *     Without it the driver only proves the pool ran to completion. It is
 *     called WITH the lock held (fix lane F4): declare it `requires Held(L)`
 *     and let it take no lock itself -- the hosted lock is a plain mutex, and
 *     a check function that takes it again would wait for itself.
 *
 * THE PIN. The decisive property is measurable: the driver starts EXACTLY
 * POOL_N threads on the routine the unit's `concurrent` set declares. The
 * mechanical check lives outside this file: extract the routine name and
 * the member count from the `.gab` source's `concurrent { ... }` line and
 * compare them against the `-DPOOL_FN=` and `-DPOOL_N=` flags of the build
 * recipe (see the lane report for the one-liner and its output).
 */

/* **Every operating-system call in this file is the PROGRAM's** (2026-09-28,
 * TODO section 0e K8): threads, the lock and the words of a failure go through
 * `laufzeit/bindung.h`, which declares them and defines none, and
 * `bibliothek/linux/linux.c` is the binding a program takes off the shelf. The
 * hand driver `start.c` and the GENERATED driver
 * (`crates/gabbro-cli/src/treiber.rs`) made the same move on the same day.
 *
 * This file is compiled by nothing in the tree today -- which is exactly why the
 * measurement that found its seven OS names is the SOURCE-level stage of
 * `instrumente/pruefe-os-bindung.sh` and not the symbol one. *A file nothing
 * links is measured by nothing.* */
#include "bindung.h"

/* -- The switches the recipe owes. ---------------------------------------- */

#ifndef EINHEIT_INCLUDE
#error "start_pool: -DEINHEIT_INCLUDE='\"unit.c\"' names the emitted unit"
#endif
#ifndef POOL_FN
#error "start_pool: -DPOOL_FN=<routine> names the one routine to run"
#endif
#ifndef POOL_N
#error "start_pool: -DPOOL_N=<count> sizes the pool"
#endif
#if POOL_N < 1
#error "start_pool: POOL_N counts threads -- at least 1"
#endif
#ifndef POOL_SPERRE
#error "start_pool: -DPOOL_SPERRE=<lock> provides the lock primitives"
#endif

/* -- The emitted unit ----------------------------------------------------- */

#include EINHEIT_INCLUDE

/* -- Lock primitives: the emitter declares them, the runtime defines them.
 *
 * WHY HERE. The emitted C only ever says `void L_nimm(void);` -- a lock is a
 * runtime object (futex, ticket lock, interrupt mask), never program text.
 * On hosted POSIX that object is a mutex; on bare metal it would be the
 * ticket lock of NICHTINTERFERENZ.md section 10. The name on each side is the
 * contract between them, and it is checked by `cc`, not by care: a misspelt
 * name is an undefined reference, not a silent default.
 *
 * WHY PASTING AND NOT A PLAIN NAME. The driver must define exactly the two
 * symbols the unit's lock declares, and the lock's name arrives as a flag.
 * A flag does not expand inside a pasting without the two-level helper
 * below -- `VERKLEBE(POOL_SPERRE, _nimm)` with `-DPOOL_SPERRE=L` defines
 * `L_nimm`, anything else is a compile error at once.
 */
#define VERKLEBE_(A, B) A ## B
#define VERKLEBE(A, B) VERKLEBE_(A, B)
#define SPERRE_NIMM VERKLEBE(POOL_SPERRE, _nimm)
#define SPERRE_GIB VERKLEBE(POOL_SPERRE, _gib)

/* The storage is this driver's, the operations are the program's: the blob is
 * words and `bibliothek/linux/linux.c` lays its own mutex into it with a
 * `_Static_assert` that it fits. A refused acquire fail-stops there, because a
 * driver has no `else` at a lock it must hold. */
static uint64_t sperre_einzig[GABBRO_OS_SPERRE_WORTE];

void SPERRE_NIMM(void)
{
    gabbro_os_sperre_nimm((uint64_t)(uintptr_t)sperre_einzig);
}

void SPERRE_GIB(void)
{
    gabbro_os_sperre_gib((uint64_t)(uintptr_t)sperre_einzig);
}

/* -- The pool: N threads on one routine.
 *
 * WHY NO WRAPPER AT ALL ANY MORE. `pthread_create` wants `void *(*)(void *)`
 * and the emitted root is `void (*)(void)`, so an adapter used to stand here.
 * The POSIX signature is the binding's since K8 and its adapter with it, so the
 * root travels to the start site as its own name -- here through `-DPOOL_FN=`,
 * since all N threads run the one routine. A declared start takes no argument
 * (`E.starts` carries each root's `Env`, here empty), and no slot pretends
 * otherwise.
 */

/* -- The idle root: `none` of `E.P.mitRuhe`.
 *
 * WHY IT LOOPS FOREVER. The model's idle root body is `return` -- it writes
 * nothing -- but a HOSTED thread that returns from its start routine simply
 * ends, while a parked core must stay parked: on bare metal this loop is a
 * `wfi` wait, and a thread that fell out of it would run into whatever bytes
 * follow, which is exactly the "thread runs what nobody declared" shape (d)
 * forbids. Spinning here touches no Gabbro carrier (no table, no lock, no
 * global), so it is invisible to every leg of `Ziel`.
 *
 * WHY IT IS NEVER SPAWNED ON HOSTED. POSIX gives `main` no spare cores to
 * park: `main` spawns exactly the declared pool and joins it. **So it is GONE
 * since K8** -- it spun on `pause()`, which is an operating-system call, and
 * keeping it would have meant binding a primitive nothing on this side ever
 * calls. Bare metal parks its spare cores inside its own runtime
 * (`laufzeit/metall/kern.c`) and never read this function.
 */

/* -- main: start the pool, join it, ask the unit what happened. ----------- */

int main(void)
{
    /* WHY AN ARRAY AND NOT N VARIABLES. The join loop must cover exactly
     * the spawned set; an array sized by POOL_N makes "spawned but never
     * joined" a size mismatch instead of a forgotten line. */
    static uint64_t faden[POOL_N][GABBRO_OS_FADEN_WORTE];
    uint32_t rc;

    gabbro_os_sperre_init((uint64_t)(uintptr_t)sperre_einzig);

    for (int i = 0; i < POOL_N; i++) {
        rc = gabbro_os_faden_start((uint64_t)(uintptr_t)faden[i],
                                   (uint64_t)(uintptr_t)POOL_FN);
        if (rc != 0) {
            gabbro_os_melden(GABBRO_OS_M_START, (uint64_t)i, rc);
            /* WHY JOIN HERE (fix lane F4, review G06 F6). Threads 0..i-1 are
             * already running; returning at once would leave them behind the
             * exit, and "the join covers exactly the spawned set" would be
             * false on exactly the path that fails. */
            for (int j = 0; j < i; j++) {
                (void)gabbro_os_faden_warte((uint64_t)(uintptr_t)faden[j]);
            }
            return 2;
        }
    }
    for (int i = 0; i < POOL_N; i++) {
        rc = gabbro_os_faden_warte((uint64_t)(uintptr_t)faden[i]);
        if (rc != 0) {
            gabbro_os_melden(GABBRO_OS_M_WARTE, (uint64_t)i, rc);
            return 2;
        }
    }

#ifdef POOL_PRUEFE
    /* WHAT IS CHECKED. The unit reports its own result through a nullary
     * function it provides for exactly this purpose (naming no table on
     * this side): the driver only compares against the expected value from
     * the recipe. Which value is deterministic is the unit's business -- a
     * pool whose threads all write the same value under the lock observes
     * that value afterwards on every schedule; a schedule-dependent value
     * belongs in the lock invariant, not in this comparison. */
    {
        /* WHY UNDER THE LOCK (fix lane F4, review G06 F6). The unit's check
         * function reads the guarded carrier, and the lane's demo declares it
         * `requires Held(L)`. After the joins nobody else runs, so there is
         * no race either way -- but the driver is a caller like any other and
         * keeps the callee's contract instead of relying on the moment. */
        SPERRE_NIMM();
        unsigned gesehen = POOL_PRUEFE();
        SPERRE_GIB();
        /* **The comparison stays, the WORDS go** (K8): printing is an
         * operating-system call and a driver has none of its own. The code and
         * its two numbers say the same thing, and the program's binding is
         * where the sentence lives. */
        gabbro_os_melden(GABBRO_OS_M_WARTE, (uint64_t)gesehen,
                         (uint64_t)(unsigned)POOL_ERWARTET);
        if (gesehen != (unsigned)POOL_ERWARTET) {
            return 1;
        }
    }
#endif

    return 0;
}
