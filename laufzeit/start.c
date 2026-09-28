/* laufzeit/start.c -- the HAND-WRITTEN hosted driver for one concurrent unit,
 * kept as the second implementation the generated one is read against.
 *
 * WHAT THIS IS. The emitter translates each `concurrent` member to a plain
 * `static void f(void)` and emits NO caller and NO `main` -- measured
 * 2026-09-15 on `beispiele/124-two-threads-private.gab` (`hauptA`, `hauptB`
 * exist, nobody calls them). This file is the missing half: it starts exactly
 * the declared roots, one thread each, and parks everything else in the idle
 * root. Together with the emitted unit it is a runnable program.
 *
 * WHY A .c FILE AND NOT EMITTED C. Thread creation is the runtime's, not the
 * program's: the goal theorem books it as assumption (d) `Laufzeit`
 * (`grammatik/Grammatik/Zielsatz/Spec.lean`), and `E.P.mitRuhe` is the model
 * of exactly this split -- the declared starts on their threads, the idle
 * root `none` on every other thread. A generator that printed `main` into the
 * unit would move a runtime fact into the program text.
 *
 * BUILD (from the tree root; the emitted file is a build artefact, not source):
 *
 *   target/debug/gabbro emit beispiele/124-two-threads-private.gab > .tmp/einheit124.c
 *   cc -std=c11 -O0 -Wall -Wextra -Werror -pthread -I .tmp -I laufzeit \
 *      -DEINHEIT_INCLUDE='"einheit124.c"' -o .tmp/start124 laufzeit/start.c \
 *      bibliothek/linux/linux.c
 *   .tmp/start124            # exit 0
 *
 * TWO THINGS MOVED OUT OF THIS FILE, both on 2026-09-28 (TODO section 0e K8).
 *
 * (1) **Every operating-system call.** Threads, the lock and the words of a
 * failure go through `laufzeit/bindung.h`, which the PROGRAM defines -- the same
 * move `crates/gabbro-cli/src/treiber.rs` made for the GENERATED driver, and for
 * the same reason: no OS call is hard-wired in any runtime. This file is linked
 * by no program at all today (the generated driver replaced it everywhere
 * `gabbro build` runs), which is precisely why the measurement that found it is
 * the SOURCE-level stage of `instrumente/pruefe-os-bindung.sh` and not the
 * symbol one -- *a file nothing links is measured by nothing.*
 *
 * (2) **The observation.** What the run PRINTS is the test's business, not the
 * runtime's, and it used to stand at the end of `main` here. It is appended at
 * the `NACHLAUF` marker now, exactly as the generated driver's is
 * (`crates/gabbro-cli/tests/treiber.rs`, `BEOBACHTUNG_124`) -- so the hand run
 * and the generated run now share the observation text character for character,
 * and what differs between them is only what this file is about.
 *
 * WHY `-DEINHEIT_INCLUDE`. The driver is one file for every unit; only the
 * included artefact and the ROOTS section below change per unit. A `#include`
 * (rather than a second translation unit) because the emitted roots are
 * `static`: a separate TU could not name them, and making them non-static
 * would widen the unit's interface for the driver's sake.
 */

/* -- The names this driver calls and does not define -------------------- */

#include "bindung.h"

/* -- The emitted unit -------------------------------------------------- */

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
 * WHY A MUTEX AND NOT A SPINLOCK. The critical sections are whole Gabbro
 * bodies (`setze`), not single instructions; spinning under contention would
 * burn the core the lock holder needs. Blocking is the honest hosted shape --
 * and WHICH blocking object it is is the binding's business since K8: the blob
 * below is words, and `bibliothek/linux/linux.c` lays a `pthread_mutex_t` into
 * it and asserts that it fits.
 */
static uint64_t sperre_L[GABBRO_OS_SPERRE_WORTE];

void L_nimm(void)
{
    gabbro_os_sperre_nimm((uint64_t)(uintptr_t)sperre_L);
}

void L_gib(void)
{
    gabbro_os_sperre_gib((uint64_t)(uintptr_t)sperre_L);
}

/* -- ROOTS: the declared starts of `beispiele/124-two-threads-private.gab`.
 *
 * Source line 84:  concurrent { hauptA, hauptB };
 *
 * WHY THIS SECTION EXISTS IN THIS FORM. The decisive property is measurable:
 * the driver starts EXACTLY the roots the unit declares -- not more, not
 * fewer, not in a different shape. The pin is mechanical and lives outside
 * this file: the probe extracts `concurrent { ... }` from the `.gab` source
 * and the `pthread_create` set from this file and compares the two lists
 * (see the report for the one-liner and its output). A new root in the source
 * without a new thread here -- or a thread here for a root the source dropped
 * -- fails that comparison. Reviewing this section means diffing two words.
 *
 * WHY NO WRAPPER PER ROOT ANY MORE. `pthread_create` wants `void *(*)(void *)`
 * and the emitted roots are `void (*)(void)`, so one adapter per root used to
 * stand here. The POSIX signature is the binding's since K8, and its adapter
 * with it -- so the root's own NAME stands at the start site, unwrapped, which
 * is what the probe reads. The GENERATED driver made the same move on the same
 * day, and the two files still read against each other line for line.
 */

/* N_WURZELN is the count the probe checks against the source's list length:
 * adding a thread without bumping it breaks the join loop below loudly
 * (a thread never joined is a leak the next reader has to explain). */
#define N_WURZELN 2

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
 * park: `main` spawns exactly the declared roots and joins them. **So it is
 * GONE since K8** -- it spun on `pause()`, which is an operating-system call,
 * and keeping it would have meant binding a primitive nothing on this side ever
 * calls. Bare metal parks its spare cores inside its own runtime
 * (`laufzeit/metall/kern.c`) and never read this function; the generated driver
 * dropped its copy on the same day.
 */

/* -- main: start exactly the roots and join them. -------------------------- */

int main(void)
{
    /* WHY AN ARRAY AND NOT TWO VARIABLES. The join loop must cover exactly
     * the spawned set; an array sized by N_WURZELN makes "spawned but never
     * joined" a size mismatch instead of a forgotten line. */
    static uint64_t faden[N_WURZELN][GABBRO_OS_FADEN_WORTE];
    uint32_t rc;

    gabbro_os_sperre_init((uint64_t)(uintptr_t)sperre_L);

    rc = gabbro_os_faden_start((uint64_t)(uintptr_t)faden[0], (uint64_t)(uintptr_t)hauptA);
    if (rc != 0) {
        gabbro_os_melden(GABBRO_OS_M_START, 0, rc);
        return 2;
    }
    rc = gabbro_os_faden_start((uint64_t)(uintptr_t)faden[1], (uint64_t)(uintptr_t)hauptB);
    if (rc != 0) {
        gabbro_os_melden(GABBRO_OS_M_START, 1, rc);
        (void)gabbro_os_faden_warte((uint64_t)(uintptr_t)faden[0]);
        return 2;
    }
    for (int i = 0; i < N_WURZELN; i++) {
        rc = gabbro_os_faden_warte((uint64_t)(uintptr_t)faden[i]);
        if (rc != 0) {
            gabbro_os_melden(GABBRO_OS_M_WARTE, (uint64_t)i, rc);
            return 2;
        }
    }

    /* WHAT USED TO STAND HERE, and where it went. The run printed
     * `konto=%u konto=%u privA=%u privA=%u privB=%u` and then asserted the lock
     * invariant (`konto[0] == konto[1]`, whose VALUE is schedule-dependent and
     * whose EQUALITY is not) and the two private slots (7, 7 and 5, which are
     * deterministic: a deviation is a lost write and not a schedule). That text
     * is the TEST's, it names carriers of one example, and printing is an
     * operating-system call -- all three say the same thing about where it
     * belongs. It is `BEOBACHTUNG_124` in `crates/gabbro-cli/tests/treiber.rs`
     * now, appended at the marker below at run time and to the generated driver
     * at its own, so both artefacts carry the identical observation -- and the
     * marker is spelt to the letter as the generator writes it, because the
     * test looks for one string and not for two. */
    /* NACHLAUF: unit-specific observation goes here in test runs. */
    return 0;
}
