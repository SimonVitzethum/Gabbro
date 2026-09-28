/* laufzeit/arena_dyn.c -- hosted-POSIX half of `arena_dyn.h` (wave D).
 *
 * This was the ONLY file of the tree (besides its header's declarations) that
 * named OS memory calls. Everything above this file speaks counts; everything
 * below it is pages. The bare-metal spelling replaces this file alone
 * (page-table/MPU setup behind the same two signatures); no caller changes,
 * because no caller names a page.
 *
 * **AND SINCE K8 THIS FILE CALLS NO OPERATING-SYSTEM FUNCTION** (server lane,
 * TODO section 0e, Simon 2026-09-28: *"an die Hardware ist OK, OS nicht, das
 * muss selbst gemacht werden"*). It asked `mmap` for the reservation, `mprotect`
 * for each commit and `sysconf` for the page size, and printed its fail-stops
 * with `fprintf` before `exit`/`abort` -- six of the twelve OS names the hosted
 * runtime chose for the program (measured: `instrumente/pruefe-os-bindung.sh`).
 * All six are the program's now: `gabbro_os_reserve`, `gabbro_os_commit`,
 * `gabbro_os_seitengroesse`, `gabbro_os_melden` and `gabbro_os_ende`, declared
 * in `laufzeit/bindung.h`, defined by whoever wrote the declaration --
 * `bibliothek/linux/` for a program that wants the usual POSIX ones.
 *
 * *What did not change is one line of the arithmetic below, and that is the
 * point:* the ceiling, the page rounding, the monotone commit and refuse-on-full
 * are the runtime's reasoning; the mapping primitive is the program's choice.
 * The same move `laufzeit/kmodul/arena.c` made under K7, in the same order, so
 * that the three flavours of one header stay readable against each other.
 *
 * A FAIL-STOP IS WRITTEN AS IF `gabbro_os_ende` MIGHT RETURN, and it must not.
 * The declaration cannot say `_Noreturn` (it is the program's ordinary
 * `extern fn`, and the emitted prototype meets this one in a single translation
 * unit), so every call site below carries the fail-closed line behind it: the
 * reservation returns with `base` still null, `grow` returns false. A binding
 * whose body returned therefore leaves the caller in the `else` it wrote, and
 * never in a program that ran on past a stop.
 */

#include "arena_dyn.h"
#include "bindung.h"

/* The commit granularity is the OS page, asked of the program's binding once
 * per process. It never crosses the interface upwards: the descriptor counts
 * slots, this file rounds to pages internally -- and the binding answers the
 * page SIZE, never where a page begins. A binding that cannot answer is a
 * fail-stop and not a guess: a wrong granularity would make every commit a
 * partial one. */
static size_t seiten_groesse(void)
{
    static size_t cached = 0;
    if (cached == 0) {
        uint64_t s = gabbro_os_seitengroesse();
        if (s == 0 || (uint64_t)(size_t)s != s) {
            gabbro_os_melden(GABBRO_OS_M_SEITE, s, 0);
            gabbro_os_ende(GABBRO_OS_ENDE_ABBRUCH);
            return 0;
        }
        cached = (size_t)s;
    }
    return cached;
}

/* Slot bytes for `slots` slots of `elem` bytes, or zero on overflow. The
 * ceiling is namable (`M <= u32::MAX`, the `used`/`committed` counters stay
 * 32-bit), but `max * elem` still has to fit `size_t`: a declaration the
 * checker accepted can still outgrow a 32-bit address space, and that is a
 * load refusal, not undefined arithmetic. */
static size_t slot_bytes(uint32_t slots, uint32_t elem)
{
    size_t out = (size_t)slots * (size_t)elem;
    if (elem != 0 && out / elem != slots) {
        return 0;
    }
    return out;
}

void gabbro_arena_reserve(gabbro_arena_desc *d)
{
    size_t span;
    uint64_t base;

    if (d == NULL || d->base != NULL || d->max == 0 || d->elem == 0 ||
            d->floor_hi > d->max) {
        /* A descriptor the emitter misbuilt is a broken handoff, not a
         * small range: fail-stop at load, before any start runs. */
        gabbro_os_melden(GABBRO_OS_M_DESKRIPTOR,
                         d ? d->max : 0u, d ? d->floor_hi : 0u);
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);
        return;
    }
    span = slot_bytes(d->max, d->elem);
    if (span == 0) {
        gabbro_os_melden(GABBRO_OS_M_SPANNE, d->max, d->elem);
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);
        return;
    }
    base = gabbro_os_reserve((uint64_t)span);
    if (base == 0) {
        /* OOM at load is fail-stop with a named exit, never a silent NULL:
         * there is no program running yet to take an `else` branch. The
         * binding answers 0 for a refusal, which is why a mapping at address
         * 0 is not a case: no hosted mapping is placed there, and one that
         * was would be indistinguishable from the refusal either way. */
        gabbro_os_melden(GABBRO_OS_M_RESERVE, d->max, (uint64_t)span);
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);
        return;
    }
    d->base = (void *)(uintptr_t)base;
    d->used = 0;
    d->committed = 0;
    /* Commit the floor now, so the first `hi` slots are usable storage
     * before the first statement runs. A floor that will not commit is a
     * load refusal for the same reason a range that will not reserve is. */
    if (d->floor_hi > 0 && !gabbro_arena_grow(d, d->floor_hi)) {
        gabbro_os_melden(GABBRO_OS_M_BODEN, d->floor_hi, 0);
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);
        return;
    }
    d->committed = d->floor_hi;
}

bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)
{
    uint64_t neu;
    size_t von, bis, seite, start, ende;
    uint64_t basis;

    if (d == NULL || d->base == NULL) {
        return false;
    }
    if (n == 0) {
        return true;
    }
    /* The ceiling is checkable: past `max` there is no commit, only the
     * fail-stop. Since fix lane F2 (2026-09-21) the checker's `N426` holds
     * every `grow` against the UPPER bound of what the whole run may have
     * committed (every path, loop pass, call and root counted; a loop
     * without a constant bound or a recursion refused), so an accepted
     * unit reaches this abort only outside the checked run model: a routine
     * entered more than once per load by something the unit does not see
     * (a separately linked caller), or a descriptor the emitter misbuilt.
     * It stays a stop, never a partial commit. */
    neu = (uint64_t)d->committed + (uint64_t)n;
    if (neu > d->max) {
        gabbro_os_melden(GABBRO_OS_M_UEBER_MAX, neu, d->max);
        gabbro_os_ende(GABBRO_OS_ENDE_ABBRUCH);
        return false;
    }
    /* Round the new span to whole pages: commit is monotone, so only the
     * not-yet-committed tail needs protection change. */
    seite = seiten_groesse();
    von = (size_t)d->committed * (size_t)d->elem;
    bis = (size_t)neu * (size_t)d->elem;
    start = (von / seite) * seite;
    ende = ((bis + seite - 1) / seite) * seite;
    basis = (uint64_t)(uintptr_t)d->base;
    if (gabbro_os_commit(basis, (uint64_t)start, (uint64_t)(ende - start)) != 0) {
        /* The platform refused the commit below the ceiling: `committed`
         * unchanged, the caller runs `else`.
         *
         * WHEN THIS BRANCH IS TAKEN (review G08 F3, fix lane F2). On Linux
         * with the default overcommit heuristic (`vm.overcommit_memory` 0)
         * or with overcommit always on (1), `mprotect` to writable on a
         * private anonymous mapping does not reserve physical memory and
         * practically always succeeds; out of memory then shows up LATER,
         * at the first touch of a page, as the OOM killer (SIGKILL) -- not
         * as `false` here, and not as the program's `else`. Only under
         * strict accounting (`vm.overcommit_memory` 2), where making the
         * range writable is charged against the commit limit, does an
         * exhausted limit fail this call with ENOMEM and reach the `else`.
         * The `else` is therefore the runtime's answer to a REFUSED commit,
         * not a guarantee that out-of-memory is always reported to the
         * program; no test here exercises this branch. */
        return false;
    }
    /* No scrub, and no touch: the commit stays lazy. The bytes
     * `[von, bis)` were never writable before this call (the region was
     * reserved `PROT_NONE`, and commit is monotone: nothing is ever made
     * inaccessible again), and a private anonymous mapping reads as zero
     * until written -- so the new slots read as zero without a store. Up to
     * 2026-09-21 a `memset` here touched every new page at once, which made
     * every commit eager and moved an overcommit OOM kill into this call. */
    d->committed = (uint32_t)neu;
    return true;
}
