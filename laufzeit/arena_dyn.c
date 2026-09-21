/* laufzeit/arena_dyn.c -- hosted-POSIX half of `arena_dyn.h` (wave D).
 *
 * This is the ONLY file of the tree (besides its header's declarations)
 * that may name OS memory calls. Everything above this file speaks counts;
 * everything below it is pages. The bare-metal spelling replaces this file
 * alone (page-table/MPU setup behind the same two signatures); no caller
 * changes, because no caller names a page.
 */

#include "arena_dyn.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>

/* The commit granularity is the OS page, read once per process. It never
 * crosses the interface: the descriptor counts slots, this file rounds to
 * pages internally. */
static long seiten_groesse(void)
{
    static long cached = 0;
    if (cached == 0) {
        cached = sysconf(_SC_PAGESIZE);
        if (cached <= 0) {
            fprintf(stderr,
                "gabbro: arena runtime: sysconf(_SC_PAGESIZE) failed\n");
            abort();
        }
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
    void *base;

    if (d == NULL || d->base != NULL || d->max == 0 || d->elem == 0 ||
            d->floor_hi > d->max) {
        /* A descriptor the emitter misbuilt is a broken handoff, not a
         * small range: fail-stop at load, before any start runs. */
        fprintf(stderr,
            "gabbro: arena reserve refused: bad descriptor "
            "(max=%u floor=%u elem=%u)\n",
            d ? d->max : 0, d ? d->floor_hi : 0, d ? d->elem : 0);
        exit(GABBRO_ARENA_EXIT_RESERVE);
    }
    span = slot_bytes(d->max, d->elem);
    if (span == 0) {
        fprintf(stderr,
            "gabbro: arena reserve refused: max=%u elem=%u overflows size_t\n",
            d->max, d->elem);
        exit(GABBRO_ARENA_EXIT_RESERVE);
    }
    base = mmap(NULL, span, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) {
        /* OOM at load is fail-stop with a named exit, never a silent NULL:
         * there is no program running yet to take an `else` branch. */
        fprintf(stderr,
            "gabbro: arena reserve refused: cannot reserve %u slots "
            "(exit %d)\n",
            d->max, GABBRO_ARENA_EXIT_RESERVE);
        exit(GABBRO_ARENA_EXIT_RESERVE);
    }
    d->base = base;
    d->used = 0;
    d->committed = 0;
    /* Commit the floor now, so the first `hi` slots are usable storage
     * before the first statement runs. A floor that will not commit is a
     * load refusal for the same reason a range that will not reserve is. */
    if (d->floor_hi > 0 && !gabbro_arena_grow(d, d->floor_hi)) {
        fprintf(stderr,
            "gabbro: arena reserve refused: cannot commit floor %u "
            "(exit %d)\n",
            d->floor_hi, GABBRO_ARENA_EXIT_RESERVE);
        exit(GABBRO_ARENA_EXIT_RESERVE);
    }
    d->committed = d->floor_hi;
}

bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)
{
    uint64_t neu;
    size_t von, bis, seite, start, ende;
    char *basis;

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
        fprintf(stderr,
            "gabbro: arena grow refused: %u committed + %u past max %u\n",
            d->committed, n, d->max);
        abort();
    }
    /* Round the new span to whole pages: commit is monotone, so only the
     * not-yet-committed tail needs protection change. */
    seite = (size_t)seiten_groesse();
    von = (size_t)d->committed * (size_t)d->elem;
    bis = (size_t)neu * (size_t)d->elem;
    start = (von / (size_t)seite) * (size_t)seite;
    ende = ((bis + (size_t)seite - 1) / (size_t)seite) * (size_t)seite;
    basis = (char *)d->base;
    if (mprotect(basis + start, ende - start, PROT_READ | PROT_WRITE) != 0) {
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
