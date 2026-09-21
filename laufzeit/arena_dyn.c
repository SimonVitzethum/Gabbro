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
#include <string.h>
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
     * fail-stop. The checker's `N426` refuses the straight-line shape only:
     * it holds the ceiling against the path's committed LOWER bound, so a
     * `grow` in a loop, after a branch that grew, or spread over several
     * functions can arrive here from an accepted program (review G08,
     * 2026-09-21). Until the checker carries an upper bound, this abort is
     * a reachable stop, not only a bypass detector. */
    neu = (uint64_t)d->committed + (uint64_t)n;
    if (neu > d->max) {
        fprintf(stderr,
            "gabbro: arena grow refused: %u committed + %u past max %u\n",
            d->committed, n, d->max);
        abort();
    }
    /* Round the new span to whole pages: commit is monotone, so only the
     * not-yet-committed tail needs protection change. Anonymous pages read
     * as zero once committed, which is the zero-fill the floor relies on. */
    seite = (size_t)seiten_groesse();
    von = (size_t)d->committed * (size_t)d->elem;
    bis = (size_t)neu * (size_t)d->elem;
    start = (von / (size_t)seite) * (size_t)seite;
    ende = ((bis + (size_t)seite - 1) / (size_t)seite) * (size_t)seite;
    basis = (char *)d->base;
    if (mprotect(basis + start, ende - start, PROT_READ | PROT_WRITE) != 0) {
        /* OOM below the ceiling: real, reportable, and the program's to
         * handle -- `committed` unchanged, the caller runs `else`. */
        return false;
    }
    /* Freshly committed anonymous pages are zero; scrub defensively so a
     * reused mapping (a platform that recycles) cannot leak a stale word
     * into a slot the program reads as fresh. Cost: one pass over the new
     * tail, priced in the declared per-slot commit cost. */
    memset(basis + von, 0, bis - von);
    d->committed = (uint32_t)neu;
    return true;
}
