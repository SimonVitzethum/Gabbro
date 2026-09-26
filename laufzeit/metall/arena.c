/* laufzeit/metall/arena.c -- the BARE-METAL half of `laufzeit/arena_dyn.h`
 * (Opus agent J, 2026-09-26).
 *
 * The hosted half (`laufzeit/arena_dyn.c`) reserves with `mmap(PROT_NONE)`
 * and commits with `mprotect`. There is no OS here, so the same two
 * signatures are kept -- no caller changes, because no caller names a page --
 * and the two OS facts are replaced by two named quantities of the image:
 *
 *   RESERVE  one static region, `METALL_ARENA_VORRAT` bytes (default 1 MiB),
 *            in `.bss` (zeroed by the boot protocol, assumption `lader` of
 *            the bare-metal block in `Spec.lean`). `gabbro_arena_reserve`
 *            carves `max * elem` bytes of it per arena, 16-aligned, at load.
 *            A reservation that does not fit refuses the LOAD (serial line +
 *            `metall_ende(GABBRO_ARENA_EXIT_RESERVE)`), exactly the hosted
 *            contract: never a program started with a smaller range.
 *   COMMIT   bookkeeping against one budget, `METALL_ARENA_ZUSAGE` bytes
 *            (default: the whole reserve). `gabbro_arena_grow` takes
 *            `n * elem` bytes of budget with a compare-and-swap; if the
 *            budget is exhausted it returns FALSE and leaves `committed`
 *            unchanged -- the program's `else` beside the `grow` runs. This
 *            is the branch the hosted runtime practically never takes (the
 *            overcommit heuristic, OFFEN O20); here it is REAL and
 *            deterministic: build the image with a smaller budget and the
 *            refusal is what the runtime does, not what a stub pretends.
 *
 * The new slots read as zero: the region is `.bss`, and a region is carved
 * once and never handed out again, so no byte of it was written before its
 * commit. A request reaching past `max` is the fail-stop of the hosted half
 * (`N426` keeps admitted grows below it), never a partial commit.
 *
 * Concurrency: reservation runs at load, before any start. `grow` may run on
 * several cores for DIFFERENT arenas (each descriptor is the program's,
 * guarded by its effects); the shared budget is one atomic word.
 */

#include <stdint.h>
#include <stdatomic.h>
#include "../arena_dyn.h"
#include "metall.h"

#ifndef METALL_ARENA_VORRAT
#define METALL_ARENA_VORRAT (1024u * 1024u)
#endif
#ifndef METALL_ARENA_ZUSAGE
#define METALL_ARENA_ZUSAGE METALL_ARENA_VORRAT
#endif

static unsigned char vorrat[METALL_ARENA_VORRAT] __attribute__((aligned(64)));
static _Atomic uint64_t vorrat_belegt;                 /* bytes carved so far */
static _Atomic uint64_t zusage_rest = METALL_ARENA_ZUSAGE;   /* commit budget left */

static void verweigere_laden(const char *warum, uint32_t a, uint32_t b)
{
    metall_schreibe("gabbro: arena reserve refused: ");
    metall_schreibe(warum);
    metall_schreibe(" ");
    metall_zahl(a);
    metall_schreibe(" ");
    metall_zahl(b);
    metall_schreibe("\n");
    metall_ende(GABBRO_ARENA_EXIT_RESERVE);
}

/* Take `bytes` of commit budget, or none. */
static int zusage_nimm(uint64_t bytes)
{
    uint64_t rest = atomic_load_explicit(&zusage_rest, memory_order_relaxed);
    do {
        if (rest < bytes) {
            return 0;
        }
    } while (!atomic_compare_exchange_weak_explicit(&zusage_rest, &rest, rest - bytes,
                                                    memory_order_relaxed, memory_order_relaxed));
    return 1;
}

void gabbro_arena_reserve(gabbro_arena_desc *d)
{
    if (d == 0 || d->base != 0 || d->max == 0 || d->elem == 0 || d->floor_hi > d->max) {
        verweigere_laden("bad descriptor (max, floor)", d ? d->max : 0u, d ? d->floor_hi : 0u);
    }
    uint64_t span = (uint64_t)d->max * (uint64_t)d->elem;
    uint64_t gerundet = (span + 15u) & ~(uint64_t)15u;
    uint64_t alt = atomic_fetch_add_explicit(&vorrat_belegt, gerundet, memory_order_relaxed);
    if (alt + gerundet > (uint64_t)METALL_ARENA_VORRAT || alt + gerundet < alt) {
        verweigere_laden("the static reserve cannot hold max slots of elem bytes", d->max, d->elem);
    }
    d->base = &vorrat[alt];
    d->used = 0;
    d->committed = 0;
    /* The floor is committed at load; a floor the budget cannot carry refuses
     * the load, as on the hosted side. */
    if (d->floor_hi > 0 && !gabbro_arena_grow(d, d->floor_hi)) {
        verweigere_laden("cannot commit the floor", d->floor_hi, d->elem);
    }
    d->committed = d->floor_hi;
}

bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)
{
    if (d == 0 || d->base == 0) {
        return false;
    }
    if (n == 0) {
        return true;
    }
    uint64_t neu = (uint64_t)d->committed + (uint64_t)n;
    if (neu > d->max) {
        metall_schreibe("gabbro: arena grow refused: past max -- fail-stop\n");
        metall_ende(4);
    }
    if (!zusage_nimm((uint64_t)n * (uint64_t)d->elem)) {
        /* The budget is exhausted below the ceiling: `committed` unchanged,
         * the caller runs `else`. */
        return false;
    }
    d->committed = (uint32_t)neu;
    return true;
}
