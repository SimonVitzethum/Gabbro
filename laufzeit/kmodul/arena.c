/* laufzeit/kmodul/arena.c -- the LINUX-KERNEL-MODULE half of
 * `laufzeit/arena_dyn.h` (server lane, TODO section 0e H2).
 *
 * Three halves of the same two signatures now exist, and no caller changes
 * between them, because no caller names a page:
 *
 *   hosted   `laufzeit/arena_dyn.c`      reserve = mmap(PROT_NONE),
 *                                        commit  = mprotect
 *   metal    `laufzeit/metall/arena.c`   reserve = a slice of one static
 *                                        region, commit = a budget
 *   module   THIS FILE                   reserve = one `vmalloc` region per
 *                                        arena, commit = a budget over it
 *
 * WHY NOT THE HOSTED SHAPE. The hosted reserve names address space without
 * storage -- 32 GiB of `PROT_NONE` costs a page table entry and nothing else.
 * A loadable module has no exported primitive for that: `get_vm_area` and
 * `vmap_pages_range` are not EXPORT_SYMBOL, and everything that is exported
 * (`vmalloc`, `__vmalloc`, `kvmalloc`) COMMITS what it maps. So the ceiling
 * here is what it is on bare metal -- a BUDGET, the `Spec.lean` (M10) reading:
 * the ceiling is the number the checker holds every `grow` against (`N426`),
 * and what the module can actually commit is the module's own provision.
 * *This is a statement about Linux's exported surface, measured, not a
 * convenience:* nothing in the checker, the emitter or the goal theorem moves
 * for it, and the program's `else` is the answer either way.
 *
 * WHAT THE CEILING COSTS: nothing. `span` below is the MINIMUM of the
 * declared ceiling and the module's provision, computed at run time out of the
 * descriptor. A `max 4294967295` arena and a `max 4096` arena produce the same
 * code and the same module size (`instrumente/miss-arena-decke.sh` measures the
 * emitted side of that claim; this file is the run-time side of it).
 *
 * REFUSE-ON-FULL IS REAL HERE, and that is the point of the flavour. On hosted
 * Linux under the default overcommit heuristic a commit practically never
 * fails and the OOM killer fires later at first touch (OFFEN O20). Here the
 * provision is a number the loader sets (`vorrat_kib`), so a `grow` past it
 * returns false, `committed` does not move, and the `else` the program wrote
 * beside the `grow` runs -- deterministically, on purpose, every boot.
 *
 * FAIL-STOP stays fail-stop: a request past the declared ceiling `max` can
 * only arrive if the checker was bypassed (`N426` holds every admitted `grow`
 * below it), so it refuses the LOAD of the module rather than committing a
 * prefix nobody reasoned about.
 */

#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/vmalloc.h>
#include <linux/printk.h>
#include <linux/atomic.h>

#include "../arena_dyn.h"
#include "kmodul.h"

/* The per-arena provision, in KiB. The module's loader sets it
 * (`insmod … vorrat_kib=16`), and a deployment that wants more says so; the
 * default is small ON PURPOSE, so that a program's refuse-on-full path is
 * exercised rather than assumed. */
static unsigned int vorrat_kib = 16;
module_param(vorrat_kib, uint, 0444);
MODULE_PARM_DESC(vorrat_kib,
    "per-arena commit provision in KiB (the ceiling is the program's `max`)");

/* Set when a reservation refused: the module's init returns the failure, and
 * nothing of the program runs. A refused reservation is never a smaller
 * range -- the hosted contract, kept. */
static int gabbro_arena_laden_fehler;

/* Every region this module mapped, so the unload gives all of them back. A
 * fixed, small table: the number of ARENAS a unit declares is a translation-
 * time number, not a run-time one. */
#ifndef GABBRO_KMOD_ARENEN
#define GABBRO_KMOD_ARENEN 8
#endif
static void *gabbro_arena_regionen[GABBRO_KMOD_ARENEN];
static unsigned int gabbro_arena_regionen_n;

int gabbro_arena_ladefehler(void)
{
    return gabbro_arena_laden_fehler;
}

void gabbro_arena_alles_freigeben(void)
{
    unsigned int i;

    for (i = 0; i < gabbro_arena_regionen_n; i++) {
        vfree(gabbro_arena_regionen[i]);
        gabbro_arena_regionen[i] = NULL;
    }
    gabbro_arena_regionen_n = 0;
}

static void verweigere_laden(const char *warum, unsigned int a, unsigned int b)
{
    pr_err("gabbro: arena reserve refused: %s (%u, %u)\n", warum, a, b);
    gabbro_arena_laden_fehler = -ENOMEM;
}

void gabbro_arena_reserve(gabbro_arena_desc *d)
{
    unsigned long long decke, vorrat, span;
    void *base;

    if (d == NULL || d->base != NULL || d->max == 0 || d->elem == 0 ||
            d->floor_hi > d->max) {
        verweigere_laden("bad descriptor (max, floor, elem)",
                         d ? d->max : 0u, d ? d->floor_hi : 0u);
        return;
    }
    if (gabbro_arena_regionen_n >= GABBRO_KMOD_ARENEN) {
        verweigere_laden("more arenas than this runtime maps",
                         gabbro_arena_regionen_n, GABBRO_KMOD_ARENEN);
        return;
    }

    /* `span` is min(ceiling, provision) -- the ceiling is a NUMBER, the
     * provision is the storage. Neither multiplication can overflow: both
     * factors are 32-bit and the product is computed in 64. */
    decke = (unsigned long long)d->max * (unsigned long long)d->elem;
    vorrat = (unsigned long long)vorrat_kib * 1024ull;
    span = decke < vorrat ? decke : vorrat;

    /* The FLOOR has to fit, or the load refuses: a program started with less
     * than its declared `hi` committed would be running against a fact the
     * checker used. */
    if (span < (unsigned long long)d->floor_hi * (unsigned long long)d->elem) {
        verweigere_laden("the provision cannot hold the committed floor",
                         d->floor_hi, vorrat_kib);
        return;
    }
    if (span > (unsigned long long)(~(size_t)0)) {
        verweigere_laden("span does not fit size_t", d->max, d->elem);
        return;
    }

    base = vzalloc((size_t)span);
    if (base == NULL) {
        verweigere_laden("vzalloc of the provision failed", vorrat_kib, d->elem);
        return;
    }
    gabbro_arena_regionen[gabbro_arena_regionen_n++] = base;

    d->base = base;
    d->used = 0;
    /* The committed prefix in SLOTS that the provision carries. It is what
     * `grow` is measured against below; `committed` itself starts at the
     * declared floor, as the emitter's descriptor already says. */
    d->committed = d->floor_hi;
}

bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)
{
    unsigned long long neu, vorrat, span, decke;

    if (d == NULL || d->base == NULL) {
        return false;
    }
    if (n == 0) {
        return true;
    }
    neu = (unsigned long long)d->committed + (unsigned long long)n;
    if (neu > (unsigned long long)d->max) {
        /* Past the DECLARED ceiling. `N426` admits no such `grow`, so this
         * is a bypassed checker, not a tight machine: fail-stop, loudly. */
        pr_err("gabbro: arena grow past max (%llu > %u) -- fail-stop\n",
               neu, d->max);
        gabbro_arena_laden_fehler = -EOVERFLOW;
        return false;
    }
    decke = (unsigned long long)d->max * (unsigned long long)d->elem;
    vorrat = (unsigned long long)vorrat_kib * 1024ull;
    span = decke < vorrat ? decke : vorrat;
    if (neu * (unsigned long long)d->elem > span) {
        /* Below the ceiling, past the provision: the program's `else` runs
         * and `committed` does not move. THIS is refuse-on-full. */
        return false;
    }
    d->committed = (uint32_t)neu;
    return true;
}
