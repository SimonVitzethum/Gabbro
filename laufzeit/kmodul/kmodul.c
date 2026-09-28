/* laufzeit/kmodul/kmodul.c -- a Gabbro unit AS A LINUX KERNEL MODULE
 * (server lane, TODO section 0e K4).
 *
 * This is the third driver flavour of one shape. `laufzeit/start.c` runs a
 * unit's declared roots as POSIX threads; `laufzeit/metall/` runs them on bare
 * metal; this file runs a unit inside a loadable Linux kernel module. Like the
 * other two it INCLUDES the emitted C (so a `static` root is nameable --
 * inclusion, not linkage) and supplies what the emitted C leaves undefined.
 *
 * IT IS NOT GENERATED, and that is deliberate (`W7`: a second register over
 * the same thing). Everything that differs between units arrives as a macro
 * the build sets, so there is exactly one copy of this text in the tree:
 *
 *   GABBRO_EINHEIT_INCLUDE   the emitted `<unit>.c`, as a string for #include
 *   GABBRO_KMOD_INIT         the unit's function that `module_init` calls
 *   GABBRO_KMOD_EXIT         the unit's function that `module_exit` calls
 *
 * **The arenas are NOT among them, since 2026-09-28.** The emitted unit carries
 * its own list -- `#define GABBRO_ARENEN &Knoten_desc`, written by the emitter,
 * which is the only place that knows which descriptors it emitted. Until that
 * day this file took the list from a `-D` on the command line, so an arena
 * added to the program and forgotten on the command line was an UNRESERVED
 * arena: a null base at the first `alloc`. *Two registers over one fact, and
 * the one nobody reads is the one that drifts* (`W7`).
 *
 * **What the program calls, the program declares.** Nothing in this file
 * stands between a Gabbro `extern fn` and the kernel: a unit that calls a
 * kernel function names it itself, with its ABI, its effects, its costs and
 * the assumption it rests on, and the module ships the body. There is no table
 * of Linux kernel functions here and none anywhere else in the tree (the
 * binding constraint, `TODO.md` section -1).
 *
 * The init/exit pair are ORDINARY Gabbro functions of the unit. A Linux module
 * is entered by a call, not by a vector, so `entry … vector V` (which is the
 * interrupt form, `SYNTAX.md` section 5) is the wrong word for it; the manifest
 * names them, because what the product IS has no representative in the source
 * (`BAUSYSTEM.md` section 1).
 *
 * The init function's `uint32_t` answer is the module's load verdict: 0 loads,
 * anything else refuses the load with `-EINVAL` and NOTHING of the unit stays
 * resident. A reservation that refused (`gabbro_arena_ladefehler`) refuses the
 * load the same way -- the hosted contract, kept: never a program started with
 * a smaller range.
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/printk.h>

#ifndef GABBRO_EINHEIT_INCLUDE
#error "GABBRO_EINHEIT_INCLUDE must name the emitted unit (the build sets it)"
#endif
#ifndef GABBRO_KMOD_INIT
#error "GABBRO_KMOD_INIT must name the unit's load function (the build sets it)"
#endif
#ifndef GABBRO_KMOD_EXIT
#error "GABBRO_KMOD_EXIT must name the unit's unload function (the build sets it)"
#endif

#include GABBRO_EINHEIT_INCLUDE

/* The unit's own list decides whether this module has arenas at all: the
 * emitter writes `GABBRO_ARENEN` exactly when it emitted descriptors. */
#ifdef GABBRO_ARENEN
#include "kmodul.h"
static gabbro_arena_desc *gabbro_kmod_arenen[] = { GABBRO_ARENEN };
#endif

/* **The LOCKS, and the list comes from the BUILD and not from the emitted C.**
 * `gabbro build` writes `sperren.h` beside this file: one `#define
 * GABBRO_SPERREN(F)` with an `F(name, kind)` per `lock`, out of the same walk
 * the hosted and the bare-metal driver read their locks from -- one register,
 * three flavours (`W7`). It is a generated file and always present; a unit
 * without a lock gets a comment instead of the macro, which is why the
 * expansion below stands under `#ifdef`.
 *
 * (It is not in the emitted unit, where `GABBRO_ARENEN` stands, because that C
 * is pinned byte for byte in the translation-validation chain and the Lean
 * `CParser` reads only `#include <x.h>` and integer `#define`s. See
 * `bau.rs::kmod_modul_binden` for the measurement.)
 *
 * `masks irqs` becomes `raw_spin_lock_irqsave` here -- see `sperre.h` for why
 * that is the kernel's word for the promise, and what a PLAIN lock
 * deliberately is not (server lane, 2026-09-28, TODO section 0e K3). */
#include "sperren.h"
#ifdef GABBRO_SPERREN
#include "sperre.h"
GABBRO_SPERREN(GABBRO_KMOD_SPERRE)
#endif

static int __init gabbro_kmod_init(void)
{
    uint32_t antwort;
#ifdef GABBRO_ARENEN
    unsigned int i;
    int fehler;

    /* Every reservation runs BEFORE any of the unit's code -- assumption (d)
     * `Laufzeit.reserve` in `Zielsatz/Spec.lean`. */
    for (i = 0; i < ARRAY_SIZE(gabbro_kmod_arenen); i++) {
        gabbro_arena_reserve(gabbro_kmod_arenen[i]);
    }
    fehler = gabbro_arena_ladefehler();
    if (fehler != 0) {
        pr_err("gabbro: load refused -- a reservation failed (%d)\n", fehler);
        gabbro_arena_alles_freigeben();
        return fehler;
    }
#endif

    antwort = GABBRO_KMOD_INIT();
    if (antwort != 0) {
        pr_err("gabbro: load refused -- the unit answered %u\n",
               (unsigned int)antwort);
#ifdef GABBRO_ARENEN
        gabbro_arena_alles_freigeben();
#endif
        return -EINVAL;
    }
#ifdef GABBRO_ARENEN
    /* **And again AFTER the unit ran.** A `grow` past the declared ceiling is
     * a fail-stop, not a branch -- `N426` admits no such `grow`, so one can
     * only arrive if the checker was bypassed. It sets the load error and
     * returns false, which means the program's `else` runs and the unit can
     * still answer 0. *Measured by the harness's fourth mutation
     * (`pruefe-kernelmodul.sh --gift 4`), which lowered the emitted ceiling
     * below the program's grows: without this second read `insmod` succeeded
     * over a fail-stop that had already fired.* A fail-stop that does not
     * reach the loader is not a fail-stop. */
    fehler = gabbro_arena_ladefehler();
    if (fehler != 0) {
        pr_err("gabbro: load refused -- a fail-stop fired during init (%d)\n",
               fehler);
        gabbro_arena_alles_freigeben();
        return fehler;
    }
#endif
    return 0;
}

static void __exit gabbro_kmod_exit(void)
{
    (void)GABBRO_KMOD_EXIT();
#ifdef GABBRO_ARENEN
    gabbro_arena_alles_freigeben();
#endif
}

module_init(gabbro_kmod_init);
module_exit(gabbro_kmod_exit);

MODULE_LICENSE("Dual MIT/GPL");
MODULE_DESCRIPTION("a Gabbro unit as a Linux kernel module");
