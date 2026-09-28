/* laufzeit/kmodul/sperre.h -- the LOCK primitives of a Gabbro unit inside a
 * Linux kernel module (server lane, TODO section 0e K3, rewired by K7).
 *
 * WHAT THIS IS, AND WHY IT IS THE THIRD COPY OF ONE SHAPE. The emitter
 * DECLARES `void L_nimm(void)` and `void L_gib(void)` per `lock` and defines
 * neither: the primitive is trust base, not product (`emit.rs`,
 * `ItemArt::Lock`). Every driver flavour therefore supplies them --
 * `laufzeit/start.c` with pthread mutexes, `laufzeit/metall/metall.h` with the
 * ticket lock of `CTicket.lean`, and this file with whatever the PROGRAM bound.
 *
 * *Until 2026-09-28 this file did not exist, and a `module` unit with one
 * `lock` did not link at all:* `ERROR: modpost: "TAKT_nimm" ... undefined!`,
 * measured on a probe that the checker had passed without a word. The other two
 * flavours are GENERATED drivers and read the lock list out of
 * `TreiberPlan::sperren`; `kmodul.c` is not generated, so `gabbro build` writes
 * that same list beside it as `sperren.h` -- **the same register, not a second
 * one** (`W7`): all three flavours stand on the one `ItemArt::Lock` walk in
 * `bau.rs::sammle`.
 *
 * **WHAT K7 CHANGED, AND IT IS THE WHOLE OF THIS FILE.** Until K7 the four
 * definitions below expanded to `raw_spin_lock`, `raw_spin_lock_irqsave` and
 * `smp_processor_id` -- three of the twelve kernel names the RUNTIME chose for
 * the program (`dokumente/OFFEN.md` O35). They are the program's now
 * (`bindung.h`): the runtime owns the STORAGE and the OPERATIONS are bound.
 * **What did not change is the shape of the promise**, and the next two
 * paragraphs are the same words they were before -- because the promise is the
 * declaration's, not the primitive's.
 *
 * WHY THE STORAGE IS A BLOB. A `raw_spinlock_t` is a kernel TYPE whose size
 * depends on the kernel's configuration, so it cannot stand in a runtime that
 * names no kernel type. What stands here is `GABBRO_KERN_SPERRE_WORTE` words of
 * `unsigned long` per lock, naturally aligned, initialised once at load
 * (`GABBRO_KMOD_SPERRE_INIT`, expanded by `kmodul.c` before the unit's init
 * runs); the program's body asserts that its own struct fits
 * (`bibliothek/linux-kmod/linux-kmod.c`, `_Static_assert` against the kernel it
 * is built for). *A blob too small is a loud build error, never a silent
 * overrun.* The flags word of a masked lock lives inside that struct, in the
 * program's half, where the release finds it again.
 *
 * WHY AN EXCLUSIVE, NON-SLEEPING LOCK -- and this is a requirement ON the
 * binding, kept by `bibliothek/linux-kmod` and stated here because the runtime
 * is what relies on it. A Gabbro lock has a DECLARED holding time
 * (`held <= N ops`) and the checker holds every path to it (`K002`/`K004`). A
 * sleeping lock (`spinlock_t` on `PREEMPT_RT`, a mutex) lets a holder be
 * descheduled, and the declared holding time then means nothing. Stronger than
 * asked, never weaker -- the same choice the shared pair below makes.
 *
 * WHAT `masks irqs` MEANS HERE -- and this is the point of the file
 * (OFFEN O19: "the C realises no masking"). `masks irqs` at a declaration is a
 * promise about the environment: while the lock is held, no interrupt handler
 * runs on this core, so a handler can never arrive INSIDE the critical section
 * and then wait for the very core it interrupted. On bare metal the runtime
 * keeps that promise with `cli`/`sti` around the ticket
 * (`METALL_SPERRE_MASKIERT`). Inside a Linux module the kernel's own word for
 * it is `raw_spin_lock_irqsave`, and that is what the MASKED pair of the
 * binding is required to be -- `gabbro_kern_sperre_nimm_maskiert` is a separate
 * NAME and not a flag exactly so that a program can bind a different primitive
 * for it. A PLAIN lock has no such promise: a handler that takes it on the core
 * that holds it deadlocks, which is exactly the shape the checker refuses as
 * `H102` (`beispiele/gift/460`).
 *
 * `gabbro_halter_L` IS THE OBSERVATION, not part of the primitive: the core
 * that holds the lock, or -1. It is the kernel-module twin of metal's
 * `metall_anspruch_L[core]`, and it exists so that a green run is a
 * MEASUREMENT and not an absence of bad news -- a probe's own interrupt body
 * reads it and reports whether it ever landed on a core that was holding.
 * Unlike metal's it is a single core number rather than a per-core claim
 * array, and the reason is the lock: a ticket lock has a WAITING state that
 * belongs to the queue, an `irqsave` acquire masks before it spins and holds no
 * ticket, so "holding" is the whole of it here.
 *
 * `WRITE_ONCE` stays, and it is not a kernel call: it is the kernel's word for
 * "one plain store, no tearing, no invention", a compiler barrier and no
 * instruction. It leaves no undefined symbol, which is why the K7 measurement
 * reads 0 over this file (`symbole_pruefe`), and it is the same class of thing
 * as the memory model of an `atomic` (`bindung.h`, the note on what is not in
 * it).
 */
#ifndef GABBRO_KMODUL_SPERRE_H
#define GABBRO_KMODUL_SPERRE_H

#include <linux/compiler.h>

#include "bindung.h"

/* The dispatch: the generated `sperren.h` writes `F(name, kind)`, the kind is
 * one of the four words below, and this file picks the definition. Two levels,
 * because a macro argument is not pasted until it has been expanded once.
 *
 * Every expansion is a sequence of file-scope definitions and ends with a `}`,
 * so the list carries no separators and no stray semicolon. */
#define GABBRO_KMOD_SPERRE(L, ART) GABBRO_KMOD_SPERRE_ART(L, ART)
#define GABBRO_KMOD_SPERRE_ART(L, ART) GABBRO_KMOD_SPERRE_##ART(L)

/* The storage and the observation, shared by all four kinds. `gabbro_halter_L`
 * is not `static`: a probe's own C reads it (see the file header). */
#define GABBRO_KMOD_SPERRE_LAGER(L)                                           \
    static unsigned long gabbro_sperre_##L[GABBRO_KERN_SPERRE_WORTE];         \
    int gabbro_halter_##L = -1;

#define GABBRO_KMOD_SPERRE_ADR(L) ((uint64_t)(uintptr_t)gabbro_sperre_##L)

/* **The initialisation, over the same list.** `kmodul.c` expands it once, at
 * load, before the unit's init runs -- so a lock is ready before anything the
 * program arms can take it (the `takt` probe arms a hardirq timer inside its
 * init, and the timer's body takes the lock). */
#define GABBRO_KMOD_SPERRE_INIT(L, ART)                                       \
    gabbro_kern_sperre_init(GABBRO_KMOD_SPERRE_ADR(L));

#define GABBRO_KMOD_SPERRE_PLAIN(L)                                           \
    GABBRO_KMOD_SPERRE_LAGER(L)                                               \
    void L##_nimm(void)                                                       \
    {                                                                         \
        gabbro_kern_sperre_nimm(GABBRO_KMOD_SPERRE_ADR(L));                   \
        WRITE_ONCE(gabbro_halter_##L, (int)gabbro_kern_kernnummer());         \
    }                                                                         \
    void L##_gib(void)                                                        \
    {                                                                         \
        WRITE_ONCE(gabbro_halter_##L, -1);                                    \
        gabbro_kern_sperre_gib(GABBRO_KMOD_SPERRE_ADR(L));                    \
    }

#define GABBRO_KMOD_SPERRE_MASKED(L)                                          \
    GABBRO_KMOD_SPERRE_LAGER(L)                                               \
    void L##_nimm(void)                                                       \
    {                                                                         \
        gabbro_kern_sperre_nimm_maskiert(GABBRO_KMOD_SPERRE_ADR(L));          \
        WRITE_ONCE(gabbro_halter_##L, (int)gabbro_kern_kernnummer());         \
    }                                                                         \
    void L##_gib(void)                                                        \
    {                                                                         \
        WRITE_ONCE(gabbro_halter_##L, -1);                                    \
        gabbro_kern_sperre_gib_maskiert(GABBRO_KMOD_SPERRE_ADR(L));           \
    }

/* The shared pair takes the SAME exclusive lock: readers exclude each other
 * too. Stronger than the declaration asks, never weaker -- no guarantee is
 * traded for a simpler lock (the same choice `METALL_SPERRE_GETEILT` makes). */
#define GABBRO_KMOD_SPERRE_SHARED(L)                                          \
    GABBRO_KMOD_SPERRE_PLAIN(L)                                               \
    void L##_nimm_geteilt(void) { L##_nimm(); }                               \
    void L##_gib_geteilt(void) { L##_gib(); }

#define GABBRO_KMOD_SPERRE_MASKED_SHARED(L)                                   \
    GABBRO_KMOD_SPERRE_MASKED(L)                                              \
    void L##_nimm_geteilt(void) { L##_nimm(); }                               \
    void L##_gib_geteilt(void) { L##_gib(); }

#endif
