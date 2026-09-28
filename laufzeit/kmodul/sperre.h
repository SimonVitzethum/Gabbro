/* laufzeit/kmodul/sperre.h -- the LOCK primitives of a Gabbro unit inside a
 * Linux kernel module (server lane, TODO section 0e K3).
 *
 * WHAT THIS IS, AND WHY IT IS THE THIRD COPY OF ONE SHAPE. The emitter
 * DECLARES `void L_nimm(void)` and `void L_gib(void)` per `lock` and defines
 * neither: the primitive is trust base, not product (`emit.rs`,
 * `ItemArt::Lock`). Every driver flavour therefore supplies them --
 * `laufzeit/start.c` with pthread mutexes, `laufzeit/metall/metall.h` with the
 * ticket lock of `CTicket.lean`, and this file with the kernel's own
 * `raw_spinlock_t`.
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
 * WHY `raw_spinlock_t` AND NOT `spinlock_t`. A Gabbro lock has a DECLARED
 * holding time (`held <= N ops`) and the checker holds every path to it
 * (`K002`/`K004`). On a `PREEMPT_RT` kernel a `spinlock_t` is a sleeping lock,
 * so a holder can be descheduled and the declared holding time means nothing;
 * `raw_spinlock_t` spins on every configuration. Stronger than asked, never
 * weaker -- the same choice the shared pair below makes.
 *
 * WHAT `masks irqs` LOWERS TO HERE -- and this is the point of the file
 * (OFFEN O19: "the C realises no masking"). `masks irqs` at a declaration is a
 * promise about the environment: while the lock is held, no interrupt handler
 * runs on this core, so a handler can never arrive INSIDE the critical section
 * and then wait for the very core it interrupted. On bare metal the runtime
 * keeps that promise with `cli`/`sti` around the ticket
 * (`METALL_SPERRE_MASKIERT`). Inside a Linux module the kernel's own word for
 * it is `raw_spin_lock_irqsave`, and that is what a MASKED lock becomes here.
 * A PLAIN lock becomes `raw_spin_lock`: a handler that takes it on the core
 * that holds it deadlocks, which is exactly the shape the checker refuses as
 * `H102` (`beispiele/gift/460`).
 *
 * THE FLAGS WORD IS A STATIC, and that is sound for the same reason it is on
 * metal: it is written only by the thread that holds the lock, between the
 * acquire and the release, and read only by that same thread. The interface
 * the emitter declares takes no argument, so the flags cannot travel on the
 * stack as `spin_lock_irqsave`'s do.
 *
 * `gabbro_halter_L` IS THE OBSERVATION, not part of the primitive: the core
 * that holds the lock, or -1. It is the kernel-module twin of metal's
 * `metall_anspruch_L[core]`, and it exists so that a green run is a
 * MEASUREMENT and not an absence of bad news -- a probe's own interrupt body
 * reads it and reports whether it ever landed on a core that was holding.
 * Unlike metal's it is a single core number rather than a per-core claim
 * array, and the reason is the lock: a ticket lock has a WAITING state that
 * belongs to the queue, `raw_spin_lock_irqsave` masks before it spins and
 * holds no ticket, so "holding" is the whole of it here.
 */
#ifndef GABBRO_KMODUL_SPERRE_H
#define GABBRO_KMODUL_SPERRE_H

#include <linux/spinlock.h>
#include <linux/smp.h>
#include <linux/compiler.h>

/* The dispatch: the generated `sperren.h` writes `F(name, kind)`, the kind is
 * one of the four words below, and this file picks the definition. Two levels,
 * because a macro argument is not pasted until it has been expanded once.
 *
 * Every expansion is a sequence of file-scope definitions and ends with a `}`,
 * so the list carries no separators and no stray semicolon. */
#define GABBRO_KMOD_SPERRE(L, ART) GABBRO_KMOD_SPERRE_ART(L, ART)
#define GABBRO_KMOD_SPERRE_ART(L, ART) GABBRO_KMOD_SPERRE_##ART(L)

#define GABBRO_KMOD_SPERRE_PLAIN(L)                                           \
    static DEFINE_RAW_SPINLOCK(gabbro_sperre_##L);                            \
    int gabbro_halter_##L = -1;                                               \
    void L##_nimm(void)                                                       \
    {                                                                         \
        raw_spin_lock(&gabbro_sperre_##L);                                    \
        WRITE_ONCE(gabbro_halter_##L, smp_processor_id());                    \
    }                                                                         \
    void L##_gib(void)                                                        \
    {                                                                         \
        WRITE_ONCE(gabbro_halter_##L, -1);                                    \
        raw_spin_unlock(&gabbro_sperre_##L);                                  \
    }

#define GABBRO_KMOD_SPERRE_MASKED(L)                                          \
    static DEFINE_RAW_SPINLOCK(gabbro_sperre_##L);                            \
    static unsigned long gabbro_flaggen_##L;                                  \
    int gabbro_halter_##L = -1;                                               \
    void L##_nimm(void)                                                       \
    {                                                                         \
        unsigned long f;                                                      \
        raw_spin_lock_irqsave(&gabbro_sperre_##L, f);                         \
        gabbro_flaggen_##L = f;                                               \
        WRITE_ONCE(gabbro_halter_##L, smp_processor_id());                    \
    }                                                                         \
    void L##_gib(void)                                                        \
    {                                                                         \
        unsigned long f = gabbro_flaggen_##L;                                 \
        WRITE_ONCE(gabbro_halter_##L, -1);                                    \
        raw_spin_unlock_irqrestore(&gabbro_sperre_##L, f);                    \
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
