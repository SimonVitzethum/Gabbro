/* laufzeit/metall/metall.h -- the bare-metal thread runtime, driver side
 * (Opus agent I, 2026-09-26).
 *
 * WHAT THIS IS. The freestanding counterpart of `laufzeit/faden.h` plus the
 * hosted drivers' lock and `main`: the SAME two thread symbols the emitter
 * calls (`gabbro_faden_start`, `gabbro_faden_warte`, declared by the emitted
 * unit itself and by `faden.h`), the ticket lock the emitter's `L_nimm` /
 * `L_gib` resolve to, and the one hook a driver provides,
 * `gabbro_metall_haupt`. No libc: only `<stdint.h>` and `<stdatomic.h>`,
 * both freestanding headers in C11.
 *
 * THE IMAGE. `start.S` (Multiboot1 entry, long mode, AP trampoline, context
 * switch, interrupt entries) + `kern.c` (serial, LAPIC, ACPI MADT, SMP
 * bring-up, per-core scheduler, the thread API) + ONE driver file that
 * `#include`s the emitted unit (its roots are `static`, exactly as with the
 * hosted drivers) and this header. `instrumente/pruefe-metall.sh` builds and
 * boots it under QEMU.
 */
#ifndef GABBRO_METALL_H
#define GABBRO_METALL_H

#include <stdint.h>
#include <stdatomic.h>

/* -- The thread interface: IDENTICAL to laufzeit/faden.h. -------------------
 *
 * The emitted C of a `start` statement declares these two itself; the
 * definitions live in `kern.c`. Same contract as the hosted file: `spitze` is
 * the 16-aligned TOP of a stack the unit owns, `wort` is zero before the
 * call, nonzero while the thread lives, zero again once it has LEFT its stack
 * (the scheduler clears it from the core's own stack, never from the thread's
 * -- the stack is free for reuse the moment the join returns). Returns 0, or
 * 22 (EINVAL: null root, stack or word; unaligned stack) or 11 (EAGAIN: the
 * runtime's thread table is full). */
int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort);
void gabbro_faden_warte(uint32_t *wort);

/* -- The ticket lock (CTicket.lean, SATZKARTE section 32). ------------------
 *
 * Two 32-bit counters per lock, the four instructions of the Lean model:
 *   zieht  my = fetch_add(&naechste, 1)          (relaxed: only a number)
 *   dreht/tritt  spin while load(&jetzt) != my   (acquire: enter synchronises
 *                                                 with the last release)
 *   gibt   store(&jetzt, jetzt + 1)              (release)
 * `laufzeit/sperre.gab` is the same lock written in Gabbro; this C is the
 * spelling the image links, word for word the shape `CTicket.lean` proves
 * (mutual exclusion `ticket_ausschluss`, FIFO `ticket_fifo`, refinement
 * `ticketLP_sperrAbstrakt`). Two findings of that section hold here verbatim:
 * the release performs no check (`gib_ohne_wache` -- the checker's lock
 * discipline is what keeps callers well nested) and the counters wrap at
 * 2^32 (not modelled: fewer than 2^32 outstanding tickets per lock).
 *
 * `pause` in the spin: the architectural spin-wait hint, no memory effect. A
 * waiter on the SAME core as the holder is not a deadlock because the timer
 * preempts it (kern.c, `metall_takt`); without preemption it would be one
 * (the Sprechprobe `koop` of the harness measures exactly that shape). */
typedef struct {
    _Atomic uint32_t naechste;
    _Atomic uint32_t jetzt;
} metall_ticket;

static inline void metall_ticket_nimm(metall_ticket *t)
{
    uint32_t my = atomic_fetch_add_explicit(&t->naechste, 1u, memory_order_relaxed);
    while (atomic_load_explicit(&t->jetzt, memory_order_acquire) != my) {
        __asm__ __volatile__("pause" ::: "memory");
    }
}

static inline void metall_ticket_gib(metall_ticket *t)
{
    uint32_t n = atomic_load_explicit(&t->jetzt, memory_order_relaxed);
    atomic_store_explicit(&t->jetzt, (uint32_t)(n + 1u), memory_order_release);
}

/* THE GABBRO-FACING ACQUIRE: the same four instructions, and one scheduler
 * action in the spin. A thread whose ticket is not served yet gives its core
 * away every `METALL_SPIN` passes (`metall_abgeben`, kern.c). WHY: with more
 * threads than cores, the ticket that is served next may belong to a thread
 * that is not running -- preempted, or queued behind the spinner on the same
 * core. Pure spinning then waits a whole quantum per hand-over (measured
 * 2026-09-26: 8 threads x 20000 acquisitions on 4 cores did not finish in
 * 60 s; 8 x 500 took 1.5 s). Yielding hands the core to exactly the thread
 * the queue is waiting for. For the lock it changes nothing: the ticket stays
 * drawn, the order stays the ticket order, and a yield leaves the spinner's
 * C configuration where it was -- the stutter `spinnt_nur` of CTicket.lean.
 * The runtime-internal locks keep the pure spin: they are held with IF = 0
 * on the scheduler's own stack, where there is no one to yield to. */
void metall_abgeben(void);

#ifndef METALL_SPIN
#define METALL_SPIN 64u
#endif

static inline void metall_sperre_nimm(metall_ticket *t)
{
    uint32_t my = atomic_fetch_add_explicit(&t->naechste, 1u, memory_order_relaxed);
    uint32_t n = 0;
    while (atomic_load_explicit(&t->jetzt, memory_order_acquire) != my) {
        __asm__ __volatile__("pause" ::: "memory");
        if (++n == METALL_SPIN) {
            n = 0;
            metall_abgeben();
        }
    }
}

/* One exclusive Gabbro lock: defines exactly the two symbols the emitter
 * declares per lock. A misspelt name is an undefined reference at link time,
 * the same contract the hosted drivers keep. */
#define METALL_SPERRE(L)                                                  \
    static metall_ticket metall_sperre_##L;                               \
    void L##_nimm(void) { metall_sperre_nimm(&metall_sperre_##L); }       \
    void L##_gib(void) { metall_ticket_gib(&metall_sperre_##L); }

/* A shared (`geteilt`) lock: its shared pair takes the SAME ticket, i.e. the
 * shared side is served exclusively. Stronger than asked (readers exclude
 * each other too), never weaker: no guarantee is traded for the simpler
 * lock. */
#define METALL_SPERRE_GETEILT(L)                                          \
    METALL_SPERRE(L)                                                      \
    void L##_nimm_geteilt(void) { metall_sperre_nimm(&metall_sperre_##L); } \
    void L##_gib_geteilt(void) { metall_ticket_gib(&metall_sperre_##L); }

/* -- The driver hook and the report channel. --------------------------------
 *
 * `gabbro_metall_haupt` runs as the FIRST thread on core 0 once every core is
 * up; it starts the unit's roots through the thread API, joins them, and
 * reports over the serial port. Its return value ends the machine: 0 is
 * success. The report lines are the harness's comparison object. */
int gabbro_metall_haupt(void);

void metall_schreibe(const char *s);
void metall_zahl(uint64_t v);
uint32_t metall_kerne(void);        /* cores that checked in */
uint32_t metall_kern_nr(void);      /* the calling thread's core */
__attribute__((noreturn)) void metall_ende(int code);

#endif
