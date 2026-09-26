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

/* The most cores the runtime brings up (kern.c); a driver may lower it with
 * `METALL_KERNE_GRENZE`. */
#define METALL_KERNE_MAX 16u

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

/* The interrupt flag of the caller, and the pair that clears and restores it
 * (Opus agent J). A yield is only taken with IF = 1: with IF = 0 the caller is
 * an interrupt handler (running on whatever it interrupted) or inside a
 * `masks irqs` section, and both must never give the core away -- the first
 * would run another thread on top of an unfinished handler, the second would
 * deschedule a masked holder, which is exactly what `masks irqs` rules out. */
static inline uint64_t metall_flaggen(void)
{
    uint64_t f;
    __asm__ __volatile__("pushfq; popq %0" : "=r"(f) :: "memory");
    return f;
}
static inline uint64_t metall_ia_aus(void)
{
    uint64_t f;
    __asm__ __volatile__("pushfq; popq %0; cli" : "=r"(f) :: "memory");
    return f;
}
static inline void metall_ia_her(uint64_t f)
{
    __asm__ __volatile__("pushq %0; popfq" :: "r"(f) : "memory", "cc");
}
#define METALL_IF 0x200u

static inline void metall_sperre_nimm(metall_ticket *t)
{
    uint32_t my = atomic_fetch_add_explicit(&t->naechste, 1u, memory_order_relaxed);
    uint32_t n = 0;
    int darf_abgeben = (metall_flaggen() & METALL_IF) != 0u;
    while (atomic_load_explicit(&t->jetzt, memory_order_acquire) != my) {
        __asm__ __volatile__("pause" ::: "memory");
        if (++n == METALL_SPIN) {
            n = 0;
            if (darf_abgeben) {
                metall_abgeben();
            }
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

/* A `masks irqs` lock (Opus agent J, OFFEN O32 residue): the emitter writes
 * no `cli`/`sti` for the word (`beispiele/59`: "das Wort ist eine ZUSAGE ueber
 * die Umgebung"), so the runtime keeps the promise HERE. Taking the lock
 * clears IF first and keeps it clear until the matching release restores the
 * caller's flags: a thrown entry (`via idt`) can never arrive on the holder's
 * core while it holds, and since a spin with IF = 0 never yields (above), a
 * masked holder is never descheduled either. A handler that takes the lock
 * therefore waits only for a holder on ANOTHER core, which runs. The unmasked
 * spelling of the same lock inside a handler is the same-core deadlock the
 * checker refuses as `H102` (`beispiele/gift/460`); the harness of
 * `instrumente/pruefe-metall.sh` (image `metall59-gift`) shows it hang.
 *
 * A ticket lock adds one case a plain spinlock does not have: a thread that
 * has DRAWN its ticket and waits is part of the queue, and an entry that
 * interrupts it on its core and then takes a later ticket waits behind the
 * very thread it sits on. So IF is cleared BEFORE the ticket is drawn, and the
 * whole claim -- waiting and holding -- runs with IF = 0.
 *
 * `metall_anspruch_L[k]` is 1 while a thread on core k has a claim on L
 * (ticket drawn, or held), 0 otherwise: the observation the harness reads in
 * the handler ("did an entry ever land on a core with a claim on the masked
 * lock?"). It is written only with IF = 0 on its own core. */
#define METALL_SPERRE_MASKIERT(L)                                         \
    static metall_ticket metall_sperre_##L;                               \
    static uint64_t metall_flaggen_##L;                                   \
    volatile uint8_t metall_anspruch_##L[METALL_KERNE_MAX];               \
    void L##_nimm(void)                                                   \
    {                                                                     \
        uint64_t f = metall_ia_aus();                                     \
        metall_anspruch_##L[metall_kern_nr()] = 1u;                       \
        metall_sperre_nimm(&metall_sperre_##L);                           \
        metall_flaggen_##L = f;                                           \
    }                                                                     \
    void L##_gib(void)                                                    \
    {                                                                     \
        uint64_t f = metall_flaggen_##L;                                  \
        metall_ticket_gib(&metall_sperre_##L);                            \
        metall_anspruch_##L[metall_kern_nr()] = 0u;                       \
        metall_ia_her(f);                                                 \
    }

/* The shared pair of a masked lock: the same masked ticket (stronger than
 * asked -- readers exclude each other -- never weaker), as `_GETEILT` above. */
#define METALL_SPERRE_MASKIERT_GETEILT(L)                                 \
    METALL_SPERRE_MASKIERT(L)                                             \
    void L##_nimm_geteilt(void) { L##_nimm(); }                           \
    void L##_gib_geteilt(void) { L##_gib(); }

/* An `rcu R` read side (Opus agent J). The emitter declares
 * `R_lese_start`/`R_lese_ende` and nothing else: WHERE a slot may be given
 * back is checked at compile time (`H011`, `H012`), and "no reader is left
 * inside once the pointer is withdrawn" is an assumption about the
 * environment (`zeugnis.rs`, `rcu`: the body comes from outside). This is
 * that outside on bare metal: a reader count per domain (acq_rel in, release
 * out) and the grace-period wait an environment's writer calls,
 * `metall_rcu_gnade_R` -- it returns once the count was seen at zero, and a
 * spin with IF = 1 gives the core away between reads. Starvation under a
 * never-empty reader population is not excluded (named in OFFEN O32). */
#define METALL_RCU(R)                                                     \
    _Atomic uint32_t metall_rcu_leser_##R;                                \
    void R##_lese_start(void)                                             \
    {                                                                     \
        atomic_fetch_add_explicit(&metall_rcu_leser_##R, 1u,              \
                                  memory_order_acq_rel);                  \
    }                                                                     \
    void R##_lese_ende(void)                                              \
    {                                                                     \
        atomic_fetch_sub_explicit(&metall_rcu_leser_##R, 1u,              \
                                  memory_order_release);                  \
    }                                                                     \
    void metall_rcu_gnade_##R(void);                                      \
    void metall_rcu_gnade_##R(void)                                       \
    {                                                                     \
        while (atomic_load_explicit(&metall_rcu_leser_##R,                \
                                    memory_order_acquire) != 0u) {        \
            if (metall_flaggen() & METALL_IF) {                           \
                metall_abgeben();                                         \
            }                                                             \
        }                                                                 \
    }

/* An entry whose `dispatch` target is not declared in the unit has nothing to
 * run (`erzeugernamen.rs`: the `_verteiler` reference exists only then); its
 * stub ends the machine loudly. And a program's foreign body (`extern fn`)
 * that the image does not supply: the freestanding stage links a trap stub
 * that names it -- reached only if a run calls it. */
void metall_eintritt_ohne_ziel(void);
void metall_eintritt_bindung_falsch(void);   /* regs in/out do not match the dispatch */
__attribute__((noreturn)) void metall_fremd_fehlt(const char *name);

/* -- The program's own entries (Opus agent J, OFFEN O32 residue). ----------
 *
 * `METALL_EINTRITT(NAME, GEWORFEN, AUFRUF...)` defines the stub the emitted
 * unit only declares, `void gabbro_eintritt_NAME(void)`: three instructions
 * that jump into `metall_eintritt_gemeinsam` (start.S: every general register
 * and the x87/SSE state saved, `iretq`), and the C half. The C half receives
 * the saved registers as `struct metall_rahmen *r` and runs `AUFRUF` -- the
 * call of the unit's own `gabbro_eintritt_NAME_verteiler` (the `dispatch`
 * target) with the registers the entry's `regs in` names, its result stored
 * into the register `regs out` names (`r->rax = ...`): what the interrupted
 * code finds in that register after `iretq`. Every other register comes back
 * as it was -- stronger than the declared `preserves`, never weaker. For a
 * THROWN entry delivered by the LAPIC (`via idt` at a vector >= 32: a device
 * interrupt or an IPI; `GEWORFEN` = 1) the C half then acknowledges the LAPIC.
 * An entry without `via` is ENTERED (`int $vector`), and an NMI or CPU
 * exception (vector < 32) is acknowledged by `iretq` alone: `GEWORFEN` = 0, no
 * EOI -- a stray EOI would retire another interrupt's in-service bit.
 * `metall_idt_setze` installs it.
 *
 * `metall_eintritt_zaehler_NAME` counts completed entries -- the report the
 * harness compares, and nothing the unit can see. */
struct metall_rahmen {
    uint64_t r15, r14, r13, r12, r11, r10, r9, r8, rbp, rdi, rsi, rdx, rcx, rbx, rax;
    uint64_t rip, cs, rflags, rsp, ss;   /* the interrupt frame */
};

/* -- The kernel service entry (OFFEN O31, Opus agent L). ---------------------
 *
 * A gate bound by `target … abi metal arch x86_64` lowers to `int $0x80`: the
 * number in rax, its parameters in the registers the binding names, the answer
 * in rax (`-errno` in -4095..-1, else the value) and NOTHING else destroyed.
 * The runtime installs the entry at vector 0x80 and hands the saved frame to
 * `metall_systemruf`, which the IMAGE supplies (weak: an image without it ends
 * the machine on the first call, status 9). The per-gate contract is the named
 * assumption the metal binding carries (`metal_kernel_contract` in the corpus).
 * A program with its own `entry … vector 0x80` (`beispiele/07`) takes the slot
 * instead and serves the calls itself. */
#define METALL_SYSTEMRUF_VEKTOR 0x80u
void metall_systemruf(struct metall_rahmen *r) __attribute__((weak));

void metall_eoi(void);
void metall_idt_setze(uint32_t vektor, void (*stub)(void));
void metall_ipi_fest(uint32_t kern_nr, uint32_t vektor);   /* fixed IPI to one core */
void metall_ipi_nmi(uint32_t kern_nr);                     /* NMI to one core */

#define METALL_EINTRITT(NAME, GEWORFEN, ...)                              \
    _Atomic uint32_t metall_eintritt_zaehler_##NAME;                      \
    void metall_eintritt_c_##NAME(struct metall_rahmen *r);               \
    void metall_eintritt_c_##NAME(struct metall_rahmen *r)                \
    {                                                                     \
        (void)r;                                                          \
        __VA_ARGS__;                                                      \
        atomic_fetch_add_explicit(&metall_eintritt_zaehler_##NAME, 1u,     \
                                  memory_order_release);                  \
        if (GEWORFEN) {                                                   \
            metall_eoi();                                                 \
        }                                                                 \
    }                                                                     \
    __asm__(".text\n\t.global gabbro_eintritt_" #NAME "\n"                \
            "gabbro_eintritt_" #NAME ":\n\t"                              \
            "pushq %rax\n\t"                                              \
            "movq $metall_eintritt_c_" #NAME ", %rax\n\t"                 \
            "jmp metall_eintritt_gemeinsam\n");

/* -- Entries on exceptions with a CPU error code (OFFEN O32 (9), Opus agent L).
 *
 * Vectors 8, 10..14, 17, 21, 29 and 30 push an error code the common stub must
 * drop before `iretq`: `METALL_EINTRITT_FC` jumps into the twin
 * `metall_eintritt_gemeinsam_fc` (eintritt_asm.h), and its C half sees the frame
 * WITH the code (`struct metall_rahmen_fc`: the registers at the same offsets
 * as `struct metall_rahmen`, so the same `r->rax` binding reads). Installed with
 * `metall_idt_setze_fc`, which takes ONLY those vectors -- the plain installer
 * keeps refusing them, so neither stub can land on the other's vector. */
struct metall_rahmen_fc {
    uint64_t r15, r14, r13, r12, r11, r10, r9, r8, rbp, rdi, rsi, rdx, rcx, rbx, rax;
    uint64_t fehlercode;
    uint64_t rip, cs, rflags, rsp, ss;
};

void metall_idt_setze_fc(uint32_t vektor, void (*stub)(void));

#define METALL_EINTRITT_FC(NAME, ...)                                     \
    _Atomic uint32_t metall_eintritt_zaehler_##NAME;                      \
    void metall_eintritt_c_##NAME(struct metall_rahmen *r);               \
    void metall_eintritt_c_##NAME(struct metall_rahmen *r)                \
    {                                                                     \
        struct metall_rahmen_fc *rf = (struct metall_rahmen_fc *)(void *)r; \
        (void)r;                                                          \
        (void)rf;                                                         \
        __VA_ARGS__;                                                      \
        atomic_fetch_add_explicit(&metall_eintritt_zaehler_##NAME, 1u,     \
                                  memory_order_release);                  \
    }                                                                     \
    __asm__(".text\n\t.global gabbro_eintritt_" #NAME "\n"                \
            "gabbro_eintritt_" #NAME ":\n\t"                              \
            "pushq %rax\n\t"                                              \
            "movq $metall_eintritt_c_" #NAME ", %rax\n\t"                 \
            "jmp metall_eintritt_gemeinsam_fc\n");

/* -- The core limit (Opus agent J). ------------------------------------------
 *
 * `METALL_KERNE_GRENZE(n)` in a driver sets the most cores the image brings
 * up to `n` (at most `METALL_KERNE_MAX`). A unit with `accumulates ... per cpu
 * N` indexes its cells with `gabbro_kern()`, whose contract is "below N"; the
 * driver passes the SMALLEST cell count, read off the arrays themselves
 * (`sizeof a / sizeof a[0]`, a constant the compiler computes), so the
 * contract holds by construction. `METALL_MIN` for the chain. */
#define METALL_MIN(a, b) ((a) < (b) ? (a) : (b))
#define METALL_ZELLEN(a) ((uint32_t)(sizeof(a) / sizeof((a)[0])))
#define METALL_KERNE_GRENZE(n) const uint32_t metall_kerne_grenze = (n);

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
