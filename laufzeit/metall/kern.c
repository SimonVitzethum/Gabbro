/* laufzeit/metall/kern.c -- the bare-metal thread runtime (Opus agent I,
 * 2026-09-26).
 *
 * SIMON'S RULE (2026-09-26). Everything Gabbro can do must work FREESTANDING:
 * Gabbro exists for the Caprock microkernel, and a thread that needs Linux is
 * a thread Caprock cannot have. This file implements the thread interface of
 * `laufzeit/faden.h` -- the emitted C does not change by one byte -- on the
 * bare x86_64 machine: no libc, no kernel, no loader beyond Multiboot1.
 *
 * WHAT STANDS HERE, AND WHAT EACH PIECE RESTS ON (every item is a named
 * assumption in `grammatik/Grammatik/Zielsatz/Spec.lean`, hunk "BARE-METAL
 * RUNTIME", and in OFFEN O30):
 *
 *   serial      16550 at port 0x3F8, polled (LSR bit 5). The report channel.
 *   PIC         both 8259s masked (0xFF): no legacy interrupt ever arrives.
 *   IDT         vectors 0..31 report and stop (start.S), 0x40 the LAPIC
 *               timer, 0xFF the LAPIC spurious vector.
 *   MADT        the ACPI table names the cores (type 0 entries, enabled or
 *               online-capable). RSDP found by signature and checksum in the
 *               EBDA's first KiB and 0xE0000..0xFFFFF (ACPI 1.0 RSDT).
 *   SMP         per AP: INIT, ~10 ms, SIPI(0x08), ~200 us, SIPI(0x08), wait
 *               for the check-in -- one AP at a time, so the trampoline page
 *               and its three parameter words are never shared.
 *   per core    `struct kern`, its address in IA32_GS_BASE; `%gs:0` is the
 *               self pointer, so "which core am I" is one load.
 *   scheduler   one FIFO run queue per core under a ticket lock; a thread is
 *               placed on a core at its start (round robin over the cores,
 *               beginning at core 1) and stays there. Round robin within a
 *               core: a yielding or preempted thread goes to the queue's tail.
 *   preemption  the LAPIC timer, periodic, vector 0x40: the running thread is
 *               switched out at the end of every quantum. With it, a thread
 *               that spins on another thread of the SAME core (a lock whose
 *               holder was preempted, an atomic flag) gets the core back
 *               within one round of the queue -- round-robin fairness, the
 *               scheduler property the model's liveness legs name.
 *   join        a waiter re-reads the join word (acquire) and YIELDS its core
 *               between reads: blocking in the scheduler's sense (the core
 *               runs the rest of its queue), with no IPI and no wake list.
 *               Justification below at `gabbro_faden_warte`.
 *   idle root   a core with an empty queue spins with `pause` in its
 *               scheduler loop, interrupts off: it touches no Gabbro carrier,
 *               which is `none` of `E.P.mitRuhe`.
 *
 * INTERRUPT DISCIPLINE (the one rule that keeps the runtime's own locks
 * deadlock-free under preemption): every runtime-internal lock (run queues,
 * thread table, serial) is taken with IF = 0 and released before IF returns.
 * The timer can therefore never interrupt a holder of a runtime lock, and its
 * handler takes one (the run queue, through the scheduler) only on the core's
 * own scheduler stack. Gabbro's own locks (`L_nimm`) are taken with IF = 1:
 * a holder may be preempted, a waiter spins or is preempted, and the ticket
 * order is untouched by either.
 */

#include <stdint.h>
#include <stdatomic.h>
#include "metall.h"

/* -- The compiler's four freestanding obligations. --------------------------
 *
 * GCC may emit calls to memcpy/memset/memmove/memcmp even under
 * `-ffreestanding -fno-builtin` (struct copies, zero initialisation). There
 * is no libc to supply them, so the runtime does, byte by byte: the image is
 * a test harness for the thread runtime, not a place to be fast. */
void *memcpy(void *d, const void *s, unsigned long n)
{
    unsigned char *dd = d;
    const unsigned char *ss = s;
    while (n--) {
        *dd++ = *ss++;
    }
    return d;
}

void *memmove(void *d, const void *s, unsigned long n)
{
    unsigned char *dd = d;
    const unsigned char *ss = s;
    if (dd < ss) {
        while (n--) {
            *dd++ = *ss++;
        }
    } else {
        while (n--) {
            dd[n] = ss[n];
        }
    }
    return d;
}

void *memset(void *d, int c, unsigned long n)
{
    unsigned char *dd = d;
    while (n--) {
        *dd++ = (unsigned char)c;
    }
    return d;
}

int memcmp(const void *a, const void *b, unsigned long n)
{
    const unsigned char *x = a, *y = b;
    for (unsigned long i = 0; i < n; i++) {
        if (x[i] != y[i]) {
            return x[i] < y[i] ? -1 : 1;
        }
    }
    return 0;
}

/* -- Ports, MSRs, flags. ---------------------------------------------------- */

static inline void outb(uint16_t p, uint8_t v) { __asm__ __volatile__("outb %0, %1" :: "a"(v), "Nd"(p)); }
static inline uint8_t inb(uint16_t p) { uint8_t v; __asm__ __volatile__("inb %1, %0" : "=a"(v) : "Nd"(p)); return v; }
static inline void outl(uint16_t p, uint32_t v) { __asm__ __volatile__("outl %0, %1" :: "a"(v), "Nd"(p)); }

static inline void wrmsr(uint32_t m, uint64_t v)
{
    __asm__ __volatile__("wrmsr" :: "c"(m), "a"((uint32_t)v), "d"((uint32_t)(v >> 32)));
}

/* Interrupts off, returning the old flags; and back. Every runtime-internal
 * lock is held inside such a pair (the interrupt discipline above). */
static inline uint64_t ia_aus(void)
{
    uint64_t f;
    __asm__ __volatile__("pushfq; popq %0; cli" : "=r"(f) :: "memory");
    return f;
}
static inline void ia_her(uint64_t f)
{
    __asm__ __volatile__("pushq %0; popfq" :: "r"(f) : "memory", "cc");
}

static inline void pause(void) { __asm__ __volatile__("pause" ::: "memory"); }

/* Roughly one microsecond per write on PC hardware (the classic ISA delay
 * port). The SMP protocol's waits are expressed in it; their length is a
 * named assumption, not a measurement. */
static void io_warte(uint32_t us)
{
    while (us--) {
        outb(0x80, 0);
    }
}

/* -- Serial: the report channel (0x3F8). ------------------------------------ */

static metall_ticket ausgabe_sperre;

static void seriell_init(void)
{
    outb(0x3F8 + 1, 0x00);   /* no UART interrupts */
    outb(0x3F8 + 3, 0x80);   /* DLAB */
    outb(0x3F8 + 0, 0x01);   /* 115200 baud */
    outb(0x3F8 + 1, 0x00);
    outb(0x3F8 + 3, 0x03);   /* 8N1 */
    outb(0x3F8 + 2, 0xC7);   /* FIFO on, cleared */
}

static void seriell_zeichen(char c)
{
    while ((inb(0x3F8 + 5) & 0x20) == 0) {
        pause();
    }
    outb(0x3F8, (uint8_t)c);
}

static void schreibe_roh(const char *s)
{
    while (*s) {
        seriell_zeichen(*s++);
    }
}

static void zahl_roh(uint64_t v)
{
    char b[24];
    int i = 0;
    do {
        b[i++] = (char)('0' + v % 10u);
        v /= 10u;
    } while (v != 0u);
    while (i > 0) {
        seriell_zeichen(b[--i]);
    }
}

static void hex_roh(uint64_t v)
{
    schreibe_roh("0x");
    for (int s = 60; s >= 0; s -= 4) {
        seriell_zeichen("0123456789abcdef"[(v >> s) & 15u]);
    }
}

void metall_schreibe(const char *s)
{
    uint64_t f = ia_aus();
    metall_ticket_nimm(&ausgabe_sperre);
    schreibe_roh(s);
    metall_ticket_gib(&ausgabe_sperre);
    ia_her(f);
}

void metall_zahl(uint64_t v)
{
    uint64_t f = ia_aus();
    metall_ticket_nimm(&ausgabe_sperre);
    zahl_roh(v);
    metall_ticket_gib(&ausgabe_sperre);
    ia_her(f);
}

/* The end of the machine. QEMU's `isa-debug-exit` device at port 0xF4 turns
 * the written value v into the process status (v << 1) | 1; on hardware
 * without the device the write does nothing and the core halts. The report
 * line comes first: the harness reads the serial log, not the status.
 *
 * Before it: METALL-VERTEILUNG, the number of threads that ENDED on each core
 * (core 0 first). Placement is round robin from core 1 and the driver thread
 * is the only starter in the harness images, so the line is deterministic
 * and says where the declared starts ran -- the measured form of "boot
 * `concurrent` starts are distributed over the cores". */
static void verteilung_melden(void);

__attribute__((noreturn)) void metall_ende(int code)
{
    (void)ia_aus();
    verteilung_melden();
    schreibe_roh("METALL-ENDE ");
    zahl_roh((uint64_t)(uint32_t)code);
    seriell_zeichen('\n');
    outl(0xF4, code == 0 ? 0x10u : 0x11u);
    for (;;) {
        __asm__ __volatile__("cli; hlt");
    }
}

/* -- CPU exceptions: loud, never silent (start.S jumps here). -------------- */

__attribute__((noreturn)) void metall_ausnahme(uint64_t vektor, uint64_t fehler, uint64_t rip);
__attribute__((noreturn)) void metall_ausnahme(uint64_t vektor, uint64_t fehler, uint64_t rip)
{
    schreibe_roh("METALL-AUSNAHME vector ");
    zahl_roh(vektor);
    schreibe_roh(" error ");
    hex_roh(fehler);
    schreibe_roh(" rip ");
    hex_roh(rip);
    seriell_zeichen('\n');
    metall_ende(2);
}

/* -- The IDT. --------------------------------------------------------------- */

struct idt_eintrag {
    uint16_t off0;
    uint16_t sel;
    uint8_t ist;
    uint8_t art;
    uint16_t off1;
    uint32_t off2;
    uint32_t null;
} __attribute__((packed));

static struct idt_eintrag idt[256] __attribute__((aligned(16)));

struct idt_zeiger {
    uint16_t grenze;
    uint64_t basis;
} __attribute__((packed));

extern char metall_ausnahme_0[], metall_ausnahme_1[], metall_ausnahme_2[], metall_ausnahme_3[],
    metall_ausnahme_4[], metall_ausnahme_5[], metall_ausnahme_6[], metall_ausnahme_7[],
    metall_ausnahme_8[], metall_ausnahme_9[], metall_ausnahme_10[], metall_ausnahme_11[],
    metall_ausnahme_12[], metall_ausnahme_13[], metall_ausnahme_14[], metall_ausnahme_15[],
    metall_ausnahme_16[], metall_ausnahme_17[], metall_ausnahme_18[], metall_ausnahme_19[],
    metall_ausnahme_20[], metall_ausnahme_21[], metall_ausnahme_22[], metall_ausnahme_23[],
    metall_ausnahme_24[], metall_ausnahme_25[], metall_ausnahme_26[], metall_ausnahme_27[],
    metall_ausnahme_28[], metall_ausnahme_29[], metall_ausnahme_30[], metall_ausnahme_31[];
extern char metall_takt_eintritt[], metall_unecht[];

static void idt_setze(int v, void *ziel)
{
    uint64_t a = (uint64_t)ziel;
    idt[v].off0 = (uint16_t)a;
    idt[v].sel = 0x18;          /* SEL_CODE64 */
    idt[v].ist = 0;
    idt[v].art = 0x8E;          /* present, DPL 0, 64-bit INTERRUPT gate: IF cleared on entry */
    idt[v].off1 = (uint16_t)(a >> 16);
    idt[v].off2 = (uint32_t)(a >> 32);
    idt[v].null = 0;
}

static void idt_bau(void)
{
    void *t[32] = {
        metall_ausnahme_0, metall_ausnahme_1, metall_ausnahme_2, metall_ausnahme_3,
        metall_ausnahme_4, metall_ausnahme_5, metall_ausnahme_6, metall_ausnahme_7,
        metall_ausnahme_8, metall_ausnahme_9, metall_ausnahme_10, metall_ausnahme_11,
        metall_ausnahme_12, metall_ausnahme_13, metall_ausnahme_14, metall_ausnahme_15,
        metall_ausnahme_16, metall_ausnahme_17, metall_ausnahme_18, metall_ausnahme_19,
        metall_ausnahme_20, metall_ausnahme_21, metall_ausnahme_22, metall_ausnahme_23,
        metall_ausnahme_24, metall_ausnahme_25, metall_ausnahme_26, metall_ausnahme_27,
        metall_ausnahme_28, metall_ausnahme_29, metall_ausnahme_30, metall_ausnahme_31,
    };
    for (int i = 0; i < 32; i++) {
        idt_setze(i, t[i]);
    }
    idt_setze(0x40, metall_takt_eintritt);
    idt_setze(0xFF, metall_unecht);
}

static void idt_lade(void)
{
    struct idt_zeiger z = { sizeof(idt) - 1, (uint64_t)idt };
    __asm__ __volatile__("lidt %0" :: "m"(z));
}

/* -- The LAPIC. ------------------------------------------------------------- */

static volatile uint32_t *lapic = (volatile uint32_t *)0xFEE00000u;

static inline uint32_t lapic_lies(uint32_t r) { return lapic[r / 4u]; }
static inline void lapic_schreib(uint32_t r, uint32_t v) { lapic[r / 4u] = v; }

#define LAPIC_ID      0x020u
#define LAPIC_EOI     0x0B0u
#define LAPIC_SVR     0x0F0u
#define LAPIC_ICR_LO  0x300u
#define LAPIC_ICR_HI  0x310u
#define LAPIC_LVT_T   0x320u
#define LAPIC_T_INIT  0x380u
#define LAPIC_T_TEIL  0x3E0u

#define TAKT_VEKTOR   0x40u

/* The quantum. The LAPIC timer counts the bus clock divided by 16; at QEMU's
 * nominal 1 GHz that is 1.6 ms per quantum. The LENGTH is not a guarantee of
 * the runtime -- only that every quantum ENDS (periodic mode) is. */
#ifndef METALL_QUANTUM
#define METALL_QUANTUM 100000u
#endif

static void lapic_an(void)
{
    lapic_schreib(LAPIC_SVR, 0x100u | 0xFFu);  /* software enable, spurious 0xFF */
}

static void takt_an(void)
{
#ifndef METALL_KOOPERATIV
    lapic_schreib(LAPIC_T_TEIL, 0x3u);                       /* divide by 16 */
    lapic_schreib(LAPIC_LVT_T, TAKT_VEKTOR | (1u << 17));    /* periodic */
    lapic_schreib(LAPIC_T_INIT, METALL_QUANTUM);
#endif
}

static void icr_warte(void)
{
    while (lapic_lies(LAPIC_ICR_LO) & (1u << 12)) {
        pause();
    }
}

static void ipi(uint32_t apic_id, uint32_t wort)
{
    lapic_schreib(LAPIC_ICR_HI, apic_id << 24);
    lapic_schreib(LAPIC_ICR_LO, wort);
    icr_warte();
}

/* -- Cores and threads. ----------------------------------------------------- */

#define KERNE_MAX 16
#define FAEDEN_MAX 64
#define KERN_STAPEL 16384

enum { FREI = 0, BEREIT, LAEUFT, TOT };

struct faden {
    uint64_t rsp;                /* saved stack pointer while switched out */
    void (*fn)(void);
    uint32_t *wort;              /* the join word the starter waits on */
    int zustand;
    struct faden *naechster;     /* run-queue link */
};

struct kern {
    struct kern *selbst;         /* %gs:0 -- must stay the first field */
    uint32_t nr;                 /* index 0..n-1 */
    uint32_t apic_id;
    uint64_t sched_rsp;          /* the scheduler loop's saved rsp */
    struct faden *laufend;
    metall_ticket schlange_sperre;
    struct faden *kopf, *schwanz;
    uint64_t gelaufen;           /* threads this core has run to their end */
};

static struct kern kerne[KERNE_MAX];
static _Atomic uint32_t n_kerne = 1;
static uint8_t kern_stapel[KERNE_MAX][KERN_STAPEL] __attribute__((aligned(16)));

static struct faden faeden[FAEDEN_MAX];
static metall_ticket faeden_sperre;
static _Atomic uint32_t naechster_kern = 1;   /* round robin, from core 1 */

static void verteilung_melden(void)
{
    uint32_t n = atomic_load_explicit(&n_kerne, memory_order_acquire);
    schreibe_roh("METALL-VERTEILUNG");
    for (uint32_t i = 0; i < n; i++) {
        seriell_zeichen(' ');
        zahl_roh(kerne[i].gelaufen);
    }
    seriell_zeichen('\n');
}

static inline struct kern *ich(void)
{
    struct kern *k;
    __asm__ __volatile__("movq %%gs:0, %0" : "=r"(k));
    return k;
}

uint32_t metall_kerne(void) { return atomic_load_explicit(&n_kerne, memory_order_acquire); }
uint32_t metall_kern_nr(void) { return ich()->nr; }

static void kern_setze(uint32_t nr)
{
    kerne[nr].selbst = &kerne[nr];
    kerne[nr].nr = nr;
    wrmsr(0xC0000101u, (uint64_t)&kerne[nr]);   /* IA32_GS_BASE */
}

/* Run queue, FIFO. Caller holds IF = 0. */
static void schlange_haenge(struct kern *k, struct faden *f)
{
    metall_ticket_nimm(&k->schlange_sperre);
    f->naechster = 0;
    if (k->schwanz) {
        k->schwanz->naechster = f;
    } else {
        k->kopf = f;
    }
    k->schwanz = f;
    metall_ticket_gib(&k->schlange_sperre);
}

static struct faden *schlange_nimm(struct kern *k)
{
    struct faden *f;
    metall_ticket_nimm(&k->schlange_sperre);
    f = k->kopf;
    if (f) {
        k->kopf = f->naechster;
        if (!k->kopf) {
            k->schwanz = 0;
        }
    }
    metall_ticket_gib(&k->schlange_sperre);
    return f;
}

void metall_schalte(uint64_t *alt_rsp, uint64_t neu_rsp);   /* start.S */

/* Give the core back to its scheduler. Callable from thread context with any
 * IF: the switch itself runs with IF = 0 (see start.S), and the old flags
 * come back when the thread is resumed. */
static void abgeben(void)
{
    uint64_t f = ia_aus();
    struct kern *k = ich();
    struct faden *t = k->laufend;
    metall_schalte(&t->rsp, k->sched_rsp);
    ia_her(f);
}

/* The public yield (metall.h): the Gabbro lock's spin calls it. */
void metall_abgeben(void)
{
    abgeben();
}

/* The timer's C half (start.S `metall_takt_eintritt`, IF = 0, all of the
 * thread's registers saved on its own stack). Acknowledge, then yield: the
 * preempted thread goes to the tail of its core's queue. */
void metall_takt(void);
void metall_takt(void)
{
    lapic_schreib(LAPIC_EOI, 0);
    if (ich()->laufend) {
        abgeben();
    }
}

/* The first instruction a new thread executes (reached by the `ret` of
 * `metall_schalte`, rsp = top - 8, the post-call alignment). It runs the root,
 * marks itself dead and leaves its stack for good. The word is NOT cleared
 * here: the thread is still standing on the unit's stack, and the starter may
 * reuse that stack the moment the join returns. The scheduler clears it
 * from the core's own stack (`begrabe`). */
static __attribute__((noreturn)) void faden_eintritt(void)
{
    struct kern *k = ich();
    struct faden *t = k->laufend;
    __asm__ __volatile__("sti" ::: "memory");
    t->fn();
    (void)ia_aus();
    k = ich();
    t->zustand = TOT;
    metall_schalte(&t->rsp, k->sched_rsp);
    __builtin_trap();   /* a dead thread is never resumed */
}

static void begrabe(struct faden *t)
{
    uint32_t *w = t->wort;
    metall_ticket_nimm(&faeden_sperre);
    t->zustand = FREI;
    metall_ticket_gib(&faeden_sperre);
    /* The join edge: everything the thread wrote happens-before this store,
     * and the waiter's acquire load of zero synchronises with it. */
    atomic_store_explicit((_Atomic uint32_t *)w, 0u, memory_order_release);
}

/* The scheduler loop of one core, on the core's own stack, IF = 0 throughout.
 * An empty queue is the idle root: `pause`, touch nothing, look again. */
static __attribute__((noreturn)) void kern_schleife(void)
{
    struct kern *k = ich();
    for (;;) {
        struct faden *t = schlange_nimm(k);
        if (!t) {
            pause();
            continue;
        }
        t->zustand = LAEUFT;
        k->laufend = t;
        metall_schalte(&k->sched_rsp, t->rsp);
        k->laufend = 0;
        if (t->zustand == TOT) {
            k->gelaufen++;
            begrabe(t);
        } else {
            t->zustand = BEREIT;
            schlange_haenge(k, t);
        }
    }
}

/* The frame `metall_schalte` pops for a thread that has never run: MXCSR and
 * x87 control word at their reset values, six zero callee-saved registers,
 * the entry as return address, a zero fake return address above it. */
static uint64_t rahmen_neu(void *spitze)
{
    uint64_t *s = (uint64_t *)spitze;
    *--s = 0;                              /* faden_eintritt's "return address" */
    *--s = (uint64_t)faden_eintritt;       /* ret target */
    for (int i = 0; i < 6; i++) {
        *--s = 0;                          /* rbp rbx r12 r13 r14 r15 */
    }
    *--s = 0x1F80u | ((uint64_t)0x037Fu << 32);  /* MXCSR | FCW << 32 */
    return (uint64_t)s;
}

static int faden_anlegen(void (*fn)(void), void *spitze, uint32_t *wort, uint32_t kern_nr)
{
    struct faden *t = 0;
    uint64_t f;
    if (fn == 0 || spitze == 0 || wort == 0) {
        return 22;
    }
    if (((uintptr_t)spitze & 15u) != 0u) {
        return 22;
    }
    f = ia_aus();
    metall_ticket_nimm(&faeden_sperre);
    for (int i = 0; i < FAEDEN_MAX; i++) {
        if (faeden[i].zustand == FREI) {
            t = &faeden[i];
            t->zustand = BEREIT;
            break;
        }
    }
    metall_ticket_gib(&faeden_sperre);
    if (!t) {
        ia_her(f);
        return 11;
    }
    t->fn = fn;
    t->wort = wort;
    t->rsp = rahmen_neu(spitze);
    /* The word is nonzero BEFORE the thread can run: a join that starts after
     * this call returns can never read a stale zero, and a thread that ends
     * before the starter looks again clears a word that already says "alive"
     * (the order the Linux runtime needs CLONE_PARENT_SETTID for). */
    atomic_store_explicit((_Atomic uint32_t *)wort, (uint32_t)(t - faeden) + 1u, memory_order_release);
    schlange_haenge(&kerne[kern_nr], t);
    ia_her(f);
    return 0;
}

int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort)
{
    uint32_t n = metall_kerne();
    uint32_t k = atomic_fetch_add_explicit(&naechster_kern, 1u, memory_order_relaxed) % n;
    return faden_anlegen(fn, spitze, wort, k);
}

/* THE JOIN: re-read with acquire until zero; between reads, give the core
 * away. WHY NOT hlt + IPI: a sleeping waiter needs a wake list per word and
 * an IPI from the ending thread's core, i.e. a second protocol with its own
 * lost-wakeup race to prove; the yield loop has none -- every path re-reads
 * the word, exactly the shape of the hosted futex loop. Its cost is a waiter
 * that stays in its core's queue, which with a round-robin queue costs the
 * other threads of that core one short turn per round and costs a core with
 * nothing else to do nothing at all. */
void gabbro_faden_warte(uint32_t *wort)
{
    while (atomic_load_explicit((_Atomic uint32_t *)wort, memory_order_acquire) != 0u) {
        abgeben();
        pause();
    }
}

/* -- ACPI: which cores exist. ----------------------------------------------- */

/* A physical address as a pointer. The empty asm hides the constant from the
 * optimiser: GCC otherwise treats a pointer below 4 KiB as "probably null" and
 * refuses the read at `-Werror=array-bounds` -- but 0x40E (the EBDA segment)
 * and 0x8000 (the trampoline page) ARE memory on this machine. */
static inline void *phys(uint64_t a)
{
    __asm__("" : "+r"(a));
    return (void *)a;
}

static int summe_null(const uint8_t *p, uint32_t n)
{
    uint8_t s = 0;
    for (uint32_t i = 0; i < n; i++) {
        s = (uint8_t)(s + p[i]);
    }
    return s == 0;
}

static const uint8_t *rsdp_suche(uint64_t von, uint64_t bis)
{
    for (uint64_t a = von; a + 20 <= bis; a += 16) {
        const uint8_t *p = (const uint8_t *)phys(a);
        if (p[0] == 'R' && p[1] == 'S' && p[2] == 'D' && p[3] == ' ' && p[4] == 'P' &&
            p[5] == 'T' && p[6] == 'R' && p[7] == ' ' && summe_null(p, 20)) {
            return p;
        }
    }
    return 0;
}

static uint32_t apic_ids[KERNE_MAX];
static uint32_t n_apic;

static void madt_lies(void)
{
    uint64_t ebda = (uint64_t)(*(volatile uint16_t *)phys(0x40Eu)) << 4;
    const uint8_t *rsdp = 0;
    const uint8_t *rsdt;
    uint32_t len;
    n_apic = 0;
    if (ebda >= 0x80000u && ebda < 0xA0000u) {
        rsdp = rsdp_suche(ebda, ebda + 1024);
    }
    if (!rsdp) {
        rsdp = rsdp_suche(0xE0000u, 0x100000u);
    }
    if (!rsdp) {
        return;
    }
    rsdt = (const uint8_t *)(uint64_t)*(const uint32_t *)(rsdp + 16);
    len = *(const uint32_t *)(rsdt + 4);
    for (uint32_t o = 36; o + 4 <= len; o += 4) {
        const uint8_t *t = (const uint8_t *)(uint64_t)*(const uint32_t *)(rsdt + o);
        if (t[0] == 'A' && t[1] == 'P' && t[2] == 'I' && t[3] == 'C') {
            uint32_t tl = *(const uint32_t *)(t + 4);
            lapic = (volatile uint32_t *)(uint64_t)*(const uint32_t *)(t + 36);
            for (uint32_t e = 44; e + 2 <= tl && n_apic < KERNE_MAX;) {
                uint8_t art = t[e], el = t[e + 1];
                if (el < 2) {
                    break;
                }
                if (art == 0 && el >= 8) {
                    uint32_t fl = *(const uint32_t *)(t + e + 4);
                    if (fl & 3u) {
                        apic_ids[n_apic++] = t[e + 3];
                    }
                }
                e += el;
            }
            return;
        }
    }
}

/* -- SMP bring-up. ---------------------------------------------------------- */

extern char tramp_anfang[], tramp_ende[], tramp_cr3[], tramp_stapel[], tramp_ziel[];
extern char pml4[];
static _Atomic uint32_t ap_angekommen;
static uint32_t ap_nr;

static __attribute__((noreturn)) void metall_ap(void);
static __attribute__((noreturn)) void metall_ap(void)
{
    kern_setze(ap_nr);
    idt_lade();
    lapic_an();
    kerne[ap_nr].apic_id = lapic_lies(LAPIC_ID) >> 24;
    takt_an();
    atomic_store_explicit(&ap_angekommen, 1u, memory_order_release);
    kern_schleife();
}

#define TRAMP 0x8000u
#define TRAMP_WORT(sym) ((uint64_t *)phys(TRAMP + (uint64_t)((sym) - tramp_anfang)))

static void aps_starten(void)
{
    uint32_t selbst = lapic_lies(LAPIC_ID) >> 24;
    memcpy(phys(TRAMP), tramp_anfang, (unsigned long)(tramp_ende - tramp_anfang));
    for (uint32_t i = 0; i < n_apic; i++) {
        uint32_t id = apic_ids[i];
        uint32_t nr = atomic_load_explicit(&n_kerne, memory_order_relaxed);
        if (id == selbst || nr >= KERNE_MAX) {
            continue;
        }
        ap_nr = nr;
        *TRAMP_WORT(tramp_cr3) = (uint64_t)pml4;
        *TRAMP_WORT(tramp_stapel) = (uint64_t)&kern_stapel[nr][KERN_STAPEL];
        *TRAMP_WORT(tramp_ziel) = (uint64_t)metall_ap;
        atomic_store_explicit(&ap_angekommen, 0u, memory_order_release);
        ipi(id, 0x4500u);                 /* INIT, assert */
        io_warte(10000);
        ipi(id, 0x4600u | (TRAMP >> 12)); /* STARTUP, vector 0x08 */
        io_warte(200);
        if (!atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
            ipi(id, 0x4600u | (TRAMP >> 12));
        }
        for (uint32_t w = 0; w < 1000000u; w++) {
            if (atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
                break;
            }
            io_warte(1);
        }
        if (atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
            atomic_store_explicit(&n_kerne, nr + 1u, memory_order_release);
        } else {
            schreibe_roh("METALL: core with APIC id ");
            zahl_roh(id);
            schreibe_roh(" did not check in\n");
        }
    }
}

/* -- The BSP. --------------------------------------------------------------- */

static uint8_t haupt_stapel[65536] __attribute__((aligned(16)));
static uint32_t haupt_wort;

static void haupt_huelle(void)
{
    metall_ende(gabbro_metall_haupt());
}

__attribute__((noreturn)) void metall_bsp(void);
__attribute__((noreturn)) void metall_bsp(void)
{
    seriell_init();
    outb(0x21, 0xFF);                     /* mask both 8259s */
    outb(0xA1, 0xFF);
    kern_setze(0);
    idt_bau();
    idt_lade();
    madt_lies();
    lapic_an();
    kerne[0].apic_id = lapic_lies(LAPIC_ID) >> 24;
    aps_starten();
    schreibe_roh("METALL-KERNE ");
    zahl_roh(metall_kerne());
    seriell_zeichen('\n');
    /* The driver's thread starts on core 0; its roots go round robin from
     * core 1, so with more than one core the declared starts run on other
     * cores than their starter. */
    if (faden_anlegen(haupt_huelle, &haupt_stapel[sizeof(haupt_stapel)], &haupt_wort, 0) != 0) {
        metall_ende(3);
    }
    takt_an();
    kern_schleife();
}
