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
 *               timer, 0x41 the wake IPI, 0xFF the LAPIC spurious vector;
 *               every other slot is free for the PROGRAM's own entries
 *               (`metall_idt_setze`, Opus agent J; an exception vector
 *               without a CPU error code may be taken too, e.g. an NMI).
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
 *   idle root   a core with an empty queue sleeps in `sti; hlt` in its
 *               scheduler loop (Opus agent J; `pause` before), woken by the
 *               timer or by the wake IPI a cross-core start sends: it touches
 *               no Gabbro carrier, which is `none` of `E.P.mitRuhe`.
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
#include "eintritt_asm.h"
#include <string.h>   /* the generated header: the four memory functions */

/* -- The compiler's four freestanding obligations (memcpy, memmove, memset,
 * memcmp) are GENERATED text since the C-free lane's C3 slice 1: the build
 * writes them beside the image (`treiber.rs::METALL_SPEICHER`, template
 * `metall.speicher`), and a harness takes them from `gabbro runtime
 * metal-memory`. */

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

/* -- The IDT: GENERATED text since the C-free lane's C3 slice 3 (2026-10-05) -- --------
 * `<unit>.metall.idt.c` (template `idt.metall`, Grammatik/SchablonenMetallIdt.lean):
 * `metall_idt_bau`, `metall_idt_lade`, `metall_idt_setze`, `metall_idt_setze_fc`. */

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

#define TAKT_VEKTOR   METALL_TAKT_VEKTOR
#define WECK_VEKTOR   METALL_WECK_VEKTOR

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

void metall_ipi_senden(uint32_t apic_id, uint32_t wort)
{
    lapic_schreib(LAPIC_ICR_HI, apic_id << 24);
    lapic_schreib(LAPIC_ICR_LO, wort);
    icr_warte();
}

/* -- Cores and threads: GENERATED text since the C-free lane's C3 slice 4 (2026-10-05) --
 * `<unit>.metall.faden.c` (template `faden.metall`, Grammatik/SchablonenMetallFaden.lean):
 * the run queues, the scheduler loop, the thread start and join, `metall_abgeben`,
 * `metall_takt`, `metall_kerne`, `metall_kern_nr`. What the bring-up below needs of it is
 * declared in metall.h. */

#define KERNE_MAX METALL_KERNE_MAX

static void verteilung_melden(void)
{
    uint32_t n = metall_kerne();
    schreibe_roh("METALL-VERTEILUNG");
    for (uint32_t i = 0; i < n; i++) {
        seriell_zeichen(' ');
        zahl_roh(metall_kern_gelaufen(i));
    }
    seriell_zeichen('\n');
}
/* -- The program's own entries (Opus agent J; metall.h METALL_EINTRITT). -- */

void metall_wecken(void);
void metall_wecken(void)
{
    lapic_schreib(LAPIC_EOI, 0);
}

/* The kernel service entry's C half (OFFEN O31). The image's kernel -- Caprock,
 * or a C body the image links -- supplies `metall_systemruf` and answers every
 * number it serves in `r->rax` under the Linux x86_64 convention (`-errno` in
 * -4095..-1, else the value). An image that supplies none ends the machine
 * loudly on the first gate call: a number nobody serves is never answered with
 * an invented errno (the stub hands an unlisted errno to the compiler as
 * unreachable). Runs with IF = 0 (an interrupt gate), on the caller's stack. */
__asm__(METALL_EINTRITT_GEMEINSAM_ASM);

void metall_systemruf_c(struct metall_rahmen *r);
void metall_systemruf_c(struct metall_rahmen *r)
{
    if (metall_systemruf) {
        metall_systemruf(r);
        return;
    }
    schreibe_roh("METALL: system call number ");
    zahl_roh(r->rax);
    schreibe_roh(" entered through vector 0x80, and the image supplies no kernel service\n");
    metall_ende(9);
}

void metall_eoi(void)
{
    lapic_schreib(LAPIC_EOI, 0);
}

void metall_eintritt_ohne_ziel(void)
{
    schreibe_roh("METALL: an entry without a dispatch target in this unit was entered\n");
    metall_ende(6);
}

void metall_eintritt_bindung_falsch(void)
{
    schreibe_roh("METALL: an entry whose regs in/out do not match its dispatch was entered\n");
    metall_ende(8);
}

__attribute__((noreturn)) void metall_fremd_fehlt(const char *name)
{
    (void)ia_aus();
    schreibe_roh("METALL: foreign body `");
    schreibe_roh(name);
    schreibe_roh("` was called and the image does not supply it (the program's own C does)\n");
    metall_ende(7);
}

/* The current core, for `accumulates ... per cpu N` (the emitter's foreign
 * body `gabbro_kern`, certificate section E: "it returns a core number below
 * the `per cpu` count, and nothing here proves that"). On bare metal the
 * runtime KNOWS the core: the answer is `%gs`'s core index, below
 * `metall_kerne()`. And `metall_kerne()` is below every `per cpu` count of
 * the image BY CONSTRUCTION: a driver whose unit has per-cpu cells defines
 * `metall_kerne_grenze` as the smallest cell count (`METALL_KERNE_GRENZE`,
 * metall.h, computed by the C compiler from the arrays themselves), and the
 * bring-up (`aps_starten`) starts no core at or above it. Cores the image
 * leaves down are idle hardware, not a Gabbro fact. Without cells the weak
 * default is `KERNE_MAX`. */
uint32_t gabbro_kern(void);
uint32_t gabbro_kern(void)
{
    return metall_kern_nr();
}

/* A fixed IPI to one core (by runtime core number). IF = 0 around the two
 * ICR writes: an entry on this core that sent an IPI itself would otherwise
 * interleave its own pair. */
void metall_ipi_fest(uint32_t kern_nr, uint32_t vektor)
{
    if (kern_nr >= metall_kerne() || vektor < 32u || vektor > 0xFEu) {
        return;
    }
    uint64_t f = ia_aus();
    metall_ipi_senden(metall_kern_apic(kern_nr), 0x4000u | vektor);
    ia_her(f);
}

/* An NMI to one core (delivery mode NMI, vector field ignored): what a program
 * entry on vector 2 answers. Not masked by IF, and acknowledged by `iretq`,
 * not by an EOI -- the stub of a vector below 32 writes none. */
void metall_ipi_nmi(uint32_t kern_nr)
{
    if (kern_nr >= metall_kerne()) {
        return;
    }
    uint64_t f = ia_aus();
    metall_ipi_senden(metall_kern_apic(kern_nr), 0x4400u);
    ia_her(f);
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

/* The driver's core limit (metall.h `METALL_KERNE_GRENZE`), weak: absent, the
 * address is 0 and the runtime's own maximum applies. At least 1 (the BSP). */
extern const uint32_t metall_kerne_grenze __attribute__((weak));
static uint32_t kerne_grenze(void)
{
    if (&metall_kerne_grenze == 0) {
        return KERNE_MAX;
    }
    return metall_kerne_grenze == 0u ? 1u : metall_kerne_grenze;
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
    metall_kern_setze(ap_nr);
    metall_idt_lade();
    lapic_an();
    metall_kern_apic_setze(ap_nr, lapic_lies(LAPIC_ID) >> 24);
    takt_an();
    atomic_store_explicit(&ap_angekommen, 1u, memory_order_release);
    metall_kern_schleife();
}

#define TRAMP 0x8000u
#define TRAMP_WORT(sym) ((uint64_t *)phys(TRAMP + (uint64_t)((sym) - tramp_anfang)))

static void aps_starten(void)
{
    uint32_t selbst = lapic_lies(LAPIC_ID) >> 24;
    memcpy(phys(TRAMP), tramp_anfang, (unsigned long)(tramp_ende - tramp_anfang));
    for (uint32_t i = 0; i < n_apic; i++) {
        uint32_t id = apic_ids[i];
        uint32_t nr = metall_kerne();
        if (id == selbst || nr >= KERNE_MAX || nr >= kerne_grenze()) {
            continue;
        }
        ap_nr = nr;
        *TRAMP_WORT(tramp_cr3) = (uint64_t)pml4;
        *TRAMP_WORT(tramp_stapel) = (uint64_t)metall_kern_stapel_oben(nr);
        *TRAMP_WORT(tramp_ziel) = (uint64_t)metall_ap;
        atomic_store_explicit(&ap_angekommen, 0u, memory_order_release);
        metall_ipi_senden(id, 0x4500u);                 /* INIT, assert */
        io_warte(10000);
        metall_ipi_senden(id, 0x4600u | (TRAMP >> 12)); /* STARTUP, vector 0x08 */
        io_warte(200);
        if (!atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
            metall_ipi_senden(id, 0x4600u | (TRAMP >> 12));
        }
        for (uint32_t w = 0; w < 1000000u; w++) {
            if (atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
                break;
            }
            io_warte(1);
        }
        if (atomic_load_explicit(&ap_angekommen, memory_order_acquire)) {
            metall_kern_angekommen(nr + 1u);
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
    metall_kern_setze(0);
    metall_idt_bau();
    metall_idt_lade();
    madt_lies();
    lapic_an();
    metall_kern_apic_setze(0, lapic_lies(LAPIC_ID) >> 24);
    aps_starten();
    schreibe_roh("METALL-KERNE ");
    zahl_roh(metall_kerne());
    seriell_zeichen('\n');
    /* The driver's thread starts on core 0; its roots go round robin from
     * core 1, so with more than one core the declared starts run on other
     * cores than their starter. */
    if (metall_faden_anlegen(haupt_huelle, &haupt_stapel[sizeof(haupt_stapel)], &haupt_wort, 0) != 0) {
        metall_ende(3);
    }
    takt_an();
    metall_kern_schleife();
}
