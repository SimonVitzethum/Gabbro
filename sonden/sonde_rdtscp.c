/* sonde_rdtscp -- the falsifier for the axiom `rdtscp`.
 *
 * THE ASSUMPTION, as the corpus declares it
 * (`beispiele/11-grammatikbefunde.gab`:17-20):
 *
 *     axiom rdtscp() -> u64
 *         requires Has(RDTSCP)
 *         effects { reads uhr }
 *         falsifier sonde_rdtscp;
 *
 * **Two halves, and the probe answers both.** The `requires` clause is a claim about the
 * MACHINE: that there is a feature bit, and that it is the right one to ask. The `effects`
 * clause is a claim about the instruction: that it reads a clock. A probe that only ran the
 * instruction would leave the precondition untested, and the precondition is the half that
 * decides whether the instruction may be reached at all.
 *
 * `dokumente/SONDENDECKUNG.md` names the probe in one line: *"`CPUID` leaf `0x8000'0001`,
 * then the instruction; **77** where the feature is absent."* This program is that line,
 * driven.
 *
 * WHAT IT MEASURES
 * ----------------
 *   the precondition -- CPUID leaf 0x80000001, EDX bit 27. Absent -> **77**, because
 *                       `requires Has(RDTSCP)` then holds vacuously and the axiom's effect
 *                       clause was never put to any test;
 *   `reads uhr`     -- the counter advances, and never steps back, on one held core;
 *   the SAME clock  -- `rdtscp` is bracketed by two `rdtsc` reads and must land between
 *                      them. *An instruction that read some other counter would satisfy
 *                      "advances" perfectly and still not be reading `uhr`* -- and nothing
 *                      in an advance-only check could tell the two apart.
 *
 * It does NOT judge the auxiliary word `rdtscp` leaves in ECX. Linux packs the processor
 * number into it, and the value is printed beside `sched_getcpu()` as data; the axiom says
 * `reads uhr` and nothing about a processor id, so a mismatch there is not this axiom's
 * refutation.
 *
 * THE THIRD STATE, AND IT IS REAL HERE
 * ------------------------------------
 * Two ways to reach **77**, and both are holes with a number rather than green ticks: the
 * feature bit is absent, or `CR4.TSD` (Linux: `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)`) makes the
 * instruction fault. In neither case was anything about the clock measured.
 *
 * THE ARMS THAT MAKE THE OTHERS READABLE
 * --------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * Every counter is read through a FUNCTION POINTER, and three arms run the identical
 * detectors over sources that violate the assumption by construction: one frozen, one
 * running backwards, one outside the bracket. **All three must be caught in every round.**
 * *If any of them goes through, the detector is blind, every green line below it is
 * worthless, and the probe ends with 1 over itself.*
 *
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no RDTSCP feature bit, no core to hold, or CR4.TSD
 */
#define _GNU_SOURCE
#include <sched.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#if !defined(__x86_64__) && !defined(__i386__)
int main(void)
{
    printf("sonde sonde_rdtscp :: rdtscp (beispiele/11-grammatikbefunde.gab:17)\n");
    printf("      no RDTSCP on this architecture -- not runnable here\n");
    return 77;
}
#else
#include <cpuid.h>

typedef unsigned long long u64;

static sigjmp_buf sprung;
static volatile sig_atomic_t gefaultet;

static void handler(int sig)
{
    (void)sig;
    gefaultet = 1;
    siglongjmp(sprung, 1);
}

static unsigned letzte_aux;

static u64 q_rdtscp(void)
{
    unsigned lo, hi, aux;
    __asm__ __volatile__("rdtscp" : "=a"(lo), "=d"(hi), "=c"(aux));
    letzte_aux = aux;
    return ((u64)hi << 32) | lo;
}

static u64 q_rdtsc(void)
{
    unsigned lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((u64)hi << 32) | lo;
}

/* **The three sources that violate the assumption by construction.** They are not analogies
 * of a broken clock, they ARE one -- the program itself promises the failure, so the
 * detector has nothing to be lucky about. */
static u64 q_eingefroren(void)
{
    static volatile u64 fest = 0x0123456789abcdefULL;
    return fest;
}

static u64 q_rueckwaerts(void)
{
    static volatile u64 zaehler = 0xffffffffffffff00ULL;
    zaehler -= 16u;
    return zaehler;
}

static u64 q_ausserhalb(void)
{
    static volatile u64 fest = UINT64_MAX;
    return fest;
}

#define GRENZE 64

struct befund {
    long stillstand;
    long rueckwaerts;
    long vorgerueckt;
    long max_lesungen;
};

static void pruefe_quelle(u64 (*quelle)(void), long runden, struct befund *b)
{
    memset(b, 0, sizeof *b);
    for (long r = 0; r < runden; r++) {
        u64 v0 = quelle();
        long n = 1;
        int rueck = 0, vor = 0;
        for (; n <= GRENZE; n++) {
            u64 v = quelle();
            if (v < v0) {
                rueck = 1;
                break;
            }
            if (v > v0) {
                vor = 1;
                break;
            }
        }
        if (n > b->max_lesungen) {
            b->max_lesungen = n;
        }
        if (rueck) {
            b->rueckwaerts++;
        } else if (vor) {
            b->vorgerueckt++;
        } else {
            b->stillstand++;
        }
    }
}

/* **Is it the SAME clock?** One `rdtsc` before, one after; the middle read must land between
 * them. Returns the number of rounds in which it did not. */
static long verschraenkt(u64 (*mitte)(void), long runden)
{
    long verletzt = 0;
    for (long r = 0; r < runden; r++) {
        u64 a = q_rdtsc();
        u64 m = mitte();
        u64 b = q_rdtsc();
        if (!(a <= m && m <= b)) {
            verletzt++;
        }
    }
    return verletzt;
}

int main(int argc, char **argv)
{
    printf("sonde sonde_rdtscp :: rdtscp -- requires Has(RDTSCP), effects { reads uhr } "
           "(beispiele/11-grammatikbefunde.gab:17)\n");

    /* **The round count is CAPPED and the cap stands in the output.** A control round costs
     * up to GRENZE reads, so the runner's 2 000 000 would be 128 million of them. */
    long gewuenscht = (argc > 1) ? strtol(argv[1], NULL, 10) : 200000;
    if (gewuenscht < 1) {
        gewuenscht = 1;
    }
    const long DECKEL = 200000;
    long runden = (gewuenscht > DECKEL) ? DECKEL : gewuenscht;

    /* ---- The PRECONDITION: `requires Has(RDTSCP)`, read out of CPUID. ---- */
    unsigned eax = 0, ebx = 0, ecx = 0, edx = 0;
    unsigned max_erweitert = __get_cpuid_max(0x80000000u, NULL);
    int hat_rdtscp = 0;
    if (max_erweitert >= 0x80000001u
        && __get_cpuid(0x80000001u, &eax, &ebx, &ecx, &edx)) {
        hat_rdtscp = (int)((edx >> 27) & 1u);
    }
    printf("      CPUID max extended leaf 0x%08x, leaf 0x80000001 EDX 0x%08x, "
           "RDTSCP bit 27 = %d\n", max_erweitert, edx, hat_rdtscp);
    if (!hat_rdtscp) {
        printf("      the feature bit is ABSENT, so `requires Has(RDTSCP)` holds vacuously\n");
        printf("      and the effect clause was never put to any test. Not runnable here.\n");
        return 77;
    }

    /* ---- The third state: does the instruction execute at all? ---- */
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_NODEFER;
    if (sigaction(SIGSEGV, &sa, NULL) != 0 || sigaction(SIGILL, &sa, NULL) != 0) {
        printf("      no right to handle SIGSEGV/SIGILL -- a trapping RDTSCP could not be\n");
        printf("      told from a working one. Not runnable here.\n");
        return 77;
    }
    gefaultet = 0;
    if (sigsetjmp(sprung, 1) == 0) {
        u64 probe = q_rdtscp();
        (void)probe;
    }
    if (gefaultet) {
        printf("      RDTSCP faults in this process although CPUID declares it -- CR4.TSD\n");
        printf("      is set, or `prctl(PR_SET_TSC, PR_TSC_SIGSEGV)`. Nothing about the\n");
        printf("      clock was measured.\n");
        return 77;
    }

    /* ---- One core, or nothing. A step backwards on a migrating thread says nothing about
     * the instruction and everything about the scheduler. ---- */
    int kern = sched_getcpu();
    cpu_set_t menge;
    CPU_ZERO(&menge);
    if (kern < 0) {
        printf("      the running core cannot be named -- a step backwards could not be\n");
        printf("      told from a migration. Not runnable here.\n");
        return 77;
    }
    CPU_SET(kern, &menge);
    if (sched_setaffinity(0, sizeof menge, &menge) != 0 || sched_getcpu() != kern) {
        printf("      this thread cannot be held on core %d -- a step backwards could not\n",
               kern);
        printf("      be told from a migration between two unsynchronised counters.\n");
        printf("      Not runnable here.\n");
        return 77;
    }

    /* ---- Arms 1, 2 and 4a: the POSITIVE CONTROLS. They run first and must be caught. ---- */
    struct befund frost, rueck;
    pruefe_quelle(q_eingefroren, runden, &frost);
    pruefe_quelle(q_rueckwaerts, runden, &rueck);
    long ausserhalb_gefangen = verschraenkt(q_ausserhalb, runden);

    /* ---- Arms 3 and 4b: the axiom itself. ---- */
    struct befund echt;
    pruefe_quelle(q_rdtscp, runden, &echt);
    long fremde_uhr = verschraenkt(q_rdtscp, runden);
    unsigned aux = letzte_aux;
    int cpu = sched_getcpu();

    /* **The work set beside the verdict (W17).** A green run without a number beside it is
     * indistinguishable from an empty one. */
    printf("      rounds %ld per arm (asked %ld, cap %ld), up to %d reads per round\n",
           runden, gewuenscht, DECKEL, GRENZE);
    printf("      held on core %d; last RDTSCP aux word 0x%08x (low 12 bits %u, "
           "sched_getcpu %d) -- data, not a verdict\n", kern, aux, aux & 0xfffu, cpu);
    printf("      arm 1  FROZEN source, MUST be caught      -- standstill %ld, backwards %ld, "
           "advanced %ld\n", frost.stillstand, frost.rueckwaerts, frost.vorgerueckt);
    printf("      arm 2  BACKWARD source, MUST be caught    -- standstill %ld, backwards %ld, "
           "advanced %ld\n", rueck.stillstand, rueck.rueckwaerts, rueck.vorgerueckt);
    printf("      arm 3  rdtscp advances                    -- standstill %ld, backwards %ld, "
           "advanced %ld (worst wait %ld reads)\n", echt.stillstand, echt.rueckwaerts,
           echt.vorgerueckt, echt.max_lesungen);
    printf("      arm 4a OUTSIDE source in the bracket, MUST be caught -- caught %ld of %ld\n",
           ausserhalb_gefangen, runden);
    printf("      arm 4b rdtscp between two rdtsc reads     -- outside the bracket %ld of "
           "%ld\n", fremde_uhr, runden);

    if (frost.stillstand != runden || rueck.rueckwaerts != runden
        || ausserhalb_gefangen != runden) {
        printf("      BLIND: the frozen source was caught in %ld of %ld rounds, the\n",
               frost.stillstand, runden);
        printf("      backward one in %ld, and the one outside the bracket in %ld. A clock\n",
               rueck.rueckwaerts, ausserhalb_gefangen);
        printf("      that violates the axiom by construction got past this detector, so\n");
        printf("      arms 3 and 4b measured nothing and their green lines are worthless.\n");
        return 1;
    }
    if (echt.stillstand > 0 || echt.rueckwaerts > 0 || fremde_uhr > 0) {
        printf("      REFUTED: rdtscp stood still in %ld round(s), went backwards in %ld,\n",
               echt.stillstand, echt.rueckwaerts);
        printf("      and landed outside the rdtsc bracket in %ld. `effects { reads uhr }`\n",
               fremde_uhr);
        printf("      is not what this instruction does on this machine, and every duty\n");
        printf("      measured against that clock falls with it.\n");
        return 1;
    }
    printf("      not refuted -- and that is ALL it means. The three controls were caught\n");
    printf("      %ld, %ld and %ld times, so the detectors have sensitivity; CPUID declares\n",
           frost.stillstand, rueck.rueckwaerts, ausserhalb_gefangen);
    printf("      the feature and rdtscp advanced inside the rdtsc bracket in all %ld\n",
           echt.vorgerueckt);
    printf("      rounds HERE, on core %d, THIS time. Another core is another measurement.\n",
           kern);
    return 0;
}
#endif
