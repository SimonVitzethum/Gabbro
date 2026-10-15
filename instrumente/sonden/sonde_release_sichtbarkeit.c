/* sonde_release_sichtbarkeit -- a falsifier for `release_stellt_sichtbarkeit_her` (A21).
 *
 * THE ASSUMPTION, as the corpus in `beispiele/` declares it:
 *
 *   "Ein Release-Speichern macht jede vorher geschriebene Nutzlast fuer den Leser sichtbar,
 *    der dieselbe Zelle mit Acquire liest."
 *
 * The whole pairing pass rests on it. `publishes`/`awaits` checks that every expected
 * payload has a publisher and back; that the publication is VISIBLE is not a statement about
 * the program at all, and `saetze.rs` says so at the pairing sentence.
 *
 * WHY THIS PROBE EXISTS EVEN THOUGH THE ASSUMPTION IS BOOKED AS "NOT FALSIFIABLE"
 * ------------------------------------------------------------------------------
 * `messung/AXIOMSCHICHT.md` gives the reason:
 *
 *   "das Speichermodell ist nicht durch Ausfuehrung widerlegbar -- eine erfolgreiche Probe
 *    zeigt nur, dass die Umordnung diesmal ausblieb"
 *
 * That sentence is true and it is an argument about the GREEN direction. Falsifiability is
 * about the RED one. A single observation of a visible flag above a stale payload kills the
 * assumption for good, on this machine, with a printed witness -- and no number of green runs
 * ever supports it. The probe is therefore ASYMMETRIC on purpose, and it says so in its own
 * output rather than letting a green line be read as a result.
 *
 * THE THIRD ARM IS THE ONE THAT MAKES THE OTHER TWO READABLE
 * ----------------------------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * On x86 the second is the likely one -- the hardware model is close to sequentially
 * consistent for this shape, so a green RELEASE arm is expected and worth nothing by itself.
 *
 * Arm 3 therefore inverts the PROGRAM ORDER: the flag is stored BEFORE the payload. A reader
 * that sees the flag can then legitimately see a stale payload on any machine whatsoever --
 * no reordering required. **If arm 3 does not fall, the detector is blind, and this probe
 * exits 1 about ITSELF.** That is the difference between a measurement and a green tick
 * (W17: a green run without demonstrated sensitivity is not a result).
 *
 * THE CONTRACT OF A PROBE IN THIS FOLDER -- see sonden/README.md
 *   exit 0   not falsified in this run   (and that is ALL it means)
 *   exit 1   FALSIFIED, or the probe proved itself blind
 *   exit 77  cannot run here -- no device, no privilege, one core
 *
 * WHAT THIS PROBE IS NOT
 * ----------------------
 * It does not run generated Gabbro code. It probes the MACHINE and the C11 model that the
 * emitter lowers onto, which is what the assumption is about. A probe over emitted code
 * would answer a different question -- whether the emitter puts the release where the
 * pairing pass believes it is -- and that one belongs to the emitter, not here.
 *
 * Build and run: instrumente/pruefe-sonden.sh
 */
#define _GNU_SOURCE
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define NUTZLAST 8

enum arm { ARM_RELEASE = 0, ARM_RELAXED = 1, ARM_INVERTIERT = 2 };

static const char *armname[3] = {
    "release/acquire   -- the assumption under test",
    "relaxed/relaxed   -- the same shape without the ordering",
    "flag BEFORE load  -- positive control, MUST fall",
};

struct lauf {
    /* The payload and the flag are atomics with RELAXED accesses where the arm does not ask
     * for more. Plain variables would be a data race and therefore undefined behaviour --
     * a litmus test written on undefined behaviour measures the optimiser, not the machine. */
    _Atomic unsigned nutzlast[NUTZLAST];
    _Atomic unsigned flagge;
    _Atomic int laeuft;
    unsigned long runden;
    enum arm arm;

    /* filled in by the reader */
    unsigned long beobachtungen;
    unsigned long verletzungen;
    unsigned erste_flagge;
    unsigned erste_nutzlast;
};

static void *schreiber(void *p)
{
    struct lauf *l = p;
    for (unsigned long i = 1; i <= l->runden; i++) {
        unsigned wert = (unsigned)(i & 0x3fffffffu);
        if (wert == 0)
            wert = 1;
        if (l->arm == ARM_INVERTIERT) {
            /* The control: the flag goes up FIRST. Nothing about the machine is being
             * tested here -- the program itself promises a window. */
            atomic_store_explicit(&l->flagge, wert, memory_order_relaxed);
            for (int j = 0; j < NUTZLAST; j++)
                atomic_store_explicit(&l->nutzlast[j], wert, memory_order_relaxed);
        } else {
            for (int j = 0; j < NUTZLAST; j++)
                atomic_store_explicit(&l->nutzlast[j], wert, memory_order_relaxed);
            atomic_store_explicit(&l->flagge, wert,
                                  l->arm == ARM_RELEASE ? memory_order_release
                                                        : memory_order_relaxed);
        }
    }
    atomic_store_explicit(&l->laeuft, 0, memory_order_release);
    return NULL;
}

static void *leser(void *p)
{
    struct lauf *l = p;
    while (atomic_load_explicit(&l->laeuft, memory_order_acquire)) {
        unsigned f = atomic_load_explicit(&l->flagge,
                                          l->arm == ARM_RELEASE ? memory_order_acquire
                                                                : memory_order_relaxed);
        if (f == 0)
            continue;
        l->beobachtungen++;
        for (int j = 0; j < NUTZLAST; j++) {
            unsigned v = atomic_load_explicit(&l->nutzlast[j], memory_order_relaxed);
            /* The payload is monotone: the writer only ever raises it. A payload BELOW the
             * flag the reader has already seen is therefore stale -- the exact shape the
             * assumption denies. */
            if (v < f) {
                if (l->verletzungen == 0) {
                    l->erste_flagge = f;
                    l->erste_nutzlast = v;
                }
                l->verletzungen++;
                break;
            }
        }
    }
    return NULL;
}

static int auf_kern(pthread_attr_t *a, int kern)
{
    cpu_set_t m;
    CPU_ZERO(&m);
    CPU_SET(kern, &m);
    return pthread_attr_setaffinity_np(a, sizeof(m), &m);
}

static void fahre(struct lauf *l, enum arm arm, unsigned long runden, int kerne)
{
    memset(l, 0, sizeof(*l));
    l->arm = arm;
    l->runden = runden;
    atomic_store(&l->laeuft, 1);

    pthread_attr_t as, al;
    pthread_attr_init(&as);
    pthread_attr_init(&al);
    if (kerne >= 2) {
        auf_kern(&as, 0);
        auf_kern(&al, 1);
    }
    pthread_t ts, tl;
    pthread_create(&tl, &al, leser, l);
    pthread_create(&ts, &as, schreiber, l);
    pthread_join(ts, NULL);
    pthread_join(tl, NULL);
    pthread_attr_destroy(&as);
    pthread_attr_destroy(&al);
}

int main(int argc, char **argv)
{
    unsigned long runden = 4000000UL;
    if (argc > 1)
        runden = strtoul(argv[1], NULL, 10);

    long kerne = sysconf(_SC_NPROCESSORS_ONLN);
    printf("sonde sonde_release_sichtbarkeit :: release_stellt_sichtbarkeit_her (A21)\n");
    printf("  cores online: %ld   rounds per arm: %lu   payload words: %d\n", kerne, runden,
           NUTZLAST);

    if (kerne < 2) {
        printf("  NOT RUNNABLE HERE: one core. Two threads on one core never interleave in\n");
        printf("  the window this probe needs -- a green run would measure the scheduler.\n");
        return 77;
    }

    struct lauf l;
    int falsifiziert = 0;
    unsigned long kontroll_verletzungen = 0;

    for (int a = 0; a < 3; a++) {
        fahre(&l, (enum arm)a, runden, (int)kerne);
        printf("  arm %d  %s\n", a + 1, armname[a]);
        printf("         observations %-12lu violations %lu\n", l.beobachtungen,
               l.verletzungen);
        if (l.verletzungen)
            printf("         first witness: flag %u stood above payload %u\n", l.erste_flagge,
                   l.erste_nutzlast);
        if (a == ARM_RELEASE && l.verletzungen)
            falsifiziert = 1;
        if (a == ARM_INVERTIERT)
            kontroll_verletzungen = l.verletzungen;
    }

    printf("\n");
    if (falsifiziert) {
        printf("  FALSIFIED. A release store was seen above a payload written before it.\n");
        printf("  `release_stellt_sichtbarkeit_her` is dead on this machine, and every\n");
        printf("  statement of the pairing pass that rests on it is dead with it.\n");
        return 1;
    }
    if (kontroll_verletzungen == 0) {
        printf("  BLIND. The positive control did not fall: the reader never caught the\n");
        printf("  window even where the writer PROMISED one by raising the flag first.\n");
        printf("  This probe therefore measured nothing about arm 1 -- a green line here\n");
        printf("  would be indistinguishable from an empty run (W17).\n");
        return 1;
    }
    printf("  not falsified in this run -- and that is ALL it means.\n");
    printf("  The control fell %lu times, so the detector has sensitivity; the release arm\n",
           kontroll_verletzungen);
    printf("  did not, so no reordering was observed HERE, THIS TIME, on THIS machine.\n");
    printf("  x86 is close to sequentially consistent for this shape: a green arm 1 is the\n");
    printf("  expected outcome and supports the assumption by nothing at all.\n");
    return 0;
}
