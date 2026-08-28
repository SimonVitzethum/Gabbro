/* sonde_boot_unerreichbar -- the falsifier for layer S3 of the boot theorem.
 *
 * THE ASSUMPTION, as `manifest.rs::stilllegungsannahmen` books it out of the clause
 * `retires t from boot falsifier sonde_boot_unerreichbar`:
 *
 *   "Nach `boot_ende` ist keine Adresse des Raumes `boot` mehr erreichbar. Dass die
 *    ABBILDUNG verschwindet, ist die Nachbedingung ueber `mappings of` und wird verlangt
 *    (`O012`); dass eine Adresse ohne Abbildung nicht mehr erreichbar ist, ist eine Aussage
 *    ueber MMU und TLB und faellt unter keinen Pass."
 *
 * SPRACHE.md §12 names the probe in one line: *"access to a `.boot` address after
 * `boot_end` must fault."* This program is that line, driven.
 *
 * WHAT IT REALLY MEASURES, AND WHAT IT DOES NOT
 * ---------------------------------------------
 * It measures the second half -- the one that left the checker. A page is mapped, touched
 * from two threads so that BOTH translation buffers hold it, then unmapped; afterwards every
 * access to it must fault, on the unmapping thread and on the other one. That second thread
 * is the whole reason this probe is more than an `munmap` demo: *the dangerous shape is not
 * a stale page table, it is a stale TLB on a core that never asked again.*
 *
 * It does NOT measure misspeculation, and `SPRACHE.md` §12 excepts it in the same words at
 * the layer itself. A transient read behind a mispredicted branch leaves no architectural
 * trace for a signal handler to see; a probe that claimed otherwise would be worse than none.
 *
 * And it measures a HOSTED kernel, not Gabbro's own. The mechanism under test -- a
 * translation removed from the page table, with the shootdown that goes with it -- is the
 * same one `boot_ende` will use, and the assumption is about exactly that mechanism. *What
 * the probe cannot say is that Caprock's own unmapping path performs it correctly; that is
 * `O012`, and it is demanded of the program instead.*
 *
 * THE ARM THAT MAKES THE OTHERS READABLE
 * ---------------------------------------
 * A probe that finds nothing has two possible reasons: nothing was there, or it cannot see.
 * Arm 1 is the positive control and it runs FIRST: the same read, through the same handler,
 * on a page that is still mapped. It must go through. *If it faults, the detector is
 * reacting to its own setup, every later green line is worthless, and the probe ends with 1
 * over itself.*
 *
 * Arm 4 is the execute arm -- a jump into the retired space, which is the case the boot
 * theorem is actually about. It is x86_64 only and it needs a W^X transition the running
 * kernel may refuse; where it cannot run it says so and counts as NOT RUN, never as green.
 *
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here
 */
#define _GNU_SOURCE
#include <pthread.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* **Per thread, and that is not a detail.** Arm 3 faults on the OTHER thread; a single
 * global jump buffer would land that thread in the main thread's stack frame. */
static _Thread_local sigjmp_buf sprung;

static void handler(int sig) {
    (void)sig;
    siglongjmp(sprung, 1);
}

/* 1 = the access faulted, 0 = it went through. */
static int lesen_faultet(volatile unsigned char *p) {
    if (sigsetjmp(sprung, 1) == 0) {
        volatile unsigned char x = *p;
        (void)x;
        return 0;
    }
    return 1;
}

typedef void (*rumpf_t)(void);

static int rufen_faultet(rumpf_t f) {
    if (sigsetjmp(sprung, 1) == 0) {
        f();
        return 0;
    }
    return 1;
}

/* Der zweite Kern: er beruehrt die Seite VOR der Ausblendung -- damit steht sie in seinem
 * Uebersetzungspuffer -- und danach noch einmal. */
struct mit {
    volatile unsigned char *seite;
    pthread_barrier_t vor;
    pthread_barrier_t nach;
    int vorher_faultete;
    int nachher_faultete;
};

static void *gehilfe(void *arg) {
    struct mit *m = (struct mit *)arg;
    m->vorher_faultete = lesen_faultet(m->seite);
    pthread_barrier_wait(&m->vor);   /* die Seite ist beruehrt -- jetzt darf ausgeblendet werden */
    pthread_barrier_wait(&m->nach);  /* ausgeblendet */
    m->nachher_faultete = lesen_faultet(m->seite);
    return NULL;
}

int main(int argc, char **argv) {
    printf("sonde boot_unerreichbar :: nach der Stilllegung ist keine Adresse des Raumes "
           "erreichbar (SPRACHE.md §12, Schicht S3)\n");

    /* **Die Rundenzahl wird GEDECKELT, und die Deckelung steht in der Ausgabe.** Der Laeufer
     * reicht 2 000 000 durch -- das ist die Zahl der Datenrennen-Sonde, und dort kostet eine
     * Runde zwei Speicherzugriffe. Hier kostet sie eine Abbildung, einen Faden und zwei
     * Fehlerbehandlungen. *Eine Sonde, die in die Frist laeuft, meldet 124 und misst nichts.* */
    long gewuenscht = (argc > 1) ? strtol(argv[1], NULL, 10) : 2000;
    if (gewuenscht < 1) {
        gewuenscht = 1;
    }
    const long DECKEL = 2000;
    long runden = (gewuenscht > DECKEL) ? DECKEL : gewuenscht;

    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_NODEFER;
    if (sigaction(SIGSEGV, &sa, NULL) != 0 || sigaction(SIGBUS, &sa, NULL) != 0) {
        printf("      kein Recht, SIGSEGV/SIGBUS zu behandeln -- hier nicht lauffaehig\n");
        return 77;
    }

    long seite_gross = sysconf(_SC_PAGESIZE);
    if (seite_gross <= 0) {
        printf("      keine Seitengroesse zu erfragen -- hier nicht lauffaehig\n");
        return 77;
    }

    long arm1 = 0, arm2 = 0, arm3 = 0, arm4 = 0;
    long blind = 0, durchgelassen = 0, exec_gelaufen = 0;
    int exec_moeglich = 1;

    for (long r = 0; r < runden; r++) {
        unsigned char *seite = mmap(NULL, (size_t)seite_gross, PROT_READ | PROT_WRITE,
                                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (seite == MAP_FAILED) {
            printf("      mmap schlug nach %ld Runden fehl -- hier nicht lauffaehig\n", r);
            return 77;
        }
        seite[0] = 0x5A;

        /* ---- Arm 1: die POSITIVE Kontrolle. Sie laeuft zuerst und muss durchgehen. ---- */
        if (lesen_faultet(seite)) {
            blind++;
            munmap(seite, (size_t)seite_gross);
            break;
        }
        arm1++;

        /* ---- Arm 4a: den Sprung vorbereiten (nur x86_64, und nur wo W^X es zulaesst). ---- */
        rumpf_t rumpf = NULL;
#if defined(__x86_64__)
        if (exec_moeglich) {
            seite[0] = 0xC3; /* ret */
            if (mprotect(seite, (size_t)seite_gross, PROT_READ | PROT_EXEC) != 0) {
                exec_moeglich = 0;
            } else {
                memcpy(&rumpf, &(void *){ (void *)seite }, sizeof rumpf);
                if (rufen_faultet(rumpf)) {
                    /* Ein Ruf in eine ABGEBILDETE, ausfuehrbare Seite muss gehen. Geht er
                     * nicht, sieht dieser Arm etwas anderes als die Abbildung. */
                    blind++;
                    munmap(seite, (size_t)seite_gross);
                    break;
                }
                exec_gelaufen++;
            }
        }
#endif

        /* ---- Der zweite Kern beruehrt die Seite, damit sein TLB sie haelt. ---- */
        struct mit m;
        m.seite = seite;
        m.vorher_faultete = -1;
        m.nachher_faultete = -1;
        if (pthread_barrier_init(&m.vor, NULL, 2) != 0 ||
            pthread_barrier_init(&m.nach, NULL, 2) != 0) {
            munmap(seite, (size_t)seite_gross);
            printf("      keine Barriere zu bekommen -- hier nicht lauffaehig\n");
            return 77;
        }
        pthread_t f;
        if (pthread_create(&f, NULL, gehilfe, &m) != 0) {
            munmap(seite, (size_t)seite_gross);
            printf("      kein Faden zu bekommen -- hier nicht lauffaehig\n");
            return 77;
        }
        pthread_barrier_wait(&m.vor);

        /* ---- Die Stilllegung. ---- */
        if (munmap(seite, (size_t)seite_gross) != 0) {
            pthread_barrier_wait(&m.nach);
            pthread_join(f, NULL);
            printf("      munmap schlug fehl -- hier nicht lauffaehig\n");
            return 77;
        }
        pthread_barrier_wait(&m.nach);

        /* ---- Arm 2: derselbe Kern. ---- */
        if (!lesen_faultet(seite)) {
            durchgelassen++;
            printf("      WIDERLEGT: Lesen von %p ging nach der Ausblendung durch "
                   "(Runde %ld, eigener Kern)\n", (void *)seite, r);
        } else {
            arm2++;
        }

        /* ---- Arm 4b: der SPRUNG in den stillgelegten Raum. ---- */
#if defined(__x86_64__)
        if (rumpf != NULL) {
            if (!rufen_faultet(rumpf)) {
                durchgelassen++;
                printf("      WIDERLEGT: Ruf nach %p lief nach der Ausblendung "
                       "(Runde %ld)\n", (void *)seite, r);
            } else {
                arm4++;
            }
        }
#endif

        /* ---- Arm 3: der ANDERE Kern, dessen TLB die Seite hielt. ---- */
        pthread_join(f, NULL);
        pthread_barrier_destroy(&m.vor);
        pthread_barrier_destroy(&m.nach);
        if (m.vorher_faultete != 0) {
            /* Auch das ist Blindheit: der Gehilfe kam gar nicht erst an die Seite. */
            blind++;
            break;
        }
        if (m.nachher_faultete == 0) {
            durchgelassen++;
            printf("      WIDERLEGT: Lesen von %p ging nach der Ausblendung durch "
                   "(Runde %ld, FREMDER Kern -- stehengebliebener TLB)\n", (void *)seite, r);
        } else {
            arm3++;
        }
    }

    /* **Die Arbeitsmenge neben dem Urteil (W17).** Ein gruener Lauf ohne Zahl ist von einem
     * leeren nicht zu unterscheiden. */
    printf("      Runden %ld (gewuenscht %ld, Deckel %ld)\n", runden, gewuenscht, DECKEL);
    printf("      arm 1  abgebildet, muss GEHEN      -- durchgelassen %ld\n", arm1);
    printf("      arm 2  ausgeblendet, eigener Kern  -- gefaultet     %ld\n", arm2);
    printf("      arm 3  ausgeblendet, FREMDER Kern  -- gefaultet     %ld\n", arm3);
#if defined(__x86_64__)
    if (exec_moeglich) {
        printf("      arm 4  SPRUNG in den Raum          -- gefaultet     %ld  "
               "(vorher gelaufen %ld)\n", arm4, exec_gelaufen);
    } else {
        printf("      arm 4  SPRUNG in den Raum          -- NICHT GEFAHREN: der Kern gibt "
               "keine Seite von schreibbar nach ausfuehrbar\n");
    }
#else
    printf("      arm 4  SPRUNG in den Raum          -- NICHT GEFAHREN: nur x86_64\n");
#endif

    if (blind > 0) {
        printf("      BLIND: die positive Kontrolle fiel %ld-mal. Jede gruene Zeile "
               "darueber ist wertlos -- der Detektor sieht nicht die Abbildung.\n", blind);
        return 1;
    }
    if (durchgelassen > 0) {
        printf("      WIDERLEGT in %ld Faellen. Schicht S3 des Bootsatzes ruht auf dieser "
               "Annahme, und alles, was auf ihr steht, faellt mit.\n", durchgelassen);
        return 1;
    }
    printf("      nicht widerlegt -- und das ist ALLES, was es heisst. Fehlspekulation "
           "sieht diese Sonde nicht, und SPRACHE.md §12 nimmt sie an der Schicht aus.\n");
    return 0;
}
