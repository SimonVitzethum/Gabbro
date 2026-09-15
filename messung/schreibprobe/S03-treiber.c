/* S03-treiber.c -- `laufzeit/start.c` with the C lock primitives REMOVED.
 *
 * WHY THIS FILE EXISTS. `laufzeit/start.c` does two things: it starts the
 * declared roots on threads, and it DEFINES `L_nimm`/`L_gib` as a POSIX mutex.
 * `S03-sperre-eigene-einheit.gab` supplies the second half from Gabbro -- its
 * emitted C carries `void L_nimm(void)` and `void L_gib(void)` as non-static
 * definitions. Linking both gives `multiple definition of 'L_nimm'`, which is
 * the right error and not a finding. This driver is the same file with the
 * mutex half cut out, so the measurement is "does the GABBRO lock serve the
 * program", not "do two definitions collide".
 *
 * Everything else -- the thread start, the idle root, the checks -- is
 * `laufzeit/start.c` verbatim, because that is the part still written in C and
 * the part the report is about.
 *
 * BUILD (from the tree root):
 *
 *   target/debug/gabbro emit beispiele/124-two-threads-private.gab > K/einheit124.c
 *   target/debug/gabbro emit messung/schreibprobe/S03-sperre-eigene-einheit.gab > K/sperre.c
 *   cc -std=c11 -O0 -Wall -Wextra -Werror -pthread -I K \
 *      -DEINHEIT_INCLUDE='"einheit124.c"' -o K/lauf \
 *      messung/schreibprobe/S03-treiber.c K/sperre.c K/stop.c
 *
 * where `stop.c` defines `_Noreturn void warte_aufgegeben(void) { abort(); }`
 * -- the overrun exit of the ticket lock, declared `extern` in the Gabbro and
 * therefore a named assumption, exactly like `L_nimm` was before this probe.
 */

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include EINHEIT_INCLUDE

/* NO `L_nimm`/`L_gib` HERE -- they come from the emitted Gabbro unit. */

static void *faden_hauptA(void *u) { (void)u; hauptA(); return NULL; }
static void *faden_hauptB(void *u) { (void)u; hauptB(); return NULL; }

#define N_WURZELN 2

/* The idle root, `none` of `E.P.mitRuhe` -- never spawned on hosted POSIX. */
static void *ruhe(void *u) __attribute__((unused));
static void *ruhe(void *u)
{
    (void)u;
    for (;;) {
        pause();
    }
    return NULL;
}

int main(void)
{
    pthread_t faden[N_WURZELN];
    int rc;

    rc = pthread_create(&faden[0], NULL, faden_hauptA, NULL);
    if (rc != 0) { fprintf(stderr, "start: hauptA: %d\n", rc); return 2; }
    rc = pthread_create(&faden[1], NULL, faden_hauptB, NULL);
    if (rc != 0) { fprintf(stderr, "start: hauptB: %d\n", rc); return 2; }
    for (int i = 0; i < N_WURZELN; i++) {
        rc = pthread_join(faden[i], NULL);
        if (rc != 0) { fprintf(stderr, "join: thread %d: %d\n", i, rc); return 2; }
    }

    unsigned konto0 = konto_speicher.slots[0].stand;
    unsigned konto1 = konto_speicher.slots[1].stand;
    unsigned pa0 = privA_speicher.slots[0].stand;
    unsigned pa1 = privA_speicher.slots[1].stand;
    unsigned pb0 = privB_speicher.slots[0].stand;

    printf("konto=%u konto=%u privA=%u privA=%u privB=%u\n",
        konto0, konto1, pa0, pa1, pb0);

    if (konto0 != konto1) {
        fprintf(stderr, "INVARIANT BROKEN: konto[0]=%u konto[1]=%u\n", konto0, konto1);
        return 1;
    }
    if (pa0 != 7 || pa1 != 7) {
        fprintf(stderr, "LOST WRITE: privA=%u,%u, want 7,7\n", pa0, pa1);
        return 1;
    }
    if (pb0 != 5) {
        fprintf(stderr, "LOST WRITE: privB=%u, want 5\n", pb0);
        return 1;
    }
    return 0;
}
