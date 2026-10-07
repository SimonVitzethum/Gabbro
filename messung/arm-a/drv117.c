#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "117-message-passing-flag.c"
/* writer publishes bericht then flag; reader must see the payload once the flag is up. One-shot per
   round: the flag is reset between rounds under a barrier-free handshake (round counter). */
static _Atomic int rund, fertig;
static int bad;
static void *wr(void *a) { (void)a; melde(4242); return 0; }
int main(void) {
    int viol = 0, seen = 0;
    for (int r = 0; r < 20000; r++) {
        atomic_store(&BEREIT, false); bericht = 0;
        pthread_t t; pthread_create(&t, 0, wr, 0);
        for (int k = 0; k < 2000; k++) {
            uint64_t v = lies();
            if (v) { seen++; if (v != 4242) viol++; break; }
        }
        pthread_join(t, 0);
    }
    printf("seen=%d violations=%d\n", seen, viol);
    return 0;
}
