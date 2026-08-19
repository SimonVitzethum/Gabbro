#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "erzeugt-tabelle.c"

typedef struct { bool benutzt; uint32_t zaehler; } hand_slot;
typedef struct { hand_slot slots[4096u]; } HandObjekte;
uint64_t hand_lauf(HandObjekte *o, const uint32_t *ix, uint32_t n);

#define M      4096u
#define RUNDEN 20000u
static uint32_t ix[M];

static uint64_t gabbro_lauf(Objekte *o, const uint32_t *i2, uint32_t n) {
    uint64_t s = 0;
    for (uint32_t k = 0; k < n; k++) { belegen(o, i2[k]); s += stand(o, i2[k]); }
    return s;
}
static double ms(void){struct timespec x;clock_gettime(CLOCK_MONOTONIC,&x);return x.tv_sec*1e3+x.tv_nsec/1e6;}

int main(void) {
    static Objekte g; static HandObjekte h;
    for (uint32_t k = 0; k < M; k++) ix[k] = (uint32_t)((k * 2654435761u) % M);
    for (uint32_t k = 0; k < M; k++) { g.slots[k].zaehler = k; h.slots[k].zaehler = k; }
    if (gabbro_lauf(&g, ix, M) != hand_lauf(&h, ix, M)) { printf("UNGLEICH\n"); return 1; }
    volatile uint64_t senke = 0;
    for (int w = 0; w < 5; w++) {
        double a0=ms(); for(unsigned r=0;r<RUNDEN;r++) senke += gabbro_lauf(&g, ix, M); double a1=ms();
        double b0=ms(); for(unsigned r=0;r<RUNDEN;r++) senke += hand_lauf(&h, ix, M);   double b1=ms();
        printf("  Gabbro %7.1f ms   Hand %7.1f ms   Gabbro/Hand %.3f\n",
               a1-a0, b1-b0, (a1-a0)/(b1-b0));
    }
    return senke == 0;
}
