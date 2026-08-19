#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <time.h>
static unsigned aktueller_kern = 0;
unsigned gabbro_kern(void) { return aktueller_kern; }
#include "erzeugt-akku.c"
#include "hand-akku.c"
#define RUNDEN 3000000u
static double ms(void){struct timespec x;clock_gettime(CLOCK_MONOTONIC,&x);return x.tv_sec*1e3+x.tv_nsec/1e6;}
int main(void) {
    hand_init();
    for (unsigned r = 0; r < 1000; r++) { aktueller_kern = r % 8; melde_hoch(r); melde_tief(r); hand_melde_hoch(r); hand_melde_tief(r); }
    if (hoechster() != hand_hoechster() || tiefster() != hand_tiefster()) { printf("UNGLEICH\n"); return 1; }
    volatile uint64_t senke = 0;
    for (int w = 0; w < 5; w++) {
        double a0=ms(); for(unsigned r=0;r<RUNDEN;r++){ aktueller_kern = r & 7u; melde_tief(r); } double a1=ms();
        senke += tiefster();
        double b0=ms(); for(unsigned r=0;r<RUNDEN;r++){ aktueller_kern = r & 7u; hand_melde_tief(r); } double b1=ms();
        senke += hand_tiefster();
        printf("  Gabbro %7.1f ms   Hand %7.1f ms   Gabbro/Hand %.3f\n", a1-a0, b1-b0, (a1-a0)/(b1-b0));
    }
    return senke == 0;
}
