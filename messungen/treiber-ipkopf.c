/* Derselbe Treiber fuer beide Seiten. Die Daten sind identisch, die Runden auch. */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "erzeugt-ipkopf.c"

uint64_t hand_summe(const uint8_t *puffer, uint32_t n, uint32_t schritt);

#define N       20000u
#define SCHRITT 20u
#define RUNDEN  2000u

static uint8_t *puffer;

static void fuellen(void) {
    for (uint32_t k = 0; k < N; k++) {
        uint8_t *p = puffer + (size_t)k * SCHRITT;
        p[0] = 0x45;  p[1] = (uint8_t)(k & 0xff);
        p[2] = 0x05;  p[3] = (uint8_t)(k & 0x3f);
        p[4] = (uint8_t)(k >> 8); p[5] = (uint8_t)k;
        p[6] = 0x40;  p[7] = (uint8_t)(k & 0x1f);
        p[8] = 64;    p[9] = 6;
        p[10] = 0;    p[11] = 0;
        p[12] = 10; p[13] = 0; p[14] = 0; p[15] = (uint8_t)k;
        p[16] = 10; p[17] = 0; p[18] = 1; p[19] = (uint8_t)(k >> 3);
    }
}

/* Dieselbe Rechnung ueber Gabbros Zugriffsfunktionen. */
static uint64_t gabbro_summe(const uint8_t *b, uint32_t n, uint32_t schritt) {
    uint64_t s = 0;
    for (uint32_t k = 0; k < n; k++) {
        IpKopf h = { b + (size_t)k * schritt, SCHRITT };
        if (IpKopf_version(&h) != 4u) continue;
        s += IpKopf_ttl(&h);
        s += IpKopf_gesamtlaenge(&h);
        s += IpKopf_quelle(&h) & 0xffu;
        s += IpKopf_fragment(&h);
        s += IpKopf_ihl(&h);
    }
    return s;
}

static double ms(void) {
    struct timespec x; clock_gettime(CLOCK_MONOTONIC, &x);
    return x.tv_sec * 1e3 + x.tv_nsec / 1e6;
}

int main(void) {
    puffer = malloc((size_t)N * SCHRITT);
    fuellen();
    /* **Erst die GLEICHHEIT, dann die Zeit.** Zwei verschieden schnelle Rechnungen ueber
       verschiedene Ergebnisse zu vergleichen ist keine Messung. */
    uint64_t a = gabbro_summe(puffer, N, SCHRITT), b = hand_summe(puffer, N, SCHRITT);
    if (a != b) { printf("UNGLEICH %llu %llu\n", (unsigned long long)a, (unsigned long long)b); return 1; }
    volatile uint64_t senke = 0;
    for (int w = 0; w < 5; w++) {
        fuellen();
        double g0 = ms(); for (unsigned r = 0; r < RUNDEN; r++) senke += gabbro_summe(puffer, N, SCHRITT); double g1 = ms();
        fuellen();
        double h0 = ms(); for (unsigned r = 0; r < RUNDEN; r++) senke += hand_summe(puffer, N, SCHRITT);   double h1 = ms();
        printf("  Gabbro %7.1f ms   Hand %7.1f ms   Gabbro/Hand %.3f\n",
               g1 - g0, h1 - h0, (g1 - g0) / (h1 - h0));
    }
    return senke == 0;
}
