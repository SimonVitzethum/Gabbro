/* **Die Handschrift fuer per-CPU-Akkumulatoren.**
 *
 * So schreibt es ein C-Kern: eine Zelle je Kern, relaxed geladen und gespeichert, die
 * Faltung von Hand. Fuer `min` steht dort `min`, nicht das Komplement.
 *
 * *Gabbro speichert bei `min` das KOMPLEMENT und faltet mit `max`* -- weil C statische
 * Felder nullt und null nicht das Neutrale von `min` ist (`Accumulates_Monoid.thy`,
 * `min_ist_monoid_mit_top`). Diese Messung sagt, was der Kunstgriff kostet.
 */
#include <stdint.h>
#include <stdatomic.h>

#define HKERNE 64u
unsigned gabbro_kern(void);

static _Atomic uint64_t h_hoch[HKERNE];
static _Atomic uint64_t h_tief[HKERNE];
static _Atomic uint32_t h_fehler[HKERNE];

void hand_melde_hoch(uint64_t v) {
    unsigned k = gabbro_kern();
    uint64_t z = atomic_load_explicit(&h_hoch[k], memory_order_relaxed);
    if (v > z) z = v;
    atomic_store_explicit(&h_hoch[k], z, memory_order_relaxed);
}
/* **Der ehrliche Handgriff:** ein Feld, das mit UINT64_MAX vorbelegt ist -- EINMAL, beim
   Anlauf, nicht in der heissen Schleife.

   *Der erste Anlauf stellte den Bereitschaftstest in `hand_melde_tief` selbst und liess
   Gabbro 3,5-mal schneller aussehen. Zum zweiten Mal an einem Tag ein Strohmann -- und
   zum zweiten Mal daran erkannt, dass die eigene Seite zu deutlich gewinnt* (R11). */
void hand_init(void) { for (unsigned i = 0; i < HKERNE; i++) h_tief[i] = UINT64_MAX; }
void hand_melde_tief(uint64_t v) {
    unsigned k = gabbro_kern();
    uint64_t z = atomic_load_explicit(&h_tief[k], memory_order_relaxed);
    if (v < z) z = v;
    atomic_store_explicit(&h_tief[k], z, memory_order_relaxed);
}
void hand_fehler_melden(uint32_t v) {
    unsigned k = gabbro_kern();
    uint32_t z = atomic_load_explicit(&h_fehler[k], memory_order_relaxed);
    atomic_store_explicit(&h_fehler[k], z + v, memory_order_relaxed);
}
uint64_t hand_hoechster(void) {
    uint64_t z = 0;
    for (unsigned i = 0; i < HKERNE; i++) { uint64_t v = atomic_load_explicit(&h_hoch[i], memory_order_relaxed); if (v > z) z = v; }
    return z;
}
uint64_t hand_tiefster(void) {
    uint64_t z = UINT64_MAX;
    for (unsigned i = 0; i < HKERNE; i++) { uint64_t v = atomic_load_explicit(&h_tief[i], memory_order_relaxed); if (v < z) z = v; }
    return z;
}
