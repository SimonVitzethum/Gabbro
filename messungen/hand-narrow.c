/* Die Handschrift: kein Test. Ein C-Programmierer verlaesst sich darauf, dass der Rufer
 * einen gueltigen Index uebergibt -- **und genau dieses Vertrauen ist das, was Gabbro
 * ersetzt.** Der Vergleich misst also nicht dieselbe Zusage, sondern ihren Preis. */
#include <stdint.h>
#define HK 4096u
typedef struct { uint64_t kopf; } h_slot;
typedef struct { h_slot slots[HK]; } HandHalde;
uint64_t hand_lesen(const HandHalde *h, uint32_t i) { return h->slots[i].kopf; }
uint64_t hand_lauf(const HandHalde *h, const uint32_t *ix, uint32_t n) {
    uint64_t s = 0;
    for (uint32_t k = 0; k < n; k++) s += hand_lesen(h, ix[k]);
    return s;
}
