/* **Die Handschrift fuer den Tabellenzugriff.**
 *
 * Ein Feld fester Laenge, direkte Indizierung, `const` wo gelesen wird. Genau das, was ein
 * C-Programmierer schreibt -- **einschliesslich der fehlenden Schrankenpruefung**, denn
 * die schreibt er auch nicht hin.
 *
 * *Das ist die faire Gegenseite und zugleich die Pointe:* Gabbros Erzeugnis hat hier
 * ebenfalls keine Pruefung -- nicht weil sie wegoptimiert wurde, sondern weil `M103` sie
 * zur Uebersetzungszeit gefuehrt hat. Der Unterschied liegt nicht im Maschinencode,
 * sondern darin, wer den Beweis schuldet.
 */
#include <stdint.h>
#include <stdbool.h>

#define HN 4096u
typedef struct { bool benutzt; uint32_t zaehler; } hand_slot;
typedef struct { hand_slot slots[HN]; } HandObjekte;

uint32_t hand_stand(const HandObjekte *o, uint32_t i) { return o->slots[i].zaehler; }
void hand_belegen(HandObjekte *o, uint32_t i) { o->slots[i].benutzt = true; }

uint64_t hand_lauf(HandObjekte *o, const uint32_t *ix, uint32_t n) {
    uint64_t s = 0;
    for (uint32_t k = 0; k < n; k++) {
        hand_belegen(o, ix[k]);
        s += hand_stand(o, ix[k]);
    }
    return s;
}
