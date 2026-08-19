/* **Die Handschrift, und sie ist die IDIOMATISCHE -- nicht die abgeschriebene.**
 *
 * So liest ein C-Kern einen IPv4-Kopf: ein gepacktes `struct` ueber dem Puffer, Bitfelder
 * fuer die Halbbytes, `ntohs`/`ntohl` fuer die Wortfelder. Genau die Form, die Linux
 * benutzt (`include/uapi/linux/ip.h`).
 *
 * **Sie ist NICHT dasselbe wie das Erzeugnis**, und der Unterschied gehoert in den Bericht:
 * die Bitfeldreihenfolge ist implementierungsdefiniert, das `struct`-Overlay verlangt
 * passende Ausrichtung, und `ntohs` ist POSIX. Gabbros Fassung ist portabel und liest
 * byteweise. *Wer beide gleich schnell misst, hat die Portabilitaet umsonst bekommen.*
 */
#include <stdint.h>
#include <string.h>

struct ipkopf_hand {
#if defined(__LITTLE_ENDIAN__) || (defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    uint8_t  ihl:4, version:4;
    uint8_t  ecn:2, dscp:6;
#else
    uint8_t  version:4, ihl:4;
    uint8_t  dscp:6, ecn:2;
#endif
    uint16_t gesamtlaenge;
    uint16_t kennung;
    uint16_t flags_fragment;
    uint8_t  ttl;
    uint8_t  protokoll;
    uint16_t pruefsumme;
    uint32_t quelle;
    uint32_t ziel;
};

static inline uint16_t be16(uint16_t x) { return (uint16_t)((x >> 8) | (x << 8)); }
static inline uint32_t be32(uint32_t x) {
    return ((x & 0xffu) << 24) | ((x & 0xff00u) << 8) | ((x >> 8) & 0xff00u) | (x >> 24);
}

/* **Das UEBERLAGERN, nicht das Kopieren** -- so macht es Linux (`ip_hdr(skb)`).
 *
 * *Der erste Anlauf kopierte je Kopf mit `memcpy` und war 3,5-mal langsamer als das
 * Erzeugnis. Ein Vergleich, den die eigene Seite so gewinnt, ist kein Vergleich, sondern
 * ein Strohmann* (R11: eine Probe, die beim ersten Versuch durchgeht, ist verdaechtig). */
uint64_t hand_summe(const uint8_t *puffer, uint32_t n, uint32_t schritt) {
    uint64_t s = 0;
    for (uint32_t k = 0; k < n; k++) {
        const struct ipkopf_hand *h =
            (const struct ipkopf_hand *)(const void *)(puffer + (size_t)k * schritt);
        if (h->version != 4u) continue;
        s += h->ttl;
        s += be16(h->gesamtlaenge);
        s += be32(h->quelle) & 0xffu;
        s += (uint64_t)(be16(h->flags_fragment) & 0x1fffu);
        s += h->ihl;
    }
    return s;
}
